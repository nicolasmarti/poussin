include Calculus_def
include Calculus_misc
include Calculus_substitution
include Calculus_engine
include Fm
open Printf

module type Kernel =
  sig 

    (* basic term definition *)

    type te = private term

    val from_ground_term: term -> te
    val to_ground_term: te -> term

    val define_inductive: name -> term -> (name * term) list -> unit
    val define_definition: name -> term -> unit
    val define_recursive: name -> term -> term -> int list -> unit

    val type_of: te -> te
    val reduce: ?strat: reduction_strategy -> te -> te
      
    val get_defs: unit -> defs

    (* proof related definition *)

    type formula = private (context * term)

    val formula_from_term: term -> formula
    val formula_context: formula -> context
    val formula_concl: formula -> term      

    type theorem = private (context * term)

    val theorem_context: theorem -> context
    val theorem_concl: theorem -> term      
    val theorem_proof: theorem -> term      


  end;;


module Kernel : Kernel =
  struct
    type te = term ;;
	
    let defs : defs = Hashtbl.create 100 ;;

    let decreasing: (name, int list) Hashtbl.t = Hashtbl.create 100;;    

    let simplification_strat = {
      beta = Some BetaStrong;
      delta = Some DeltaWeak;
      iota = true;
      zeta = true;
      eta = true;
    };;

    (* totality *)
    let totality_check () : unit =
      List.iter (fun ((ctxt, p, te, ret_ty) as case) ->
	raise (PoussinException (MissingMatchCase (
	  case
	)))
      ) !unmatched_pattern ;;

    (* terminaison *)
    let rec term_to_nexpr defs (te: term) : nexpr =
      match te.ast with
	| Cste c when is_irreducible defs te -> Ncons 1
	| App (_, args) when (is_irreducible defs (app_head te)) ->
	  List.fold_right (fun (hd, n) acc ->
	    Nplus (term_to_nexpr defs hd, acc)
	  ) args (Ncons 1)
	| App (f, _) ->
	  term_to_nexpr defs f
	| Var i -> Nvar (String.concat "" ["@"; string_of_int i])

    let terminaison_check n : unit =
      (* first we filter the registered_calls *)
      let lst = List.filter (fun (_, n', _) ->
	match Hashtbl.find defs n' with
	  | Axiom _ when String.compare n n' = 0 -> true
	  | Axiom _ -> 
	    printf "warning: No recursive calls to undefined term yet supported (%s)\n" n'; false
	  (*raise (PoussinException (FreeError "No recursive calls to undefined term yet supported"))*)
	  | _ -> false
      ) !registered_calls in
      (* then we grab the decreasing arguments of decreasing in n *)
      if List.length lst != 0 then (
	let dec = 
	  try 
	    Hashtbl.find decreasing n 
	  with
	    | _ -> 
	      printf "warning: No decreasing arguments\n"; []
	(*raise (PoussinException (FreeError "No decreasing arguments"))*)
	in
	if List.length dec != 0 then (
	  List.iter (fun (ctxt, n, args) ->
	    (* first build hypothesis from conversion hyps *)
	    let hyps = List.fold_right (fun (te1, te2) acc -> 
	      try
		Band (acc, Beq (term_to_nexpr defs te1, term_to_nexpr defs te2)) 
	      with
		| _ -> acc
	    ) ctxt.conversion_hyps BTrue in
	    (* we build the needed condition *)
	    let ccl = Blt (
	      (* the sum of rec. call args *)
	      List.fold_right (fun hd acc -> Nplus (acc, term_to_nexpr defs hd)) (List.map (fun i -> fst (List.nth args i)) dec) (Ncons 0),
	  (* the sum of the vars *)
	      List.fold_right (fun hd acc -> Nplus (acc, Nvar (String.concat "" ["@"; string_of_int hd]))) (List.map (fun i -> List.length ctxt.bvs - i - 1) dec) (Ncons 0)	  
	    ) in
	    (* we also need to assert the positivity of all vars *)
	    let positivity = VarSet.fold (fun hd acc ->
	      Band (acc, Bgt (Nvar hd, Ncons 0))
	    ) (VarSet.union (bexpr_var ccl) (bexpr_var hyps)) BTrue in

	    (* final formula *)
	    let f = bimpl (Band (hyps, positivity)) ccl in
	    if not (fm_dp f) then (
	      raise (PoussinException (NoDecreasingArguments (ctxt, n, args)))
	    )
	  ) lst
	)
      );;

    (* *)

    let process_signature n ty : term =
      (* initialization of a few globals *)
      unmatched_pattern := [];
      registered_calls := [];
      let ctxt = ref empty_context in
      (* typecheck the type *)
      let ty = untype_term ty in
      let ty = (
	try 
	  match Hashtbl.find defs n with
	    | _ -> raise (PoussinException (FreeError (
	      String.concat "" ["term "; n; " is already defined"]
	    )))
	with
	  | Not_found -> typeinfer defs ctxt ty
      ) in
      let ty = typecheck defs ctxt ty (type_ (UName "")) in
      let [ty] = flush_fvars defs ctxt [ty] in 

      (* some extra check *)
      assert (List.length !ctxt.bvs = 0);

      (* well-formness *)
      totality_check ();
      terminaison_check n;

      (* updating the env *)
      Hashtbl.add defs n (Axiom ty);
      ty

    let process_constructor n ty ind : term =
      (* initialization of a few globals *)
      unmatched_pattern := [];
      registered_calls := [];
      let ctxt = ref empty_context in
      (* typecheck the type *)
      let ty = untype_term ty in
      let ty = (
	try 
	  match Hashtbl.find defs n with
	    | Axiom ty' -> 
	      let ty = typecheck defs ctxt ty (type_ (UName "")) in
	      unification defs ctxt ty ty' 
	    | _ -> raise (PoussinException (FreeError (
	      String.concat "" ["term "; n; " is already defined"]
	    )))
	with
	  | Not_found -> typeinfer defs ctxt ty
      ) in
      (* flush free vars *)
      let [ty] = flush_fvars defs ctxt [ty] in 
      
      (* some extra check *)
      assert (List.length !ctxt.bvs = 0);

      (* well-formness *)
      totality_check ();
      terminaison_check n;

      (* ensure that conclusion head is an Inductive *)
      let hd = app_head (snd (destruct_forall ty)) in
      (match hd.ast with
	| Cste n when String.compare n ind = 0 -> ()
	| _ -> raise (PoussinException (FreeError (
	  String.concat "" ["constructor conclusion head is not the Inductive "; ind]
	)))
      );
      
      ty


    let process_inductive n ty cstors: term * (name * term) list =
      (* initialization of a few globals *)
      unmatched_pattern := [];
      registered_calls := [];
      let ctxt = ref empty_context in
      (* typecheck the type *)
      let ty = untype_term ty in
      let ty = (
	try 
	  match Hashtbl.find defs n with
	    | Axiom ty' -> 
	      let ty = typecheck defs ctxt ty (type_ (UName "")) in
	      unification defs ctxt ty ty' 
	    | _ -> raise (PoussinException (FreeError (
	      String.concat "" ["term "; n; " is already defined"]
	    )))
	with
	  | Not_found -> typeinfer defs ctxt ty
      ) in
      let [ty] = flush_fvars defs ctxt [ty] in 

      (* some extra check *)
      assert (List.length !ctxt.bvs = 0);

      (* well-formness *)
      totality_check ();
      terminaison_check n;

      (* updating the env *)
      Hashtbl.add defs n (Inductive ([], ty));

      try
	(* then trying to typecheck all the constructors *)
	let cstors = List.map (fun (n', ty) ->
	  (n', process_constructor n' ty n)
	) cstors in

	(* everything is ok, add the constructor and update the type *)      
	List.iter (fun (n', ty) -> 
	  Hashtbl.add defs n' (Constructor (n, ty))
	) cstors;

	(* update the inductive def in the env *)
	Hashtbl.replace defs n (Inductive (List.map fst cstors, ty));

	ty, cstors

      with
	| err -> 
	  Hashtbl.remove defs n;
	  raise err

    let process_definition n te : term =
      (* initialization of a few globals *)
      unmatched_pattern := [];
      registered_calls := [];
      let ctxt = ref empty_context in
      (* typecheck the term *)
      let te = untype_term te in
      let te = (
	try 
	  match Hashtbl.find defs n with
	    | Axiom ty -> 
	      typecheck defs ctxt te ty		
	    | _ -> raise (PoussinException (FreeError (
	      String.concat "" ["term "; n; " is already defined"]
	    )))
	with
	  | Not_found -> typeinfer defs ctxt te
      ) in
      let [te] = flush_fvars defs ctxt [te] in 

      (* some extra check *)
      assert (List.length !ctxt.bvs = 0);

      (* well-formness *)
      totality_check ();
      terminaison_check n;
      
      let te = { te with annot = Typed (reduction_term defs ctxt simplification_strat (get_type te))} in
      Hashtbl.replace defs n (Definition te);
      te

    (* *)

    let from_ground_term (te: term) : te =
      (* initialization of a few globals *)
      unmatched_pattern := [];
      registered_calls := [];

      (* initialize a new context *)
      let ctxt = ref empty_context in
      (* untype the term *)
      let te = untype_term te in
      (* type inference *)
      let te = typeinfer defs ctxt te in
      let [te] = flush_fvars defs ctxt [te] in 
      
      (* some extra check *)
      assert (List.length !ctxt.bvs = 0);

      (* well-formness *)
      totality_check ();
      let te = { te with annot = Typed (reduction_term defs ctxt simplification_strat (get_type te))} in
      te;;

    let to_ground_term (te: te) : term = te;;

    let define_inductive n ty cstors = ignore (process_inductive n ty cstors);;
    let define_definition n te = ignore (process_definition n te);;
    
    let define_recursive (n: name) (ty: term) (te: term) (dec: int list) =
      try
	ignore(process_signature n ty);
	Hashtbl.replace decreasing n dec;
	ignore (process_definition n te)
      with
	| err ->
	  Hashtbl.remove decreasing n;
	  Hashtbl.remove defs n;
	  raise err
    ;;

    let type_of t = get_type t;;

    let get_defs () = Hashtbl.copy defs;;

    let reduce ?(strat: reduction_strategy = simplification_strat) te = 
      let ctxt = ref empty_context in
      reduction_term defs ctxt strat te

    type formula = (context * term);;

    let formula_context = fst;;
    let formula_concl = snd;;

    let formula_from_term (te: term): formula =
      (* initialization of a few globals *)
      unmatched_pattern := [];
      registered_calls := [];

      (* initialize a new context *)
      let ctxt = ref empty_context in
      (* untype the term *)
      let te = untype_term te in
      (* type checking *)
      let ty = typeinfer defs ctxt (prop_ (UName "")) in
      let te = typecheck defs ctxt te ty in

      (* some extra check *)
      assert (List.length !ctxt.bvs = 0);

      (* well-formness *)
      totality_check ();

      (* then we need to look for the free variables *)

      (* we rewrite the conversion hypothesis in increasing order in the free vars *)
      let s, _ = conversion_hyps2subst ~dec_order:true !ctxt.conversion_hyps in
      let fvs = List.map (fun (i, ty, te, n) ->
	(i,
	 term_substitution s ty,
	 (match te with | None -> None | Some te -> Some (term_substitution s te)),
	 n)
      ) !ctxt.fvs in  
      (* we rewrite all the terms *)
      let te = List.fold_left (fun acc (i, ty, te', n) ->
	match te' with
	  | None -> acc
	  | Some te' -> term_substitution (IndexMap.singleton i te') te
      ) te fvs in
      (* update the context *)
      ctxt := {!ctxt with fvs = fvs};
      (* we compute the fvars of the terms *)
      let lfvs = fv_term te in  
      (* we need to compute an order of free variables: based on their occurences in each other types *)
      let ordered_lfvs = (* not yet done !! *) IndexSet.elements lfvs in      
      (* then we make the processing list *)
      let lst = List.map (fun i -> i, get_fvar ctxt i) ordered_lfvs in
      (* and rebuild the bvs parts of the context with this list *)
      let (bvs, te, _) = fold_cont (fun (bvs, te, names) ((i, (ty, _ (* None *), name))::tl) ->
	let name = (fresh_name_list ~basename:(match name with | None -> "X" | Some n -> n) names) in
	(* we shift and rewrite *)
	let te = term_substitution (IndexMap.singleton i (var_ ~annot:(Typed ty) 0)) (shift_term te 1) in
	(* we rewrite the var i in remaining free vars *)
	let tl, _ = mapacc (fun (ind, ty') (i, (ty, _ (* None *), name)) -> 
	  (i, ((term_substitution (IndexMap.singleton i (var_ ~annot:(Typed ty') ind)) ty), None, name)), 
	  (ind + 1, ty')
	) (0, ty) tl in
	tl, (bvs @ [{name = name; ty = ty; nature = Explicit}], te, names @ [name])
      ) ([], te, []) lst in
      
      let ctxt = { empty_context with bvs = List.rev bvs } in
      let te = { te with annot = Typed (reduction_term defs (ref ctxt) simplification_strat (get_type te))} in
      (ctxt , te);;

    type theorem = (context * term);;

    let theorem_context = fst;;
    let theorem_concl (c, t) = get_type t;;
    let theorem_proof (c, t) = t;;

  end;;

include Kernel;;
