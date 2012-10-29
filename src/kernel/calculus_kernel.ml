include Calculus_def
include Calculus_misc
include Calculus_substitution
include Calculus_engine
include Fm
open Printf

module type KernelTerm =
  sig 
    type t = private term

    val from_ground_term: term -> t
    val to_ground_term: t -> term

    val define_inductive: name -> term -> (name * term) list -> unit
    val define_definition: name -> term -> unit
    val define_recursive: name -> term -> term -> int list -> unit

    val type_of: t -> t
    val reduce: reduction_strategy -> t -> t
      
    val get_defs: unit -> defs

  end;;


module Term : KernelTerm =
  struct
    type t = term ;;
	
    let defs : defs = Hashtbl.create 100 ;;

    let decreasing: (name, int list) Hashtbl.t = Hashtbl.create 100;;    

    let type_simplification_strat = {
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
      
      let te = { te with annot = Typed (reduction_term defs ctxt type_simplification_strat (get_type te))} in
      Hashtbl.replace defs n (Definition te);
      te

    (* *)

    let from_ground_term (te: term) : t =
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
      let te = { te with annot = Typed (reduction_term defs ctxt type_simplification_strat (get_type te))} in
      te;;

    let to_ground_term (te: t) : term = te;;

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

    let reduce strat te = 
      let ctxt = ref empty_context in
      reduction_term defs ctxt strat te

  end;;

include Term;;
