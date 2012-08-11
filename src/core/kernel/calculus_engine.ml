open Calculus_def
open Calculus_misc
open Calculus_substitution
open Calculus_pprinter
open Extlist
open Libparser
open Printf

(* returns if a definition is irreducible (an inductive or a constructor) *)
let is_irreducible (defs: defs) (n: name) : bool =
  match Hashtbl.find defs n with
    | Inductive _ | Constructor _ | Axiom _ -> true
    | Definition _ -> false

(**)
let context_add_lvl_contraint (ctxt: context ref) (c: uLevel_constraints) : unit =
  ctxt := { !ctxt with lvl_cste = c::!ctxt.lvl_cste }

(**)
let context_add_conversion (ctxt: context ref) (te1: term) (te2: term) : unit =
  (*printf "added conversion: %s == %s\n" (term2string ctxt te1) (term2string ctxt te2);*)
  ctxt := { !ctxt with conversion_hyps = ((te1, te2)::(List.hd !ctxt.conversion_hyps))::(List.tl !ctxt.conversion_hyps) }

(**)
let context_add_substitution (ctxt: context ref) (s: substitution) : unit =
  (*printf "ctxt + %s\n" (substitution2string ctxt s);*)
  (* computes the needed shited substitution *)
  let ss = fst (mapacc (fun acc hd -> (acc, shift_substitution acc (-1))) s !ctxt.fvs) in
  (* for bvs, we do not neet the last one *)
  let ss' = take (List.length ss - 1) ss in
  ctxt := { !ctxt with
    bvs = List.map2 (fun hd1 hd2 -> {hd1 with ty = term_substitution hd2 hd1.ty} ) !ctxt.bvs ss';

    fvs = List.map2 (fun hd1 hd2 -> 
      List.map (fun (i, ty, te, n) -> 
	if IndexMap.mem i hd2 then (
	match te with
	  | None -> (i, term_substitution hd2 ty, Some (IndexMap.find i hd2), n)
	    (* here we should to the unification between both values (maybe not necessary as addition is always on a singleton ...) *)
	  | Some te -> (i, term_substitution hd2 ty, Some (term_substitution hd2 te), n)
	) else (
	match te with
	  | None -> (i, term_substitution hd2 ty, None, n)
	  | Some te -> (i, term_substitution hd2 ty, Some (term_substitution hd2 te), n)
	)
      ) hd1
    ) !ctxt.fvs ss;

    conversion_hyps = List.map2 (fun hd1 hd2 -> 
      List.map (fun (te1, te2) -> 
	(term_substitution hd2 te1, term_substitution hd2 te2)
      ) hd1
    ) !ctxt.conversion_hyps ss;
  }

let push_quantification (q: (name * term * nature * position)) (ctxt: context ref) : unit =
  let s, ty, n, p = q in
  ctxt := { !ctxt with
    bvs = {name = s; ty = shift_term ty 1; nature = n; pos = p}::!ctxt.bvs;
    fvs = []::!ctxt.fvs;
    conversion_hyps = (List.map (fun (hd1, hd2) -> (shift_term hd1 1, shift_term hd2 1)) (List.hd !ctxt.conversion_hyps))::!ctxt.conversion_hyps
  }


(* this function rewrite all free vars that have a real value in the upper frame of a context into a list of terms, and removes them *)
let rec flush_fvars (defs: defs) (ctxt: context ref) (l: term list) : term list =
  (*if !debug then printf "before flush_vars: %s\n" (context2string !ctxt);*)
  (* we compute the fvars of the terms *)
  let lfvs = List.fold_left (fun acc te -> IndexSet.union acc (fv_term te)) IndexSet.empty l in
  (* and traverse the free variables *)
  let (terms, fvs) = fold_cont (fun (terms, fvs) ((i, ty, te, name)::tl) ->
    match te with
      | None when not (IndexSet.mem i lfvs) ->
	(* there is no value for this free variable, and it does not appear in the terms --> remove it *)
	(*printf "removed: %s\n" (string_of_int i);*)
	tl, (terms, fvs)
      | None when IndexSet.mem i lfvs ->
	(* there is no value for this free variable, but it does appear in the terms --> keep it *)
	tl, (terms, fvs @ [i, ty, te, name])
      | Some te -> 
      (* there is a value, we can get rid of the free var *)
	(*if !debug then printf "flush_vars, rewrite %s --> %s\n" (term2string !ctxt (TVar (i, nopos))) (term2string !ctxt te);*)
	let s = (IndexMap.singleton i te) in
	let terms = List.map (fun hd -> term_substitution s hd) terms in
	let tl = List.map (fun (i, ty, te, name) -> i, term_substitution s ty, (match te with | None -> None | Some te -> Some (term_substitution s te)), name) tl in
	tl, (terms, fvs)
  ) (l, []) (List.hd !ctxt.fvs) in
  (* here we are removing the free vars and putting them bellow only if they have no TVar 0 in their term/type *)
  (* first we shift them *)
  let terms, fvs = List.fold_left (fun (terms, acc) (i, ty, te, name) ->
    try 
      terms, (acc @ [i, shift_term ty (-1), 
		     (match te with
		       | None -> None
		       | Some te -> Some (shift_term te (-1))), 
		     name])
    with
      | PoussinException (Unshiftable_term _) ->
	(* we have a free variable that has a type / value containing the symbol in hd -> 
	   we try to ask an oracle if it can guess the term
	*)
	raise (PoussinException (FreeError "we failed to infer a free variable that cannot be out-scoped"))
  ) (terms, []) fvs in
  (* pushing the freevariables on the upper frame *)
  (if List.length !ctxt.bvs != 0 then
      ctxt := { !ctxt with
	fvs = (fvs @ (List.hd !ctxt.fvs))::(List.tl !ctxt.fvs)
      } else 
      List.iter (fun te -> 
	if not (IndexSet.is_empty (fv_term te)) then
	  let msg = String.concat "" ["there are free variables in the remaining term: \n"; term2string ctxt te] in
	  raise (PoussinException (FreeError msg))
  
      ) terms
  );
  terms


let pop_quantification (defs: defs) (ctxt: context ref) (tes: term list) : (name * term * nature * position) * term list =
  (* we flush the free variables *)
  let tes = flush_fvars defs ctxt tes in
  (* we grab the remaining context and the popped frame *)
  let frame = List.hd (!ctxt.bvs) in
  (* we set the context *)
  ctxt := { !ctxt with 
    bvs = List.tl !ctxt.bvs;
    fvs = List.tl !ctxt.fvs;    
    conversion_hyps = List.tl !ctxt.conversion_hyps;    
  };
  (* and returns the quantifier *)
  (frame.name, shift_term frame.ty (-1), frame.nature, frame.pos), tes  

let rec pop_quantifications (defs: defs) (ctxt: context ref) (tes: term list) (n: int) : (name * term * nature * position) list * term list =
  match n with
    | _ when n < 0 -> raise (PoussinException (FreeError "Catastrophic: negative n in pop_quantifications"))
    | 0 -> [], tes
    | _ ->
      let hd, tes = pop_quantification defs ctxt tes in
      let tl, tes = pop_quantifications defs ctxt tes (n-1) in
      hd::tl, tes

let fvar_subst (ctxt: context ref) (i: index) : term option =
  let lookup = fold_stop (fun level frame ->
    let lookup = fold_stop (fun () (index, ty, value, name) -> 
      if index = i then Right value else Left ()
    ) () frame in
    match lookup with
      | Left () -> Left (level + 1)
      | Right res -> Right (match res with | None -> None | Some res -> Some (shift_term res level))
  ) 0 !ctxt.fvs in
  match lookup with
    | Left _ -> raise (PoussinException (UnknownFVar (!ctxt, i)))
    | Right res -> res


(* grab the type of a free var *)
let fvar_type (ctxt: context ref) (i: index) : term =
  let lookup = fold_stop (fun level frame ->
    let lookup = fold_stop (fun () (index, ty, value, name) -> 
      if index = i then Right ty else Left ()
    ) () frame in
    match lookup with
      | Left () -> Left (level + 1)
      | Right res -> Right (shift_term res level)
  ) 0 !ctxt.fvs in
  match lookup with
    | Left _ -> raise (PoussinException (UnknownFVar (!ctxt, i)))
    | Right res -> res

(* grab the type of a bound var *)
let bvar_type (ctxt: context ref) (i: index) : term =
  try (
    let frame = List.nth !ctxt.bvs i in
    let ty = frame.ty in
    shift_term ty i
  ) with
    | Failure "nth" -> raise (PoussinException (UnknownBVar (!ctxt, i)))
    | Invalid_argument "List.nth" -> raise (PoussinException (NegativeIndexBVar i))

(* we add a free variable *)
let rec add_fvar ?(pos: position = NoPosition) ?(name: name option = None) ?(te: term option = None) ?(ty: term option = None) (ctxt: context ref) : term =
  let ty = match ty with
    | None -> add_fvar ~ty:(Some (type_ (UName""))) ctxt
    | Some ty -> ty 
      in
  let next_fvar_index = 
    match (fold_stop (fun acc frame ->
      match frame with
	| [] -> Left acc
	| (i, _, _, _)::_ -> Right (i - 1)
    ) (-1) !ctxt.fvs)
    with
      | Left i -> i
      | Right i -> i
  in
  ctxt := { !ctxt with 
    fvs = ((next_fvar_index, ty, te, name)::(List.hd !ctxt.fvs))::(List.tl !ctxt.fvs)
  };
  Var (next_fvar_index, Typed ty, pos)

(* retrieve the debruijn index of a bound var through its symbol *)
let var_lookup (ctxt: context ref) (n: name) : index option =
  let res = fold_stop (fun level frame ->
    if frame.name = n then Right level else Left (level+1)
  ) 0 !ctxt.bvs in
  match res with
    | Left _ -> (
      let res = fold_stop (fun () frame ->
	fold_stop (fun () (i, _, _, n') ->
	  match n' with
	    | Some n' when n' = n -> Right i
	    | _ -> Left ()
	) () frame
      ) () !ctxt.fvs in
      match res with
	| Left () -> None
	| Right i -> Some i
    )
    | Right level -> Some level

let nature_unify (n1: nature) (n2: nature) : nature option =
  match n1, n2 with
    | NJoker, NJoker | Explicit, Implicit | Implicit, Explicit -> None
    | NJoker, _ -> Some n2
    | _, NJoker -> Some n1
    | Explicit, Explicit -> Some Explicit
    | Implicit, Implicit -> Some Implicit

let rec head (te: term) : term =
  match te with
    | App (hd, _, _, _, _) ->
      head hd
    | _ -> te

let rec pattern_to_term (p: pattern) : term =
  fst (pattern_to_term_loop p (pattern_size p - 1))
and pattern_to_term_loop (p: pattern) (i: int): term * int =
  match p with
    | PAvar -> (avar_ (), i)
    | PName s -> (var_ i, i-1)
    | PCstor (n, args) ->
      let args, i = List.fold_left (fun (hds, i) (p, n) ->
	let p, i = pattern_to_term_loop p i in
	((hds @ [p, n]), i)
      ) ([], i) args in
      (app_ (cste_ n) args, i)


type beta_strength =
  | BetaStrong (* reduction under the quantifier*)
  | BetaWeak

type delta_strength =
  | DeltaStrong (* always unfold *)
  | DeltaWeak (* unfold a term only if the following reduction does not have lambdas or match *)

type reduction_strategy = {
  beta: beta_strength option;
  delta: delta_strength option;
  iota: bool; (* match reduction *)
  zeta: bool; (* let reduction *)
  eta: bool; (* not sure I will implement this one ... *)
}

(* is clean term:
   no lambda, no match, ....
 *)
let rec is_clean_term (te: term) : bool =
  match te with
    | Universe _ | Cste _ | Var _ | AVar _ | TName _ -> true
    | Let _ | Lambda _ | Match _ -> false
    | Forall (_, te, _, _, _) -> is_clean_term te
    | App (f, args, _, _, _) ->
      List.fold_left (fun acc (hd, _) -> acc && is_clean_term hd) (is_clean_term f) args

(* simpl pattern match *)
let rec pattern_match (p: pattern) (te: term) : (term list) option =
  match p with
    | PAvar -> Some []
    | PName s -> Some [te]
    | PCstor (c, args) ->
      match te with
	| Cste (c2, _, _, _) when c = c2 && List.length args = 0 -> Some []
	| App (Cste (c2, _, _, _), args2, _, _, _) when c = c2 && List.length args = List.length args2 ->
	  List.fold_left (fun acc (hd1, hd2) -> 
	    match acc with
	      | None -> None
	      | Some l ->
		match pattern_match hd1 hd2 with
		  | None -> None
		  | Some l' -> Some (l @ l')
	  ) (Some []) (List.map2 (fun hd1 hd2 -> (fst hd1, fst hd2)) args args2)
	| _ -> None
	  

let unification_strat = {
  beta = Some BetaWeak;
  delta = Some DeltaStrong;
  iota = true;
  zeta = true;
  eta = true;
}

let typeinfer_strat = {
  beta = Some BetaWeak;
  delta = Some DeltaStrong;
  iota = true;
  zeta = true;
  eta = true;
}

let simplification_strat = {
  beta = Some BetaWeak;
  delta = Some DeltaWeak;
  iota = false;
  zeta = false;
  eta = false;
}

let rec typecheck 
    (defs: defs)
    (ctxt: context ref)
    (te: term)
    (ty: term) : term =
  if !mk_trace then trace := (TC (!ctxt, te, ty))::!trace;
  let res = 
  match get_term_annotation te with
    | Typed ty' ->
      ignore(unification defs ctxt true ty' ty);
      te
    | Annotation ty' ->
      (*let ty' = typecheck defs ctxt ty' (type_ (UName "")) in*)
      let ty' = typeinfer defs ctxt ty' in
      let te = typeinfer defs ctxt (set_term_tannotation te ty') in
      ignore(unification defs ctxt true (get_type te) ty);
      te 
    | TypedAnnotation ty' ->
      let te = typeinfer defs ctxt te in
      ignore(unification defs ctxt true (get_type te) ty);
      te 
    | NoAnnotation ->
      let te = typeinfer defs ctxt te in
      ignore(unification defs ctxt true (get_type te) ty);
      te
  in
  if !mk_trace then trace := List.tl !trace;
  res


and typeinfer 
    (defs: defs)
    (ctxt: context ref)
    (te: term) : term =
  if !mk_trace then trace := (TI (!ctxt, te))::!trace;
  let res = 
  match get_term_annotation te with
    | Typed ty -> te
    | Annotation ty ->
      (*let ty = typecheck defs ctxt ty (type_ (UName "")) in*)
      let ty = typeinfer defs ctxt ty in
      typeinfer defs ctxt (set_term_tannotation te ty)
    | _ ->
      let te' = (
	match te with
	  | Universe _ -> te
	  | Cste (n, _, pos, reduced) -> (
	    try 
	      match Hashtbl.find defs n with
		| Inductive (_, ty) | Axiom ty | Constructor ty -> 
		  Cste (n, Typed ty, pos, reduced)
		| Definition te -> 
		  Cste (n, Typed (get_type te), pos, reduced)
	    with
	      | Not_found -> raise (PoussinException (UnknownCste n))
	  )

	  | Var (i, _, pos) when i < 0 ->
	    Var (i, Typed (fvar_type ctxt i), pos)
	  | Var (i, _, pos) when i >= 0 ->
	    Var (i, Typed (bvar_type ctxt i), pos)

	  | AVar (_, pos) ->
	    add_fvar ~pos:pos ctxt

	  | TName (n, _, pos) -> (
	    (* we first look for a variable *)
	    match var_lookup ctxt n with
	      | Some i -> 
		Var (i, Typed (bvar_type ctxt i), pos)
	      | None -> 
		typeinfer defs ctxt (Cste (n, NoAnnotation, pos, false))		
	  )

	  | Forall ((s, ty, n, pq), te, _, p, reduced) ->
	    (* first let's be sure that ty :: Type *)
	    let ty = typecheck defs ctxt ty (type_ (UName "")) in
	    (* we push the quantification *)
	    push_quantification (s, ty, n, pq) ctxt;
	    (* we typecheck te :: Type *)
	    let te = typecheck defs ctxt te (type_ (UName "")) in
	    (* we pop quantification *)
	    let q1, [te] = pop_quantification defs ctxt [te] in
	    (* and we returns the term with type Type *)
	    Forall ((s, ty, n, pq), te, Typed (type_ (UName "")), p, reduced)

	  | Lambda ((s, ty, n, pq), te, _, p, reduced) ->
	    (* first let's be sure that ty :: Type *)
	    let ty = typecheck defs ctxt ty (type_ (UName "")) in
	    (* we push the quantification *)
	    push_quantification (s, ty, n, pq) ctxt;
	    (* we typecheck te :: Type *)
	    let te = typeinfer defs ctxt te in
	    (* we pop quantification *)
	    let q1, [te] = pop_quantification defs ctxt [te] in
	    (* and we returns the term with type Type *)
	    let res = Forall ((s, ty, n, pq), get_type te, Typed (type_ (UName "")), NoPosition, reduced) in
	    Lambda ((s, ty, n, pq), te, Typed res, p, reduced)

	  | App (hd, [], _, pos, reduced) ->
	    typeinfer defs ctxt hd 

	  | App (hd, (arg, n)::args, _, pos, reduced) ->	  
	    (* we infer hd and arg *)
	    let hd = typeinfer defs ctxt hd in
	    let arg = typeinfer defs ctxt arg in
	    (* we unify the type of hd with a forall *)
	    let fty = add_fvar ctxt in
	    let hd_ty = unification defs ctxt true (get_type hd) (forall_ ~annot:(Typed (type_ (UName ""))) "@typeinfer_App" ~nature:NJoker ~ty:fty (avar_ ())) in
	    let Forall ((_, _, n', _), _, _, _, _) = hd_ty in
	    (* if n' is Implicit and n is Explicit, it means we need to insert a free variable *)
	    if n' = Implicit && n = Explicit then (
	      let new_arg = add_fvar ctxt in
	      (* and retypeinfer the whole *)
	      typeinfer defs ctxt (App (hd, (new_arg, n')::(arg, n)::args, NoAnnotation, pos, reduced))
	    ) else (
	      (* needs to unify the type properly *)
	      let ty = unification defs ctxt true fty (get_type arg) in
	      let Forall ((q, _, n', pq), te, Typed fty, p, reduced) = hd_ty in
	      (* we build a new head, as the reduction of hd and arg, with the proper type *)
	      let new_hd_ty = (App (Lambda ((q, ty, n, pq), te, Typed fty, p, reduced), (arg,n)::[], Typed fty, pos, false)) in
	      (*printf "Unification, App new_hd_ty:\n%s\n\n" (term2string ctxt new_hd_ty);*)
	      let new_hd_ty = reduction_term defs ctxt simplification_strat new_hd_ty in
	      let new_hd = App (hd, (arg, n)::[], 
				Typed (new_hd_ty), pos,
				false) in
	      (*printf "Unification, App new_hd:\n%s\n\n" (term2string ctxt new_hd);*)
	      let new_hd = reduction_term defs ctxt simplification_strat (
		new_hd
	      ) in 
	      typeinfer defs ctxt (App (new_hd, args, NoAnnotation, pos, reduced))
	    )

	  | Match (te, des, aty, pos, reduced) ->
	    (* first we typecheck the destructed term *)
	    let te = typeinfer defs ctxt te in
	    (* then we assure ourselves that it is an inductive *)
	    let tety = (get_type te) in
	    let _ = 
	      match head (reduction_term defs ctxt typeinfer_strat tety) with
		| Cste (n, _, _, _) -> (
		  try 
		    match Hashtbl.find defs n with
		      | Inductive _ as ty -> ty
		      | _ -> raise (PoussinException (NotInductiveDestruction (!ctxt, te)))
		  with
		    | Not_found -> raise (PoussinException (UnknownCste n))
		)
		| _ -> raise (PoussinException (NotInductiveDestruction (!ctxt, te)))
	    in 
	    (* we create a type for the return value *)
	    let ret_ty = 
	      match aty with
		| TypedAnnotation ty -> ty
		| _ -> add_fvar ctxt
	    in
	    (* then we traverse the destructors *)
	    let des = List.map (fun (ps, des) ->
	      (* first grab the vars of the patterns *)
	      let vars = patterns_vars ps in
	      (* we push quantification corresponding to the pattern vars *)
	      List.iter (fun v -> 
		let ty = add_fvar ctxt in
		push_quantification (v, ty, Explicit (*dummy*), NoPosition) ctxt
	      ) vars;
	      (* we need to shift ret_ty, te, and tety to be at the same level *)
	      let ret_ty = shift_term ret_ty (List.length vars) in
	      let tety = shift_term tety (List.length vars) in
	      let te = shift_term te (List.length vars) in
	      (* then we create the terms corresponding to the patterns *)
	      let tes = List.map (fun p -> pattern_to_term p) ps in
	      (* then, for each patterns, we typecheck against tety *)
	      let tes = List.map (fun te -> 
		let te = typeinfer defs ctxt te in
		let _ = unification defs ctxt false (get_type te) tety in
		te
	      ) tes in
	      (* then, for each pattern *)
	      let des = List.map (fun hd ->
		(* we unify it (with negative polarity) with te *)
		let _ = unification defs ctxt false hd te in
		(* and typecheck des against ret_ty *)
		typecheck defs ctxt des ret_ty
	      ) tes in
	      (* we pop all quantifiers *)
	      let _, des = pop_quantifications defs ctxt des (List.length vars) in
	      (* and finally returns all the constructors *)
	      List.map2 (fun hd1 hd2 -> [hd1], hd2) ps des
	    ) des in
	    let ret_ty = typecheck defs ctxt ret_ty (type_ (UName "")) in
	    Match (te, List.concat des, Typed ret_ty, pos, reduced)
	      
	      
	  | _ -> raise (Failure (String.concat "" ["typeinfer: NYI for " ; term2string ctxt te]))
      ) in (*
	     match get_term_annotation te with
	     | TypedAnnotation ty ->
	     let ty = unification defs ctxt true (get_type te') ty in
	     set_term_type te' ty
	     | _ ->*) te'
  in
  if !mk_trace then trace := List.tl !trace;
  res

and unification 
    (defs: defs)
    (ctxt: context ref)
    (polarity: bool)
    (te1: term) (te2: term) : term =
  if !mk_trace then trace := (U (!ctxt, te1, te2))::!trace;
  let res = 
  (*printf "%s Vs %s\n" (term2string ctxt te1) (term2string ctxt te2);*)
    try (
  match te1, te2 with

    (* AVar is just a wildcard for unification *)
    | AVar _, _ -> te2
    | _, AVar _ -> te1

    (* the error case for AVar *)
    | TName _, _ -> raise (PoussinException (FreeError "unification_term_term catastrophic: TName in te1 "))
    | _, TName _ -> raise (PoussinException (FreeError "unification_term_term catastrophic: TName in te2 "))
     
    (* Prop and Set are imcompatible *)
    | Universe (Set, _, _), Universe (Prop, u2, _) ->
      raise (PoussinException (NoUnification (!ctxt, te1, te2)))
    | Universe (Prop, _, _), Universe (Set, u2, _) ->
      raise (PoussinException (NoUnification (!ctxt, te1, te2)))
    (* equality over universe is pending equality of level *)
    | Universe (t1, u1, pos1), Universe (t2, u2, pos2) when t1 = Set or t2 = Set ->
      context_add_lvl_contraint ctxt (UEq (u1, u2));
      Universe (Set, u1, pos_to_position (best_pos (pos_from_position pos1) (pos_from_position pos2)))

    | Universe (t1, u1, pos1), Universe (t2, u2, pos2) when t1 = Prop or t2 = Prop ->
      context_add_lvl_contraint ctxt (UEq (u1, u2));
      Universe (Prop, u1, pos_to_position (best_pos (pos_from_position pos1) (pos_from_position pos2)))

    | Universe (Type, u1, pos1), Universe (Type, u2, pos2) ->
      context_add_lvl_contraint ctxt (UEq (u1, u2));
      Universe (Prop, u1, pos_to_position (best_pos (pos_from_position pos1) (pos_from_position pos2)))

    (* equality on cste *)
    | Cste (c1, Typed ty1, pos1, reduced1), Cste (c2, Typed ty2, pos2, reduced2) when c1 = c2 ->
      let ty = unification defs ctxt polarity ty1 ty2 in
      Cste (c1, Typed ty, pos_to_position (best_pos (pos_from_position pos1) (pos_from_position pos2)), reduced1 && reduced2)
      

    | Cste (c1, Typed ty1, _, _), Cste (c2, Typed ty2, _, _) when c1 != c2 && is_irreducible defs c1 && is_irreducible defs c2 ->
      raise (PoussinException (NoUnification (!ctxt, te1, te2)))

    (* equality over variables *)
    (* two bounded variables case *)
    | Var (i1, Typed ty1, pos1), Var (i2, Typed ty2, pos2) when i1 = i2 -> 
      let ty = unification defs ctxt polarity ty1 ty2 in
      Var (i1, Typed ty, pos_to_position (best_pos (pos_from_position pos1) (pos_from_position pos2)))

    (* if one of terms is a free variable which which there is a substitution, we redo unification on the term*)
    | Var (i1, Typed ty1, pos1), _ when i1 < 0 && fvar_subst ctxt i1 != None -> 
      unification defs ctxt polarity (match fvar_subst ctxt i1 with Some te1 -> te1) te2

    | _, Var (i2, Typed ty2, pos2) when i2 < 0 && fvar_subst ctxt i2 != None -> 
      unification defs ctxt polarity te1 (match fvar_subst ctxt i2 with Some te2 -> te2)
	
    (* two free variables case *)
    | Var (i1, Typed ty1, pos1), Var (i2, Typed ty2, pos2) when i1 < 0 && i2 < 0 -> 
      let ty = unification defs ctxt polarity ty1 ty2 in
      let imin = min i1 i2 in
      let imax = max i1 i2 in
      let s = IndexMap.singleton imin (Var (imax, Typed ty, pos_to_position (best_pos (pos_from_position pos1) (pos_from_position pos2)))) in
      context_add_substitution ctxt s;
      Var (imax, Typed ty, pos_to_position (best_pos (pos_from_position pos1) (pos_from_position pos2)))
    (* one free variable and one bounded *)
    | Var (i1, Typed ty1, _), _ when i1 < 0 && not (IndexSet.mem i1 (fv_term te2)) -> (
      let ty = unification defs ctxt polarity ty1 (get_type te2) in
      let s = IndexMap.singleton i1 (set_term_type te2 ty) in
      context_add_substitution ctxt s;
      te2
    )
    | Var (i1, Typed ty1, _), _ when i1 < 0 && (IndexSet.mem i1 (fv_term te2)) -> (
      raise (PoussinException (NoUnification (!ctxt, te1, te2)))
    )
    | _, Var (i2, Typed ty2, _) when i2 < 0 && not (IndexSet.mem i2 (fv_term te1)) -> (
      let ty = unification defs ctxt polarity (get_type te1) ty2  in
      let s = IndexMap.singleton i2 (set_term_type te1 ty) in
      context_add_substitution ctxt s;
      te1
    )
    | _, Var (i2, Typed ty2, _) when i2 < 0 && (IndexSet.mem i2 (fv_term te1)) -> (
      raise (PoussinException (NoUnification (!ctxt, te1, te2)))
    )

    (* the Lambda case: only works if both are Lambda *)
    | Lambda ((s1, ty1, n1, pq1), te1, Typed lty1, p1, reduced1), Lambda ((s2, ty2, n2, pq2), te2, Typed lty2, p2, reduced2) ->
      if n1 <> n2 then raise (PoussinException (NoUnification (!ctxt, te1, te2)));
      (* we unify the types *)
      let lty = unification defs ctxt polarity lty1 lty2 in
      let ty = unification defs ctxt polarity ty1 ty2 in
      (* we push the quantification *)
      push_quantification (s1, ty, n1, pq1) ctxt;
      (* we unify the body *)
      let te = unification defs ctxt polarity te1 te2 in
      (* we pop quantification (possibly modifying te) *)
      let q1, [te] = pop_quantification defs ctxt [te] in
      (* and we return the term *)
      Lambda (q1, te, Typed lty, p1, false)

    | Forall ((s1, ty1, n1, pq1), fte1, Typed lty1, p1, reduced1), Forall ((s2, ty2, n2, pq2), fte2, Typed lty2, p2, reduced2) ->
      let n = nature_unify n1 n2 in
      if n = None then raise (PoussinException (NoUnification (!ctxt, te1, te2)));
      let Some n = n in
      (* we unify the types *)
      let lty = unification defs ctxt polarity lty1 lty2 in
      let ty = unification defs ctxt polarity ty1 ty2 in
      (* we push the quantification *)
      push_quantification (s1, ty, n1, pq1) ctxt;
      (* we unify the body *)
      let te = unification defs ctxt polarity fte1 fte2 in
      (* we pop quantification (possibly modifying te) *)
      let (s, ty, _, pq), [te] = pop_quantification defs ctxt [te] in
      (* and we return the term *)
      Forall ((s, ty, n, pq), te, Typed lty, p1, false)

    | Let ((s1, ty1, pq1), te1, Typed lty1, p1, reduced1), Let ((s2, ty2, pq2), te2, Typed lty2, p2, reduced2) ->
      (* we unify the types *)
      let lty = unification defs ctxt polarity lty1 lty2 in
      let ty = unification defs ctxt polarity ty1 ty2 in
      (* we push the quantification *)
      push_quantification (s1, ty, Explicit, pq1) ctxt;
      (* we unify the body *)
      let te = unification defs ctxt polarity te1 te2 in
      (* we pop quantification (possibly modifying te) *)
      let (s, ty, _, pq), [te] = pop_quantification defs ctxt [te] in
      (* and we return the term *)
      Let ((s, ty, pq), te, Typed lty, p1, false)

	(*
    (* TODO: App case *)
    (* some higher order unification *)
    | App (Var (i, _, _), _::args, _, _, true), t2 when i < 0 ->
      raise (Failure "unification: NYI")
    | t1, App (Var (i, _, _), _::args, _, _, true) when i < 0  ->
      raise (Failure "unification: NYI")
	*)

    (* Normalizing App *)
    | App (App(hd1, args1, Typed ty1, pos1, _), args2, Typed ty2, pos2, _), _ -> 
      unification defs ctxt polarity (App(hd1, args1 @ args2, Typed ty2, pos2, false)) te2

    |  _, App(App(hd1, args1, Typed ty1, pos1, _), args2, Typed ty2, pos2, _) -> 
      unification defs ctxt polarity te1 (App(hd1, args1 @ args2, Typed ty2, pos2, false))

    (* this is really conservatives ... *)
    | Match (t1, des1, Typed ty1, pos1, _), Match (t2, des2, Typed ty2, pos2, _) when List.length des1 = List.length des2 ->
      (* unify the destructed term and the returned type *)
      let t = unification defs ctxt polarity t1 t2 in
      let ty = unification defs ctxt polarity ty1 ty2 in
      (* then proceeds with the destructor *)
      let des = List.map2 (fun (ps1, t1) (ps2, t2) ->
	if ps1 <> ps2 then raise (PoussinException (UnknownUnification (!ctxt, te1, te2)));
	(* first grab the vars of the patterns *)
	let vars = patterns_vars ps1 in	      
	(* we push quantification corresponding to the pattern vars *)
	List.iter (fun v -> 
	  let ty = add_fvar ctxt in
	  push_quantification (v, ty, Explicit (*dummy*), NoPosition) ctxt
	) vars;
	let t = unification defs ctxt polarity t1 t2 in
	let _, [t] = pop_quantifications defs ctxt [t] (List.length vars) in
	ps1, t	  
      ) des1 des2 in
      Match (t, des, Typed ty, pos1, false)      

    (* the case of two application: with the same arity *)
    | App (hd1, args1, Typed ty1, pos1, _), App (hd2, args2, Typed ty2, pos2, _) when List.length args1 = List.length args2 ->
      let ty = unification defs ctxt polarity ty1 ty2 in
      let hd = unification defs ctxt polarity hd1 hd2 in
      let args = List.map (fun (n, hd1, hd2) -> unification defs ctxt polarity hd1 hd2, n) 
	(List.map2 (fun (hd1, n1) (hd2, n2) -> 
	  if n1 <> n2 then 
	    raise (PoussinException (NoNatureUnification (!ctxt, hd1, hd2)))
	  else
	    n1, hd1, hd2
	 ) args1 args2) in
      App (hd, args, Typed ty, pos1, false)

    (* maybe we can reduce the term *)
    | _ when not (is_reduced te1) ->
      unification defs ctxt polarity (set_term_reduced (reduction_term defs ctxt unification_strat te1)) te2
    | _ when not (is_reduced te2) ->
      unification defs ctxt polarity te1 (set_term_reduced (reduction_term defs ctxt unification_strat te2))
    (* nothing so far, if the polarity is negative, we add the unification as a converion hypothesis *)
    | _ when not polarity ->
      context_add_conversion ctxt te1 te2;
      te1

    (* we try a simple use of conversions *)
	
    | _ ->
	let s, l = conversion_hyps2subst (List.hd !ctxt.conversion_hyps) in
	(*printf "s := %s\n" (substitution2string ctxt s);*)
	if not (IndexMap.is_empty s) && polarity then (
	  if !mk_trace then trace := (Free (substitution2string ctxt s)):: !trace;
	  let te1' = term_substitution s te1 in
	  let te2' = term_substitution s te2 in
	  (*printf "(%s, %s) --> (%s, %s)\n" (term2string ctxt te1) (term2string ctxt te2) (term2string ctxt te1') (term2string ctxt te2');*)
	  try 
	    let res = unification defs (ref {!ctxt with conversion_hyps = l::[] }) polarity te1' te2' in
	    if !mk_trace then trace := List.tl !trace;
	    res
	  with
	    | _ -> 
	      if are_convertible defs (ref {!ctxt with conversion_hyps = l::[] }) te1 te2 or are_convertible defs (ref {!ctxt with conversion_hyps = l::[] }) te2 te1 then te1 else
		raise (PoussinException (UnknownUnification (!ctxt, te1, te2)));
	) else
	  raise (PoussinException (UnknownUnification (!ctxt, te1, te2)));
    ) with
      | (PoussinException (UnknownUnification (ctxt', te1', te2'))) when not (is_reduced te1) or not (is_reduced te2) ->
	let te1 = if not (is_reduced te1) then set_term_reduced (reduction_term defs ctxt unification_strat te1) else te1 in
	let te2 = if not (is_reduced te2) then set_term_reduced (reduction_term defs ctxt unification_strat te2) else te2 in
	unification defs ctxt polarity te1 te2
  in
  if !mk_trace then trace := List.tl !trace;
  res

(* these stuffs are quite ... *)
and are_convertible 
    (defs: defs)
    (ctxt: context ref)
    (te1: term) (te2: term) : bool =
  match 
    fold_stop (fun () (hd1, hd2) ->
      (*printf "(%s, %s) <--> (%s, %s)\n" (term2string ctxt te1) (term2string ctxt te2) (term2string ctxt hd1) (term2string ctxt hd2);*)
      try 
	if !mk_trace then trace := (Free (String.concat "" ["try conversion: "; (term2string ctxt hd1); " <-> "; (term2string ctxt hd2)])):: !trace;
	let ctxt' = ref {!ctxt with conversion_hyps =  (List.tl (List.hd !ctxt.conversion_hyps)) :: [] } in
	let _ = unification defs ctxt' true (get_type te1) (get_type hd1) in
	let _ = unification defs ctxt' true te1 hd1 in
	let _ = unification defs ctxt' true te2 hd2 in
	ctxt := { !ctxt' with conversion_hyps = !ctxt.conversion_hyps };
	if !mk_trace then trace := List.tl !trace;
	Right ()
      with
	| _ -> 	if !mk_trace then trace := List.tl !trace; Left ()
    ) () (List.hd !ctxt.conversion_hyps) with
      | Left () -> false
      | Right () -> true

(* transform a conversion_hyps list into a substitution *)
and conversion_hyps2subst (cv: (term * term) list) : (substitution * (term * term) list) =
  match cv with
    | [] -> IndexMap.empty,  []
    | (Var (i, _, _), te2)::tl when i >= 0 && IndexSet.is_empty (IndexSet.filter (fun i' -> i < i') (bv_term te2)) ->
      let s, l = conversion_hyps2subst tl in
      IndexMap.add i te2 s, l 
    | (te1, Var (i, _, _))::tl when i >= 0  && IndexSet.is_empty (IndexSet.filter (fun i' -> i < i') (bv_term te1)) ->
      let s, l = conversion_hyps2subst tl in
      IndexMap.add i te1 s, l 
    | hd::tl -> 
      let s, l = conversion_hyps2subst tl in
      s, hd::tl


(* reduction *)
(* NB: in order to enhanced reduction, it might be proper have a marker on terms 
   stating the term is reduced
*)


and reduction_term (defs: defs) (ctxt: context ref) (strat: reduction_strategy) (te: term) : term = 
  if !debug_reduction then   printf "reduction: ";
  let te' = reduction_term_loop defs ctxt strat (unset_term_reduced ~r:true te) in
  if !debug_reduction then   printf "\n";
  (unset_term_reduced ~r:true te')
and reduction_term_loop (defs: defs) (ctxt: context ref) (strat: reduction_strategy) (te: term) : term = 
  if !debug_reduction then   printf "{ %s }" (term2string ctxt te);
  if !mk_trace then trace := (Reduction (!ctxt, te)) :: !trace;
  let te' = (
    match te with
      | Universe _ | AVar _ | TName _ -> te

      | _ when is_reduced te -> te

      | Cste (n, ty, position, _) -> (
	try 
	  match Hashtbl.find defs n with
		(* delta strong -> we return it 
		   delta_weak -> we make sure the resulting term is 'clean'
		*)
	    | Definition te -> (
	      match strat.delta with
		| Some _ -> 
		  let te' = reduction_term_loop defs ctxt strat te in
		  te'
		| None -> set_term_reduced te
	    )
	    | _ -> set_term_reduced te
	with
	  | Not_found -> raise (PoussinException (UnknownCste n))
	    
      )

      | Lambda ((n, ty, nature, pos), te, ty2, pos2, _) when strat.beta = Some BetaStrong ->
	(
	  let te = reduction_term_loop defs ctxt strat te in
	  Lambda ((n, ty, nature, pos), te, ty2, pos2, true)
	)

      | Forall ((n, ty, nature, pos), te, ty2, pos2, _) when strat.beta = Some BetaStrong ->
	(
	  let te = reduction_term_loop defs ctxt strat te in
	  Forall ((n, ty, nature, pos), te, ty2, pos2, true)
	)

      | Let _ when strat.zeta = false && strat.beta != Some BetaStrong -> set_term_reduced te
      | Let ((n, te, pos), te2, ty, pos2, _) when strat.zeta = false && strat.beta = Some BetaStrong ->
	Let ((n, te, pos), reduction_term_loop defs ctxt strat te2, ty, pos2, true)

      | Let ((n, te, pos), te2, ty, pos2, _) when strat.zeta = true ->
      (* here we compute the reduction of te and shift it such that it is at the same level as te2 *)
	let te = shift_term (reduction_term_loop defs ctxt strat te) 1 in
      (* we substitute all occurence of n by te *)
	let te2 = term_substitution (IndexMap.singleton 0 te) te2 in
      (* and we shift back to the proper level *)
	let te2 = shift_term te2 (-1) in
	reduction_term_loop defs ctxt strat te2

      | Match _ when strat.iota = false -> set_term_reduced te
      | Match (dte, des, ty, pos, _) -> (
	let dte = reduction_term_loop defs ctxt strat dte in
	let res = fold_stop (fun () (ps, body) ->
	  fold_stop (fun () p ->
	    match pattern_match p dte with
	      | None -> Left ()
	      | Some l ->
	      (* we will do the same thing as in let, but on the reversed order of the matching list *)
		let te = List.fold_left (fun acc te -> 
		(* rewrite the var 0 *)
		  let acc = term_substitution (IndexMap.singleton 0 te) acc in
		(* shift the term by -1 *)
		  let acc = shift_term acc (-1) in
		  acc
		) 
		  body 
		  (List.map (fun te -> shift_term te (List.length l)) (List.rev l)) in
		Right te
	  ) () ps
	) () des in
	match res with
	  | Left () -> set_term_reduced te
	  | Right te -> reduction_term_loop defs ctxt strat te
      )

      | App (Lambda ((n, ty, nature, pos), te, ty2, pos2, _), (hd1, hd2)::tl, app_ty, app_pos, _) when strat.beta != None ->
	let hd1 = shift_term (reduction_term_loop defs ctxt strat hd1) 1 in
	let f = unset_term_reduced ~r:true (term_substitution (IndexMap.singleton 0 hd1) te) in
	reduction_term_loop defs ctxt strat (App (shift_term f (-1), tl, app_ty, app_pos, false))

      | App (f, [], _, _, _) ->
	set_term_reduced (reduction_term_loop defs ctxt strat f)

      | App (f, args, ty, pos, _) when not (is_reduced f) -> (
	let f = reduction_term_loop defs ctxt { strat with delta = match strat.delta with | Some DeltaWeak -> Some DeltaStrong | _ -> strat.delta } f in
	set_term_reduced (reduction_term_loop defs ctxt strat (App (f, args, ty, pos, false)))
      )

      | App (f, args, ty, pos, _) when is_reduced f ->
	let args = List.map (fun (te, n) -> reduction_term_loop defs ctxt strat te, n) args in
	App (f, args, ty, pos, true)

      (* using conversion (adhoc) *)
      | _ -> 
	(* create the substitution *)
	let s, l = conversion_hyps2subst (List.hd !ctxt.conversion_hyps) in
	(*  if its not empty and the bv_term + fv_term has an intersection with the domain of the substitution -> apply *)
	if not (IndexMap.is_empty s) then (
	  (*
	  printf "reduction of %s\n" (term2string ctxt te);
	  printf "rewriting s for reduction := %s\n" (substitution2string ctxt s);
	  *)
	  let vars = IndexSet.union (bv_term te) (fv_term te) in
	  let intersect = 
	    match fold_stop (fun () i -> 
	      if IndexMap.mem i s then Right () else Left ()
	    ) () (IndexSet.elements vars) with 
	      | Left () -> false
	      | Right () -> true
	  in
	  if intersect then
	    let te = term_substitution s te in
	    te
	  else
	    te
	) else te	  

  ) in
  let te' = 
    match strat.delta with
      | Some DeltaWeak when is_clean_term te' -> te'
      | Some DeltaStrong -> set_term_reduced te'
      | _ -> set_term_reduced te      
  in
  if !debug_reduction then printf "{ %s }" (term2string ctxt te');
  if !mk_trace then trace := List.tl !trace;
  te'

and reduction_typeannotation (defs: defs) (ctxt: context ref) (strat: reduction_strategy) (ty: typeannotation) : typeannotation =
  match ty with
    | NoAnnotation -> NoAnnotation
    | Annotation te -> Annotation (reduction_term_loop defs ctxt strat te)
    | Typed te -> Typed (reduction_term_loop defs ctxt strat te)
