open Calculus_def
open Calculus_misc
open Calculus_substitution
open Calculus_reduction
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
  ctxt := { !ctxt with conversion_hyps = ((te1, te2)::(List.hd !ctxt.conversion_hyps))::(List.tl !ctxt.conversion_hyps) }

(**)
let context_add_substitution (ctxt: context ref) (s: substitution) : unit =
  (* computes the needed shited substitution *)
  let ss = fst (mapacc (fun acc hd -> (acc, shift_substitution acc (-1))) s !ctxt.fvs) in
  (* for bvs, we do not neet the last one *)
  let ss' = take (List.length ss - 1) ss in
  ctxt := { !ctxt with
    bvs = List.map2 (fun hd1 hd2 -> {hd1 with ty = term_substitution hd2 hd1.ty} ) !ctxt.bvs ss';

    fvs = List.map2 (fun hd1 hd2 -> 
      List.map (fun (i, ty, te, n) -> 
	match te with
	  | None -> (i, term_substitution hd2 ty, None, n)
	  | Some te -> (i, term_substitution hd2 ty, Some (term_substitution hd2 te), n)
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
    conversion_hyps = (List.map (fun (hd1, hd2) -> (shift_term hd1 1, shift_term hd2 1))  (List.hd !ctxt.conversion_hyps))::!ctxt.conversion_hyps
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
  (if List.length !ctxt.bvs = 0 then
    (if List.length fvs != 0 then raise (PoussinException (FreeError "flush_fvars failed because the term still have freevariables")))
  else
      ctxt := { !ctxt with
	fvs = (fvs @ (List.hd !ctxt.fvs))::(List.tl !ctxt.fvs);
	conversion_hyps = List.tl !ctxt.conversion_hyps;
      });
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


let unification_strat = {
  beta = Some BetaWeak;
  delta = Some DeltaStrong;
  iota = true;
  zeta = true;
  eta = true;
}

let context2namelist (ctxt: context ref): name list =
  List.map (fun f -> f.name) !ctxt.bvs

let rec typecheck 
    (defs: defs)
    (ctxt: context ref)
    (te: term)
    (ty: term) : term =
  match get_term_annotation te with
    | Typed ty' ->
      ignore(unification defs ctxt false ty' ty);
      te
    | Annotation ty' ->
      (* TODO *)
      typecheck defs ctxt (set_term_noannotation te) ty
    | NoAnnotation ->
      let te = typeinfer defs ctxt te in
      ignore(unification defs ctxt false (get_type te) ty);
      te


and typeinfer 
    (defs: defs)
    (ctxt: context ref)
    (te: term) : term =
  match get_term_annotation te with
    | Typed ty -> te
    | _ ->
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

	  
	| _ -> raise (Failure (String.concat "" ["typeinfer: NYI for " ; term2string (context2namelist ctxt) te]))
	  
and unification 
    (defs: defs)
    (ctxt: context ref)
    (polarity: bool)
    (te1: term) (te2: term) : term =
  match te1, te2 with

    (* the error cases for AVar and TName *)
    | AVar _, _ -> raise (PoussinException (FreeError "unification_term_term catastrophic: AVar in te1 "))
    | _, AVar _ -> raise (PoussinException (FreeError "unification_term_term catastrophic: AVar in te2 "))
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
      Lambda (q1, te, Typed lty, p1, reduced1 && reduced2)

    | Forall ((s1, ty1, n1, pq1), te1, Typed lty1, p1, reduced1), Forall ((s2, ty2, n2, pq2), te2, Typed lty2, p2, reduced2) ->
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
      Forall (q1, te, Typed lty, p1, reduced1 && reduced2)

    (* TODO: App case *)
    (* some higher order unification *)
    | App (Var (i, _, _), _::args, _, _, _), t2 when i < 0 ->
      raise (Failure "unification: NYI")
    | t1, App (Var (i, _, _), _::args, _, _, _) when i < 0  ->
      raise (Failure "unification: NYI")
    (* the case of two application: with the same arity *)
    | App (hd1, args1, _, _, _), App (hd2, args2, _, _, _) when List.length args1 = List.length args2 ->
      raise (Failure "unification: NYI")

    (* maybe we can reduce the term *)
    | _ when not (is_reduced te1) ->
      unification defs ctxt polarity (reduction_term defs unification_strat te1) te2
    | _ when not (is_reduced te2) ->
      unification defs ctxt polarity te1 (reduction_term defs unification_strat te2)

    (* nothing so far, if the polarity is negative, we add the unification as a converion hypothesis *)
    | _ when not polarity ->
      context_add_conversion ctxt te1 te2;
      te1

    | _ -> raise (PoussinException (UnknownUnification (!ctxt, te1, te2)));
