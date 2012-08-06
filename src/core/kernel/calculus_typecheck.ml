open Calculus_def
open Calculus_misc
open Calculus_substitution
open Calculus_reduction
open Extlist
open Libparser

(* returns if a definition is irreducible (an inductive or a constructor) *)
let is_irreducible (defs: defs) (n: name) : bool =
  match Hashtbl.find defs n with
    | Inductive _ | Constructor _ | Axiom _ -> true
    | Definition _ -> false

(**)
let context_add_lvl_contraint (ctxt: context ref) (c: uLevel_constraints) : unit =
  raise (Failure "context_add_lvl_contraint: NYI")

let context_add_substitution (ctxt: context ref) (s: substitution) : unit =
  raise (Failure "context_add_substitution: NYI")

let rec typecheck 
    (defs: defs)
    (ctxt: context ref)
    (te: term)
    (ty: term) : term =
  raise (Failure "")

and typeinfer 
    (defs: defs)
    (ctxt: context ref)
    (te: term) : term =
  raise (Failure "")

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
	
    | _ -> raise (Failure "")
