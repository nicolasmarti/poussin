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

(* all the terms should be typed *)
let rec eq_resolution (defs: defs) (hyps: (bool * term * term) list) (goal: (term * term)) : (substitution * uLevel_constraints list * (term * term) list) option =
  let te1, te2 = goal in
  match goal with

    (* the error cases for AVar and TName *)
    | AVar _, _ -> raise (DoudouException (FreeError "unification_term_term catastrophic: AVar in te1 "))
    | _, AVar _ -> raise (DoudouException (FreeError "unification_term_term catastrophic: AVar in te2 "))
    | TName _, _ -> raise (DoudouException (FreeError "unification_term_term catastrophic: TName in te1 "))
    | _, TName _ -> raise (DoudouException (FreeError "unification_term_term catastrophic: TName in te2 "))
     
    (* Prop and Set are imcompatible *)
    | Universe (Set, _, _), Universe (Prop, u2, _) ->
      None
    | Universe (Prop, _, _), Universe (Set, u2, _) ->
      None
    (* equality over universe is pending equality of level *)
    | Universe (_, u1, _), Universe (_, u2, _) ->
      Some (IndexMap.empty, [UEq (u1, u2)], [])

    (* equality on cste *)
    | Cste (c1, Typed ty1, _, _), Cste (c2, Typed ty2, _, _) when c1 = c2 ->
      Some (IndexMap.empty, [], [(ty1, ty2)])

    | Cste (c1, Typed ty1, _, _), Cste (c2, Typed ty2, _, _) when c1 != c2 && is_irreducible defs c1 && is_irreducible defs c2 ->
      None

    (* equality over variables *)
    (* two bounded variables case *)
    | Var (i1, Typed ty1, _), Var (i2, Typed ty2, _) when i1 = i2 -> 
      Some (IndexMap.empty, [], [(ty1, ty2)])    
    (* two free variables case *)
    | Var (i1, Typed ty1, pos1), Var (i2, Typed ty2, pos2) when i1 < 0 && i2 < 0 -> 
      let imin = min i1 i2 in
      let imax = max i1 i2 in
      let s = IndexMap.singleton imin (Var (imax, Typed ty1, pos_to_position (best_pos (pos_from_position pos1) (pos_from_position pos2)))) in
	Some (s, [], [(ty1, ty2)])
    (* one free variable and one bounded *)
    | Var (i1, Typed ty1, _), _ when i1 < 0 && not (IndexSet.mem i1 (fv_term te2)) -> (
      let s = IndexMap.singleton i1 te2 in
      Some (s, [], [(ty1, get_type te2)])
    )
    | Var (i1, Typed ty1, _), _ when i1 < 0 && (IndexSet.mem i1 (fv_term te2)) -> (
      None
    )
    | _, Var (i2, Typed ty2, _) when i2 < 0 && not (IndexSet.mem i2 (fv_term te1)) -> (
      let s = IndexMap.singleton i2 te1 in
      Some (s, [], [(ty2, get_type te1)])
    )
    | _, Var (i2, Typed ty2, _) when i2 < 0 && (IndexSet.mem i2 (fv_term te1)) -> (
      None
    )



    (* *)
    | _ -> raise (Failure "eq_resolution: NYI")
