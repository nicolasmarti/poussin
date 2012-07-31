open Calculus_def
open Calculus_misc

(*************************************)
(*      substitution/rewriting       *)
(*************************************)

(* substitution = replace variables (free or bound) by terms (used for typechecking/inference with free variables, and for reduction with bound variable) *)

(* substitution: from free variables to term *) 
type substitution = term IndexMap.t;;

(* shift a set of variable *)
let shift_vars (vars: IndexSet.t) (delta: int) : IndexSet.t =
  IndexSet.fold (fun e acc ->
    if (e >= 0 && e + delta < 0) || e < 0 then acc
    else IndexSet.add (e + delta) acc      
  ) vars IndexSet.empty

(* shifting of terms *)
let rec shift_term (te: term) (delta: int) : term =
  leveled_shift_term te 0 delta

(* shift bvar index in a term, above a given index *)
and leveled_shift_term (te: term) (level: int) (delta: int) : term =
  raise (Failure "leveled_shift_term: NYI")

(* shift substitution *)
let rec shift_substitution (s: substitution) (delta: int) : substitution =
  raise (Failure "shift_substitution: NYI")
    
