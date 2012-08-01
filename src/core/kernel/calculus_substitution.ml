open Calculus_def
open Calculus_misc

(*************************************)
(*      substitution/rewriting       *)
(*************************************)

(* substitution = replace variables (free or bound) by terms (used for typechecking/inference with free variables, and for reduction with bound variable) *)

(* substitution: from free variables to term *) 
type substitution = term IndexMap.t;;

(* shifting of terms *)
let rec shift_term (te: term) (delta: int) : term =
  leveled_shift_term te 0 delta

(* shift bvar index in a term, above a given index *)
and leveled_shift_term (te: term) (level: int) (delta: int) : term =
  raise (Failure "leveled_shift_term: NYI")

(* shift substitution *)
let rec shift_substitution (s: substitution) (delta: int) : substitution =
  raise (Failure "shift_substitution: NYI")

(* substitution *)
let rec term_substitution (s: substitution) (te: term) : term =
  raise (Failure "term_substitution: NYI")

(* apply a substitution in a context *)
let context_substitution (s: substitution) (ctxt: context) : context =
  raise (Failure "context_substitution: NYI")



    
