open Calculus_def
open Calculus_misc
open Calculus_substitution
open Extlist

(* for now only eager is implemented !!!*)
type beta_strategy = 
  | Lazy 
  | Eager

type beta_strength =
  | BetaStrong (* reduction under the quantifier*)
  | BetaWeak

type delta_strength =
  | DeltaStrong (* always unfold *)
  | DeltaWeak (* unfold a term only if the following reduction does not have lambdas or match *)

type reduction_strategy = {
  beta: (beta_strategy * beta_strength) option;
  delta: delta_strength option;
  iota: bool; (* match reduction *)
  zeta: bool; (* let reduction *)
  eta: bool; (* not sure I will implement this one ... *)
}

(* reduction *)
let rec reduction (defs: defs) (context: context) (strat: reduction_strategy) (te: term) : term = 
  raise (Failure "reduction: NYI")
