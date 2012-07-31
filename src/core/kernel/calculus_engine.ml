open Calculus_def
open Calculus_misc
open Calculus_substitution
open Extlist

(*************************************************************)
(*      unification/reduction, type{checking/inference}      *)
(*************************************************************)


(*
  reduction of terms
  several strategy are possible:
  for beta reduction: Lazy or Eager
  possibility to have strong beta reduction
  delta: unfold destructors (replace cste with their destructors)
  iota: try to match destructors l.h.s
  deltaiotaweak: if after delta reduction (on head of app), a iota reduction fails, then the delta reduction is backtracked
  deltaiotaweak_armed: just a flag to tell the reduction function that it should raise a IotaReductionFailed
  zeta: compute the let bindings
  eta: not sure if needed

  all these different strategy are used for several cases: unification, typechecking, ...
  
*)

(* for now only eager is implemented !!!*)
type beta_strategy = 
  | Lazy 
  | Eager

type beta_strength =
  | BetaStrong
  | BetaWeak

type delta_strength =
  | DeltaStrong
  | DeltaWeak

type reduction_strategy = {
  beta: (beta_strategy * beta_strength) option;
  delta: delta_strength option;
  iota: bool;
  zeta: bool;
  eta: bool;
}

(* unification *)
let rec unification (module_: module_) (ctxt: context ref) (te1: term) (te2: term) : term =
  raise (Failure "unification_term_term: NYI")

(* unification *)
and reduction (module_: module_) (ctxt: context ref) (strat: reduction_strategy) (te: term) : term = 
  raise (Failure "reduction: NYI")

and typecheck (module_: module_) (ctxt: context ref) (te: term) : term * term =
  raise (Failure "typecheck: NYI")


