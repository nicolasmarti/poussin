open Calculus_def
open Calculus_misc
open Calculus_substitution
open Calculus_reduction
open Calculus_eq_resolution
open Extlist

let rec typecheck (defs: defs) (context: context) (te: term) (ty: term) : term =
  raise (Failure "typecheck: NYI")

and typeinfer (defs: defs) (context: context) (te: term) : term =
  raise (Failure "typeinfer: NYI")

and unification (defs: defs) (context: context) (te1: term) (te2: term) : term =
  raise (Failure "unification: NYI")
