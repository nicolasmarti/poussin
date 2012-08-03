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

(* is clean term *)
let rec is_clean_term (te: term) : bool =
    raise (Failure "is_clean_term: NYI")

(* reduction *)
(* NB: in order to enhanced reduction, it might be proper have a marker on terms 
   stating the term is reduced
*)

let rec reduction_term (defs: defs) (context: context) (strat: reduction_strategy) (te: term) : term = 
  match te with
    | Universe _ | Var _ | AVar _ | TName _ -> te

    | Cste (n, ty, position) -> (
      match strat.delta with
	(* no unfolding *)
	| None -> te

	| Some delta -> (
	  try 
	    match Hashtbl.find defs n with
	      (* delta strong -> we return it 
		 delta_weak -> we make sure the resulting term is 'clean'
	      *)
	      | Definition te ->
		let te' = reduction_term defs context strat te in
		match delta with
		  | DeltaStrong -> te'
		  | DeltaWeak when is_clean_term te' -> te'
		  | _ -> te
	  with
	    | Not_found -> raise (DoudouException (UnknownCste n))
	      
	)
	  
    )

    |_ -> raise (Failure "reduction: NYI")
