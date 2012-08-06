open Calculus_def
open Calculus_misc
open Calculus_substitution
open Calculus_reduction
open Calculus_eq_resolution
open Extlist

let rec typecheck 
    (defs: defs) 
    (context: context ref) 
    (* a stack of terms *)
    (tes: term ref list)
    (* the term to typecheck *)
    (te: term ref) 
    (* ty is typed *)
    (ty: term ref) 
    : unit =
  match !te with
    | Universe (_, lvl, _) -> (
      unification defs context [te] (ref (Universe (Type, USucc lvl, NoPosition))) ty
    )
    | _ -> 
      match get_term_annotation !te with
	| Typed tety -> (
	  let tety' = ref tety in
	  unification defs context [te] tety' ty;
	  te := set_term_type !te !tety'
	)
	| Annotation tety -> (
	  let tety = ref tety in
	  let tyty = ref (get_type !ty) in
	  typecheck defs context [te;ty] tety tyty;
	  ty := set_term_type !ty !tyty;
	  unification defs context [te] tety ty;
	  te := set_term_noannotation !te;
	  typecheck defs context [ty] te tety
	)	  
	| NoAnnotation -> (
	  typeinfer defs context [ty] te;
	  let tety = ref (get_type !te) in
	  unification defs context [te] tety ty	  
	)

and typeinfer 
    (defs: defs) 
    (context: context ref) 
    (tes: term ref list)
    (te: term ref) : unit =
  raise (Failure "typeinfer: NYI")

and unification 
    (defs: defs) 
    (context: context ref) 
    (tes: (term ref) list)
    (te1: term ref) 
    (te2: term ref) : unit =
  raise (Failure "unification: NYI")
