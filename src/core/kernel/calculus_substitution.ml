open Calculus_def
open Calculus_misc

(*************************************)
(*      substitution/rewriting       *)
(*************************************)

(* substitution = replace variables (free or bound) by terms (used for typechecking/inference with free variables, and for reduction with bound variable) *)

(* shifting of terms *)
let rec shift_term (te: term) (delta: int) : term =
  leveled_shift_term te 0 delta

(* shift bvar index in a term, above a given index *)
and leveled_shift_term (te: term) (level: int) (delta: int) : term =
  match te with
    | Universe _ -> te
    | Cste (n, ty, pos, reduced) -> Cste (n, leveled_shift_typeannotation ty level delta, pos, reduced)
    | AVar (ty, pos) -> AVar (leveled_shift_typeannotation ty level delta, pos)
    | TName (n, ty, pos) -> TName (n, leveled_shift_typeannotation ty level delta, pos)
      
    | Var (i, ty, pos) when i < 0 -> Var (i, leveled_shift_typeannotation ty level delta, pos)

    | Var (i, ty, pos) when i >= 0 ->
      if i >= level then
	if i + delta < level then (
	  raise (PoussinException (Unshiftable_term (te, level, delta)))
	)
	else
	  Var (i + delta, leveled_shift_typeannotation ty level delta, pos)
      else
	Var (i, leveled_shift_typeannotation ty level delta, pos)

    | App (te, args, ty, pos, reduced) ->
      App (
	leveled_shift_term te level delta,
	List.map (fun (te, n) -> leveled_shift_term te level delta, n) args,
	leveled_shift_typeannotation ty level delta,
	pos,
	reduced
      )

    | Forall ((s, ty, n, p), te, ty2, pos, reduced) ->
      Forall ((s, leveled_shift_term ty level delta, n, p), leveled_shift_term te (level + 1) delta,
	      leveled_shift_typeannotation ty2 level delta,
	      pos, reduced)

    | Lambda ((s, ty, n, p), te, ty2, pos, reduced) ->
      Lambda ((s, leveled_shift_term ty level delta, n, p), leveled_shift_term te (level + 1) delta, 
	      leveled_shift_typeannotation ty2 level delta,
	      pos, reduced)

    | Let ((s, ty,p), te, ty2, pos, reduced) ->
      Let ((s, leveled_shift_term ty level delta, p), leveled_shift_term te (level + 1) delta, 
	      leveled_shift_typeannotation ty2 level delta,
	      pos, reduced)

    | Match (te, des, ty, pos, reduced) ->
      Match (leveled_shift_term te level delta,
	     List.map (fun des -> leveled_shift_destructor des level delta) des,
	     leveled_shift_typeannotation ty level delta,
	     pos, reduced)

and leveled_shift_typeannotation (ty: typeannotation) (level: int) (delta: int) : typeannotation =
  match ty with
    | NoAnnotation -> NoAnnotation
    | Annotation te -> Annotation (leveled_shift_term te level delta)
    | Typed te -> Typed (leveled_shift_term te level delta)

and leveled_shift_destructor (des: pattern list * term) (level: int) (delta: int) : pattern list * term =
  let (ps, te) = des in
  let sz = patterns_size ps in
  ps, leveled_shift_term te (level + sz) delta

(* shift substitution *)
let rec shift_substitution (s: substitution) (delta: int) : substitution =
  IndexMap.fold (fun key value acc -> 
    try 
      if key < 0 then 
	IndexMap.add key (shift_term value delta) acc
      else 
	if key + delta < 0 then acc else IndexMap.add (key + delta) (shift_term value delta) acc 
    with
      | PoussinException (Unshiftable_term _) -> acc
  ) s IndexMap.empty

(* substitution *)
let rec term_substitution (s: substitution) (te: term) : term =
  match te with
    | Universe _ -> te
    | Cste (n, ty, pos, reduced) -> Cste (n, typeannotation_substitution s ty, pos, reduced)
    | Var (i, ty, pos) -> 
      (
	try 
	  IndexMap.find i s 
	with
	  | Not_found -> Var (i, typeannotation_substitution s ty, pos)
      )

    | AVar _ -> raise (PoussinException (FreeError "term_substitution catastrophic: AVar"))
    | TName _ -> raise (PoussinException (FreeError "term_substitution catastrophic: TName"))

    | App (te, args, ty, pos, reduced) ->
      App (term_substitution s te,
	   List.map (fun (te, n) -> term_substitution s te, n) args,
	   typeannotation_substitution s ty,
	   pos, false)

    | Forall ((symb, ty, n, p), te, ty2, pos, reduced) ->
      Forall ((symb, term_substitution s ty, n, p),
	      term_substitution (shift_substitution s 1) te,
	      typeannotation_substitution s ty2,
	      pos, false)

    | Lambda ((symb, ty, n, p), te, ty2, pos, reduced) ->
      Lambda ((symb, term_substitution s ty, n, p),
	      term_substitution (shift_substitution s 1) te,
	      typeannotation_substitution s ty2,
	      pos, false)

    | Let ((symb, ty, p), te, ty2, pos, reduced) ->
      Let ((symb, term_substitution s ty, p),
	      term_substitution (shift_substitution s 1) te,
	      typeannotation_substitution s ty2,
	      pos, false)

    | Match (te, des, ty, p, reduced) ->
      Match (term_substitution s te,
	     List.map (fun des -> destructor_substitution s des) des,
	     typeannotation_substitution s ty,
	     p, false
      )

and typeannotation_substitution (s: substitution) (ty: typeannotation) : typeannotation =
  match ty with
    | NoAnnotation -> NoAnnotation
    | Annotation te -> Annotation (term_substitution s te)
    | Typed te -> Typed (term_substitution s te)

and destructor_substitution (s: substitution) (des: pattern list * term) : pattern list * term =
  let (ps, te) = des in
  let sz = patterns_size ps in
  (ps, term_substitution (shift_substitution s sz) te)




    
