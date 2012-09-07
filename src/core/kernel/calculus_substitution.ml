open Calculus_def
open Calculus_misc
open Calculus_pprinter
open Extlist
open Printf
(*************************************)
(*      substitution/rewriting       *)
(*************************************)

(* substitution = replace variables (free or bound) by terms (used for typechecking/inference with free variables, and for reduction with bound variable) *)

(* substitution *)
let rec term_substitution (s: substitution) (te: term) : term =
  let te = 
    match te.ast with
      | Universe _ | Cste _ | AVar | Interactive -> te
      | Var i -> 
	(
	  try 
	    IndexMap.find i s 
	  with
	    | Not_found -> te
	)

      | TName n -> raise (PoussinException (FreeError (String.concat " " ["term_substitution catastrophic: TName"; n])))

      | App (f, args) ->
	{ te with ast = App (term_substitution s f,
			     List.map (fun (te, n) -> term_substitution s te, n) args) }

      | Forall ((symb, ty, n), body) ->
	{ te with ast = Forall ((symb, term_substitution s ty, n),
				term_substitution (shift_substitution s 1) body) }

      | Lambda ((symb, ty, n), body) ->
	{ te with ast = Lambda ((symb, term_substitution s ty, n),
				term_substitution (shift_substitution s 1) body) }

      | Let ((symb, value), body) ->
	{ te with ast = Let ((symb, term_substitution s value),
			     term_substitution (shift_substitution s 1) body) }

      | Match (m, des) ->
	{ te with ast = Match (term_substitution s m,
			       List.map (fun des -> destructor_substitution s des) des) }
  in 
  { te with annot = typeannotation_substitution s te.annot }

and typeannotation_substitution (s: substitution) (ty: typeannotation) : typeannotation =
  match ty with
    | NoAnnotation -> NoAnnotation
    | Annotation te -> Annotation (term_substitution s te)
    | TypedAnnotation te -> TypedAnnotation (term_substitution s te)
    | Typed te -> Typed (term_substitution s te)

and destructor_substitution (s: substitution) (des: pattern list * term) : pattern list * term =
  let (ps, te) = des in
  let sz = patterns_size ps in
  (ps, term_substitution (shift_substitution s sz) te)

(* transform a conversion_hyps list into a substitution *)
let rec conversion_hyps2subst ?(dec_order: bool = false) (cv: (term * term) list) : (substitution * (term * term) list) =
  match cv with
    | [] -> IndexMap.empty,  []
    | ({ ast = Var i; _} , te2)::tl when i >= 0 && IndexSet.is_empty 
	(IndexSet.filter 
	   (fun i' -> if dec_order then i >= i' else i <= i') (bv_term te2)) ->
      let s = IndexMap.singleton i te2 in
      let s', l = conversion_hyps2subst ~dec_order:dec_order (List.map (fun (te1, te2) -> term_substitution s te1, term_substitution s te2) tl) in
      (IndexMap.add i te2 s'), l 

    | (te1, { ast = Var i; _})::tl when i >= 0  && IndexSet.is_empty (IndexSet.filter (fun i' -> if dec_order then i >= i' else i <= i') (bv_term te1)) ->
      let s = IndexMap.singleton i te1 in
      let s', l = conversion_hyps2subst ~dec_order:dec_order (List.map (fun (te1, te2) -> term_substitution s te1, term_substitution s te2) tl) in
      (IndexMap.add i te1 s'), l 

    | (({ ast = Var i; _} , te2) as hd)::tl ->
      let s = IndexMap.singleton i te2 in
      let s', l = conversion_hyps2subst ~dec_order:dec_order (List.map (fun (te1, te2) -> term_substitution s te1, term_substitution s te2) tl) in
      s', hd::l 

    | ((te1, { ast = Var i; _}) as hd)::tl ->
      let s = IndexMap.singleton i te1 in
      let s', l = conversion_hyps2subst ~dec_order:dec_order (List.map (fun (te1, te2) -> term_substitution s te1, term_substitution s te2) tl) in
      s', hd::l 

    | hd::tl -> 
      let s, l = conversion_hyps2subst ~dec_order:dec_order tl in
      s, hd::l


(**)

let substitution_vars (s: substitution) =
  IndexMap.fold (fun k _ acc -> IndexSet.add k acc) s IndexSet.empty

let context2subst (ctxt: context ref) : substitution =
  List.fold_left (fun acc (i, _, te, _) ->
    match te with | None -> acc | Some te -> IndexMap.add i te acc
  ) IndexMap.empty !ctxt.fvs

let append_substitution (s1: substitution) (s2: substitution): substitution =
  let s2 = IndexMap.map (term_substitution s1) s2 in
  IndexMap.merge (fun k v1 v2 ->
    match v1, v2 with
      | Some v1 ,_ -> Some v1
      | _, Some v2 -> Some v2
  ) s1 s2
