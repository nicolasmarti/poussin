open Calculus_def
open Calculus_misc
open Calculus_pprinter
open Extlist
open Printf
(*************************************)
(*      substitution/rewriting       *)
(*************************************)

(* substitution = replace variables (free or bound) by terms (used for typechecking/inference with free variables, and for reduction with bound variable) *)

(* shifting of terms *)
let rec shift_term (te: term) (delta: int) : term =
  leveled_shift_term te 0 delta

(* shift bvar index in a term, above a given index *)
and leveled_shift_term (te: term) (level: int) (delta: int) : term =
  let te =
    match te.ast with
      | Universe _ | Cste _ | AVar | TName _ -> te
	
      | Var i when i < 0 -> te

      | Var i when i >= 0 ->
	if i >= level then
	  if i + delta < level then (
	    raise (PoussinException (Unshiftable_term (te, level, delta)))
	  )
	  else
	    { te with ast = Var (i + delta) }
	else
	  te

      | App (f, args) ->
	{ te with ast = App (leveled_shift_term f level delta,
			     List.map (fun (te, n) -> leveled_shift_term te level delta, n) args) }

      | Forall ((s, ty, n), body) ->
	{ te with ast = Forall ((s, leveled_shift_term ty level delta, n), leveled_shift_term body (level + 1) delta) }

      | Lambda ((s, ty, n), body) ->
	{ te with ast = Lambda ((s, leveled_shift_term ty level delta, n), leveled_shift_term body (level + 1) delta) }

      | Let ((s, value), body) ->
	{ te with ast = Let ((s, leveled_shift_term value level delta), leveled_shift_term body (level + 1) delta) }

      | Match (m, des) ->
	{ te with ast = Match (leveled_shift_term m level delta,
			       List.map (fun des -> leveled_shift_destructor des level delta) des) }
  in
  { te with annot = leveled_shift_typeannotation te.annot level delta }

and leveled_shift_typeannotation (ty: typeannotation) (level: int) (delta: int) : typeannotation =
  match ty with
    | NoAnnotation -> NoAnnotation
      (* this case should be an error ... *)
    | Annotation te -> Annotation (leveled_shift_term te level delta)
    | TypedAnnotation te -> TypedAnnotation (leveled_shift_term te level delta)
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
  let te = 
    match te.ast with
      | Universe _ | Cste _ | AVar -> te
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
      s, hd::tl


(**)
let context_add_substitution (ctxt: context ref) (s: substitution) : unit =
  (* computes the needed shited substitution *)
  let ss = fst (mapacc (fun acc hd -> (acc, shift_substitution acc (-1))) s !ctxt.bvs) in
  ctxt := { !ctxt with
    bvs = List.map2 (fun hd1 hd2 -> {hd1 with ty = term_substitution hd2 hd1.ty} ) !ctxt.bvs ss;

    fvs = 
      List.map (fun (i, ty, te, n) -> 
	if IndexMap.mem i s then (
	match te with
	  | None -> (i, term_substitution s ty, Some (IndexMap.find i s), n)
	    (* here we should to the unification between both values (maybe not necessary as addition is always on a singleton ...) *)
	  | Some te -> (i, term_substitution s ty, Some (term_substitution s te), n)
	) else (
	match te with
	  | None -> (i, term_substitution s ty, None, n)
	  | Some te -> (i, term_substitution s ty, Some (term_substitution s te), n)
	)
      ) !ctxt.fvs;

    conversion_hyps = 
      List.map (fun (te1, te2) -> 
	(term_substitution s te1, term_substitution s te2)
      ) !ctxt.conversion_hyps;
  }

    
let substitution_vars (s: substitution) =
  IndexMap.fold (fun k _ acc -> IndexSet.add k acc) s IndexSet.empty

let context2subst (ctxt: context ref) : substitution =
  List.fold_left (fun acc (i, _, te, _) ->
    match te with | None -> acc | Some te -> IndexMap.add i te acc
  ) IndexMap.empty !ctxt.fvs
