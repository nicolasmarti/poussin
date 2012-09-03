open Calculus_def
open Extlist
open Libparser
open Printf

(* Some general constante *)


(* Some general functions to build terms *)
let type_ ?(pos: position = NoPosition) (level: uLevel) : term =
  { ast = Universe(Type, level); annot = NoAnnotation; tpos = pos; reduced = false }

let set_ ?(pos: position = NoPosition) (level: uLevel) : term =
  { ast = Universe(Set, level); annot = NoAnnotation; tpos = pos; reduced = false }

let prop_ ?(pos: position = NoPosition) (level: uLevel) : term =
  { ast = Universe(Prop, level); annot = NoAnnotation; tpos = pos; reduced = false }

let cste_ ?(annot: typeannotation = NoAnnotation) ?(pos: position = NoPosition) (name: name) : term =
  { ast = Cste name; annot = annot; tpos = pos; reduced = false }

let var_ ?(annot: typeannotation = NoAnnotation) ?(pos: position = NoPosition) (idx: index) : term =
  { ast = Var idx; annot = annot; tpos = pos; reduced = false }

let avar_ ?(annot: typeannotation = NoAnnotation) ?(pos: position = NoPosition) () : term =
  { ast = AVar; annot = annot; tpos = pos; reduced = false }

let name_ ?(annot: typeannotation = NoAnnotation) ?(pos: position = NoPosition) (name: name) : term =
  { ast = TName name; annot = annot; tpos = pos; reduced = false }

let lambda_ ?(annot: typeannotation = NoAnnotation) ?(pos: position = NoPosition) (name: name) ?(nature: nature = Explicit) ?(ty: term = avar_ ()) (body: term) : term =
  { ast = Lambda ((name, ty, nature), body); annot = annot; tpos = pos; reduced = false }

let forall_ ?(annot: typeannotation = NoAnnotation) ?(pos: position = NoPosition) (name: name) ?(nature: nature = Explicit) ?(ty: term = avar_ ()) (body: term) : term =
  { ast = Forall ((name, ty, nature), body); annot = annot; tpos = pos; reduced = false }

let let_ ?(annot: typeannotation = NoAnnotation) ?(pos: position = NoPosition) (name: name) (value: term) (body: term) : term =
  { ast = Let ((name, value), body); annot = annot; tpos = pos; reduced = false }

let app_ ?(annot: typeannotation = NoAnnotation) ?(pos: position = NoPosition) f args =
  { ast = App (f, args); annot = annot; tpos = pos; reduced = false }

let match_ ?(annot: typeannotation = NoAnnotation) ?(pos: position = NoPosition) t des =
  { ast = Match (t, des); annot = annot; tpos = pos; reduced = false }

(* functions to get/set term annotation *)
let get_term_typeannotation (te: term) : typeannotation =
  te.annot

let set_term_typeannotation (te: term) (ty: typeannotation) : term =
  { te with annot = ty }

let set_term_typedannotation (te: term) (ty: term) : term =
  set_term_typeannotation te (TypedAnnotation ty)

let set_term_annotation (te: term) (ty: term) : term =
  set_term_typeannotation te (Annotation ty)

let set_term_typed (te: term) (ty: term) : term =
  set_term_typeannotation te (Typed ty)

let set_term_noannotation (te: term) : term =
  set_term_typeannotation te NoAnnotation


(* shift a set of variable *)
let shift_vars (vars: IndexSet.t) (delta: int) : IndexSet.t =
  IndexSet.fold (fun e acc ->
    if (e >= 0 && e + delta < 0) || e < 0 then acc
    else IndexSet.add (e + delta) acc      
  ) vars IndexSet.empty


(* size in PName of a pattern *)
let rec pattern_size (p: pattern) : int =
  match p with
    | PAvar -> 1
    | PName s -> 1
    | PCste _ -> 0
    | PApp (_, args) ->
      List.fold_left (fun acc arg -> acc + pattern_size (fst arg)) 0 args

let rec patterns_size (ps: pattern list) : int =
  List.fold_left (fun acc p -> 
    if pattern_size p != acc then raise (Failure "patterns_size: all patterns does not have the same number of names");
    acc
  ) (pattern_size (List.hd ps)) (List.tl ps)

(* list of names in a pattern *)
let rec pattern_vars (p: pattern) : name list =
  match p with
    | PAvar -> ["_"]
    | PName s -> [s]
    | PCste _ -> []
    | PApp (_, args) ->
      List.fold_left (fun acc arg -> acc @ pattern_vars (fst arg)) [] args

let rec patterns_vars (ps: pattern list) : name list =
  List.fold_left (fun acc p -> 
    if pattern_vars p != acc then raise (Failure "patterns_vars: all patterns does not have the same list of names");
    acc
  ) (pattern_vars (List.hd ps)) (List.tl ps)


(* the set of free variable in a term *)
let rec fv_term (te: term) : IndexSet.t =
  match te.ast with
    | Universe _ | AVar _ | TName _ | Cste _ | Interactive -> fv_typeannotation te.annot
    | Var i when i < 0 -> IndexSet.add i (fv_typeannotation te.annot)
    | Var i when i >= 0 -> fv_typeannotation te.annot
    | Lambda ((_, ty, _), body) ->
      IndexSet.union (fv_typeannotation te.annot) (IndexSet.union (fv_term ty) (fv_term body))
    | Forall ((_, ty, _), body) ->
      IndexSet.union (fv_typeannotation te.annot) (IndexSet.union (fv_term ty) (fv_term body))
    | Let ((_, te1), te2) ->
      IndexSet.union (fv_typeannotation te.annot) (IndexSet.union (fv_term te1) (fv_term te2))
    | App (f, args) -> List.fold_left (fun acc (te, _) -> IndexSet.union acc (fv_term te)) (IndexSet.union (fv_typeannotation te.annot) (fv_term f)) args
    | Match (m, des) ->
      List.fold_left (fun acc (_, eq) -> IndexSet.union acc (fv_term eq)) (IndexSet.union (fv_typeannotation te.annot) (fv_term m)) des

and fv_typeannotation (ty: typeannotation) : IndexSet.t =
  match ty with
    | NoAnnotation -> IndexSet.empty
    | Annotation te -> fv_term te
    | TypedAnnotation te -> fv_term te
    | Typed te -> fv_term te

(* the set of bounded variable in a term NB: does not take into account vars in type annotation *)
let rec bv_term (te: term) : IndexSet.t =
  match te.ast with
    | Universe _ | AVar _ | TName _ | Cste _ | Interactive -> bv_typeannotation te.annot
    | Var i when i < 0 -> bv_typeannotation te.annot
    | Var i when i >= 0 -> IndexSet.add i (bv_typeannotation te.annot)
    | Lambda ((_, ty, _), body) ->
      IndexSet.union (bv_typeannotation te.annot) (IndexSet.union (bv_term ty) (shift_vars (bv_term body) (-1)))
    | Forall ((_, ty, _), body) ->
      IndexSet.union (bv_typeannotation te.annot) (IndexSet.union (bv_term ty) (shift_vars (bv_term body) (-1)))
    | Let ((_, te1), te2) ->
      IndexSet.union (bv_typeannotation te.annot) (IndexSet.union (bv_term te1) (shift_vars (bv_term te2) (-1)))
    | App (f, args) -> List.fold_left (fun acc (te, _) -> IndexSet.union acc (bv_term te)) (IndexSet.union (bv_typeannotation te.annot) (bv_term f)) args
    | Match (m, des) ->
      List.fold_left (fun acc eq -> IndexSet.union acc (destructor_bv_term eq)) (bv_term m) des


and destructor_bv_term (des: (pattern list * term)) : IndexSet.t =
    (shift_vars (bv_term (snd des)) (patterns_size (fst des)))

and bv_typeannotation (ty: typeannotation) : IndexSet.t =
  match ty with
    | NoAnnotation -> IndexSet.empty
    | Annotation te -> bv_term te
    | TypedAnnotation te -> bv_term te
    | Typed te -> bv_term te

(* the set of cste in a term *)
let rec cste_term (te: term) : NameSet.t =
  match te.ast with
    | Universe _ | AVar _ | TName _ | Var _ | Interactive -> cste_typeannotation te.annot
    | Cste c ->  NameSet.add c (cste_typeannotation te.annot)
    | Lambda ((_, ty, _), body) ->
      NameSet.union (cste_typeannotation te.annot) (NameSet.union (cste_term ty) (cste_term body))
    | Forall ((_, ty, _), body) ->
      NameSet.union (cste_typeannotation te.annot) (NameSet.union (cste_term ty) (cste_term body))
    | Let ((_, te1), te2) ->
      NameSet.union (cste_typeannotation te.annot) (NameSet.union (cste_term te1) (cste_term te2))
    | App (f, args) -> List.fold_left (fun acc (te, _) -> NameSet.union acc (cste_term te)) (NameSet.union (cste_typeannotation te.annot) (cste_term f)) args
    | Match (m, des) ->
      List.fold_left (fun acc eq -> NameSet.union acc (cste_term (snd eq))) (cste_term m) des

and cste_typeannotation (ty: typeannotation) : NameSet.t =
  match ty with
    | NoAnnotation -> NameSet.empty
    | Annotation te -> cste_term te
    | TypedAnnotation te -> cste_term te
    | Typed te -> cste_term te

(* the set of cste in a term *)
let rec name_term (te: term) : NameSet.t =
  match te.ast with
    | Universe _ | AVar _ | Cste _ | Var _ | Interactive -> name_typeannotation te.annot
    | TName c ->  NameSet.add c (name_typeannotation te.annot)
    | Lambda ((_, ty, _), body) ->
      NameSet.union (name_typeannotation te.annot) (NameSet.union (name_term ty) (name_term body))
    | Forall ((_, ty, _), body) ->
      NameSet.union (name_typeannotation te.annot) (NameSet.union (name_term ty) (name_term body))
    | Let ((_, te1), te2) ->
      NameSet.union (name_typeannotation te.annot) (NameSet.union (name_term te1) (name_term te2))
    | App (f, args) -> List.fold_left (fun acc (te, _) -> NameSet.union acc (name_term te)) (NameSet.union (name_typeannotation te.annot) (name_term f)) args
    | Match (m, des) ->
      List.fold_left (fun acc eq -> NameSet.union acc (name_term (snd eq))) (name_term m) des

and name_typeannotation (ty: typeannotation) : NameSet.t =
  match ty with
    | NoAnnotation -> NameSet.empty
    | Annotation te -> name_term te
    | TypedAnnotation te -> name_term te
    | Typed te -> name_term te

 
(* some name freshness *)
let rec add_string_index (y: string) index =
  let len = (String.length y - index) in
  match (String.get y) len with 
    | c when c >= '0' && c < '9' -> (String.set y len (char_of_int (int_of_char c + 1))); y 
    | '9' -> (String.set y len '0'); (add_string_index (y: string) (index + 1));
    | c -> (String.concat "" (y :: "0" :: [])) ;;

let rec fresh_name ?(basename: string = "H") (s: NameSet.t) : string =
  if NameSet.mem basename s then
    fresh_name ~basename:(add_string_index basename 1) s
  else
    basename

let rec fresh_name_list ?(basename: string = "H") (l: name list) : string =
  if List.mem basename l then
    fresh_name_list ~basename:(add_string_index basename 1) l
  else
    basename

(* returns only the elements that are explicit *)
let filter_explicit (l: ('a * nature) list) : 'a list =
  List.map fst (List.filter (fun (_, n) -> n = Explicit) l)

(* position to/from pos *)
let pos_from_position (p: position) : pos =
  match p with
    | NoPosition -> nopos
    | Position (p, _) -> p
let pos_to_position (p: pos) : position =
  Position (p, [])


(* get/set the outermost term position *)
let get_term_pos (te: term) : position =
  te.tpos

let set_term_pos (te: term) (pos: position) : term =
 { te with tpos = pos }


(* function for deconstructing/constructing contiguous lambdas *)
let rec destruct_lambda (te: term) : ((name * term * nature) * typeannotation * position) list * term =
  match te with
    | { ast = Lambda (q, body); annot = annot; tpos = pos; reduced = reduced } ->
      let l, te = destruct_lambda body in
      ((q, annot, pos) :: l, te)
    | _ -> ([], te)

let rec destruct_forall (te: term) : ((name * term * nature) * typeannotation * position) list * term =
  match te with
    | { ast = Forall (q, body); annot = annot; tpos = pos; reduced = reduced } ->
      let l, te = destruct_forall body in
      ((q, annot, pos) :: l, te)
    | _ -> ([], te)

let rec construct_lambda (qs: ((name * term * nature) * typeannotation * position) list) (body: term) : term =
  match qs with
    | [] -> body
    | (hd, annot, pos) :: tl -> { ast = Lambda (hd, construct_lambda tl body); annot = annot; tpos = pos; reduced = false}

let rec construct_forall (qs: ((name * term * nature) * typeannotation * position) list) (body: term) : term =
  match qs with
    | [] -> body
    | (hd, annot, pos) :: tl -> { ast = Forall (hd, construct_forall tl body); annot = annot; tpos = pos; reduced = false}

(* computing the numbers of first implicits *)
let nb_first_implicits (te: term) : int option =
  let qs, _ = destruct_forall te in
  match qs with 
    | [] -> None
    | _ -> Some (
      List.fold_left (fun acc ((_, _, n), _, _) -> if n = Implicit then acc + 1 else acc) 0 qs
    )
  
(* build an implication: no shifting in types !!! (used by the parser) *)
let build_impl (symbols: (name * pos) list) (ty: term) (nature: nature) (body: term) : term =
  List.fold_right (fun (s, pos) acc -> 
    { ast = Forall ((s, ty, nature), acc);
      annot = NoAnnotation;
      tpos = Position ((fst pos, snd (pos_from_position (get_term_pos acc))), []);
      reduced = false;
    }
  ) symbols body

(* build a Forall: no shifting in types !!! (used by the parser) *)
let build_impls (qs: ((name * pos) list * term * nature) list) (body: term) : term =
  List.fold_right (fun (s, ty, n) acc -> build_impl s ty n acc) qs body

(* build a Lambda: no shifting in types !!! *)
let build_lambda (symbols: (name * pos) list) (ty: term) (nature: nature) (body: term) : term =
  List.fold_right (fun (s, pos) acc -> 
    { ast = Lambda ((s, ty, nature), acc);
      annot = NoAnnotation;
      tpos = Position ((fst pos, snd (pos_from_position (get_term_pos acc))), []);
      reduced = false;
    }
  ) symbols body


(* build a Lambda: no shifting in types !!! (used by the parser) *)
let build_lambdas (qs: ((name * pos) list * term * nature) list) (body: term) : term =
  List.fold_right (fun (s, ty, n) acc -> build_lambda s ty n acc) qs body

(* returns if a term is reduced *)
let get_term_reduced (te: term) : reduced =
  te.reduced

(* set a term as reduced *)
let rec set_term_reduced ?(recursive: bool = false) (reduced: bool) (te: term) : term =
  let te =
  match te.ast with
    | _ when get_term_reduced te = reduced && not recursive -> te

    | Universe _ | Var _ | AVar _ | TName _ | Cste _ | Interactive -> { te with reduced = reduced }
    | Lambda (q, body) -> 
      { te with ast = Lambda (q, if recursive then set_term_reduced ~recursive:recursive reduced body else body); reduced = reduced }
    | Forall (q, body) -> 
      { te with ast = Forall (q, if recursive then set_term_reduced ~recursive:recursive reduced body else body); reduced = reduced }
    | Let (q, body) -> 
      { te with ast = Let (q, if recursive then set_term_reduced ~recursive:recursive reduced body else body); reduced = reduced }
    | App (f, args) -> 
      { te with ast = App ((if recursive then set_term_reduced ~recursive:recursive reduced f else f),  
			   if recursive then (List.map (fun (te, n) -> set_term_reduced ~recursive:recursive reduced te,n) args) else args); reduced = reduced }
    | Match (m, des) -> 
      { te with ast = Match ((if recursive then set_term_reduced ~recursive:recursive reduced m else m), 
			     if recursive then (List.map (fun (ps, te) -> ps, set_term_reduced ~recursive:recursive reduced te) des) else des); reduced = reduced }
  in
  if recursive then
  { te with annot = set_typeannotation_reduced ~recursive:recursive reduced te.annot }
  else te

and set_typeannotation_reduced ?(recursive: bool = false) (reduced: bool) (ty: typeannotation): typeannotation =
  match ty with
    | NoAnnotation -> NoAnnotation
    | Annotation te -> Annotation (set_term_reduced ~recursive:recursive reduced te)
    | TypedAnnotation te -> TypedAnnotation (set_term_reduced ~recursive:recursive reduced te)
    | Typed te -> Typed (set_term_reduced ~recursive:recursive reduced te)
 

(* get the typeannotation of a typed term *)
let get_type (te: term) : term =
  match te.ast with
    | Universe (ty, lvl) -> type_ (USucc lvl)
    | _ -> let Typed ty = te.annot in ty

(* an empty context *)
let empty_context = {
  bvs = [];
  fvs = [];
  conversion_hyps = [];
  lvl_cste = [];
}
    

(* returns if a definition is irreducible (an inductive or a constructor) *)
let is_irreducible (defs: defs) (n: name) : bool =
  match Hashtbl.find defs n with
    | Inductive _ | Constructor _ -> true
    | Axiom _ | Definition _ -> false


let nature_unify (n1: nature) (n2: nature) : nature option =
  match n1, n2 with
    | NJoker, NJoker | Explicit, Implicit | Implicit, Explicit -> None
    | NJoker, _ -> Some n2
    | _, NJoker -> Some n1
    | Explicit, Explicit -> Some Explicit
    | Implicit, Implicit -> Some Implicit

let rec app_head (te: term) : term =
  match te.ast with
    | App (hd, _) ->
      app_head hd
    | _ -> te

let rec app_args (te: term) : (term * nature) list =
  match te.ast with
    | App (hd, args) ->
      (app_args hd) @ args
    | _ -> []

let maybe_constante (te: term): name option =
  match (app_head te).ast with
    | Cste c -> Some c
    | _ -> None

let get_cste (defs: defs) (n: name) : value =
  try 
    Hashtbl.find defs n
  with
    | Not_found -> raise (PoussinException (UnknownCste n))

let get_constructor (defs: defs) (n: name) : term =
  match get_cste defs n with
    | Constructor _ -> cste_ n
    | _ -> raise (PoussinException (CsteNotConstructor n))

let get_inductive (defs: defs) (n: name) : term =
  match get_cste defs n with
    | Inductive _ -> cste_ n
    | _ -> raise (PoussinException (CsteNotInductive n))

let rec pattern_to_term (defs: defs) (p: pattern) : term =
  fst (pattern_to_term_loop defs p (pattern_size p - 1))

and pattern_to_term_loop (defs: defs) (p: pattern) (i: int): term * int =
  match p with
    | PAvar -> (var_ i, i - 1)
    | PName s -> (var_ i, i-1)
    | PCste c -> (get_constructor defs c, i)
    | PApp (n, args) ->
      let args, i = List.fold_left (fun (hds, i) (p, n) ->
	let p, i = pattern_to_term_loop defs p i in
	((hds @ [p, n]), i)
      ) ([], i) args in
      (app_ (get_constructor defs n) args, i)


(* is clean term:
   no lambda, no match, ....
 *)
let rec is_clean_term (te: term) : bool =
  match te.ast with
    | Universe _ | Cste _ | Var _ | AVar _ | TName _ -> true
    | Let _ | Lambda _ | Match _ -> false
    | Forall (_, te) -> is_clean_term te
    | App (f, args) ->
      List.fold_left (fun acc (hd, _) -> acc && is_clean_term hd) (is_clean_term f) args

(* does a constante appears negatively *)	  
let rec neg_occur_cste (te: term) (n: name) : bool = false

(* shifting of terms *)
let rec shift_term (te: term) (delta: int) : term =
  leveled_shift_term te 0 delta

(* shift bvar index in a term, above a given index *)
and leveled_shift_term (te: term) (level: int) (delta: int) : term =
  let te =
    match te.ast with
      | Universe _ | Cste _ | AVar | TName _ | Interactive -> te
	
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


(* simpl pattern match *)
let rec pattern_match (ctxt: context ref) (p: pattern) (te: term) : (term list) option =
  match p with
    | PAvar -> Some [te]
    | PName s -> Some [te]
    | PCste c -> (
      match te.ast with
	| Cste c2 when c = c2 -> Some []
	| _ -> (*printf "%s <> %s (1)\n" (pattern2string ctxt p) (term2string ctxt te);*) None
    )
    | PApp (c, args) ->
      match te.ast with
	| Cste c2 when c = c2 && List.length args = 0 -> Some []
	| App ({ ast = Cste c2; _} , args2) when c = c2 && List.length args = List.length args2 ->
	  List.fold_left (fun acc (hd1, hd2) -> 
	    match acc with
	      | None -> None
	      | Some l ->
		match pattern_match ctxt hd1 hd2 with
		  | None -> None
		  | Some l' -> Some (l @ l')
	  ) (Some []) (List.map2 (fun hd1 hd2 -> (fst hd1, fst hd2)) args args2)
	| _ -> (*printf "%s <> %s (2)\n" (* (term2string ctxt te)*) (pattern2string ctxt p) (term2string ctxt te);*) None


(**)
let context_add_lvl_contraint (ctxt: context ref) (c: uLevel_constraints) : unit =
  ctxt := { !ctxt with lvl_cste = c::!ctxt.lvl_cste }

(**)
let context_add_conversion (ctxt: context ref) (te1: term) (te2: term) : unit =
  (*printf "added conversion: %s == %s\n" (term2string ctxt te1) (term2string ctxt te2);*)
  ctxt := { !ctxt with conversion_hyps = ((te1, te2)::(!ctxt.conversion_hyps)) }
  (*printf "%s\n"(conversion_hyps2string ctxt (!ctxt.conversion_hyps))*)


(* retrieve the debruijn index of a bound var through its symbol *)
let var_lookup (ctxt: context ref) (n: name) : index option =
  let res = fold_stop (fun level frame ->
    if frame.name = n then Right level else Left (level+1)
  ) 0 !ctxt.bvs in
  match res with
    | Left _ -> (
      let res = fold_stop (fun () (i, _, _, n') ->
	match n' with
	  | Some n' when n' = n -> Right i
	  | _ -> Left ()
      ) () !ctxt.fvs in
      match res with
	| Left () -> None
	| Right i -> Some i
    )
    | Right level -> Some level

let get_fvar (ctxt: context ref) (i: index) : (term * term option * name option) =
  let lookup = fold_stop (fun () (index, ty, value, name) -> 
    if index = i then Right (ty, value, name) else Left ()
  ) () !ctxt.fvs in
  match lookup with
    | Left _ -> raise (PoussinException (UnknownFVar (!ctxt, i)))
    | Right res -> res

let fvar_subst (ctxt: context ref) (i: index) : term option =
  let (_, te, _) = get_fvar ctxt i in
  te

(* grab the type of a free var *)
let fvar_type (ctxt: context ref) (i: index) : term =
  let (ty, _, _) = get_fvar ctxt i in
  ty

(* grab the type of a bound var *)
let bvar_type (ctxt: context ref) (i: index) : term =
  try (
    let frame = List.nth !ctxt.bvs i in
    let ty = frame.ty in
    shift_term ty i
  ) with
    | Failure "nth" -> raise (PoussinException (UnknownBVar (!ctxt, i)))
    | Invalid_argument "List.nth" -> raise (PoussinException (NegativeIndexBVar i))

(* grab the name of a bound var *)
let bvar_name (ctxt: context ref) (i: index) : name =
  try (
    let frame = List.nth !ctxt.bvs i in
    frame.name
  ) with
    | Failure "nth" -> raise (PoussinException (UnknownBVar (!ctxt, i)))
    | Invalid_argument "List.nth" -> raise (PoussinException (NegativeIndexBVar i))

(* we add a free variable *)
let rec add_fvar ?(pos: position = NoPosition) ?(name: name option = None) ?(te: term option = None) ?(ty: term option = None) (ctxt: context ref) : term =
  let ty = match ty with
    | None -> add_fvar ~ty:(Some (type_ (UName""))) ctxt
    | Some ty -> ty 
      in
  let next_fvar_index = 
      match !ctxt.fvs with
	| [] -> (-1)
	| (i, _, _, _)::_ -> (i - 1)
  in
  ctxt := { !ctxt with 
    fvs = ((next_fvar_index, ty, te, name)::!ctxt.fvs)
  };
  (*printf "adding %s\n" (string_of_int next_fvar_index);
  ignore(fvar_subst ctxt next_fvar_index);*)
  var_ ~annot:(Typed ty) ~pos:pos next_fvar_index

(* strict equality *)
let rec term_equal (te1: term) (te2: term) : bool =
  match te1.ast, te2.ast with
    | Universe (u1, lvl1), Universe (u2, lvl2) -> u2 = u1
    | Cste n1, Cste n2 -> n1 = n2
    | Var i1, Var i2 -> i1 = i2
    | Lambda ((_, ty1, n1), te1), Lambda ((_, ty2, n2), te2) ->
      term_equal ty1 ty2 && n1 = n2 && term_equal te1 te2
    | Forall ((_, ty1, n1), te1), Forall ((_, ty2, n2), te2) ->
      term_equal ty1 ty2 && n1 = n2 && term_equal te1 te2
    | Let ((_, val1), te1), Let ((_, val2), te2) ->
      term_equal val1 val2 && term_equal te1 te2
    | App (f1, args1), App (f2, args2) when List.length args1 = List.length args2 && (term_equal f1 f2) ->
      List.fold_left (fun acc ((arg1, n1), (arg2, n2)) ->
	if n1 = n2 && term_equal arg1 arg2 then
	  acc else false
      ) true (List.combine args1 args2)
    | Match (te1, des1), Match (te2, des2) when List.length des1 = List.length des2 && term_equal te1 te2 ->
      List.fold_left (fun acc ((ps1, te1), (ps2, te2)) -> 
	if ps1 = ps2 && term_equal te1 te2 then
	  acc
	else false
      ) true (List.combine des1 des2)
    | _ -> false
      
