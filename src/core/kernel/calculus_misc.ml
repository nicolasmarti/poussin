open Calculus_def
open Extlist
open Libparser
open Printf

(* Some general constante *)

(* Some general functions to build terms *)
let type_ ?(pos: position = NoPosition) (level: uLevel) : term =
  Universe(Type, level, pos)

let set_ ?(pos: position = NoPosition) (level: uLevel) : term =
  Universe(Set, level, pos)

let prop_ ?(pos: position = NoPosition) (level: uLevel) : term =
  Universe(Prop, level, pos)

let cste_ ?(annot: typeannotation = NoAnnotation) ?(pos: position = NoPosition) (name: name) : term =
  Cste(name, annot, pos, false)

let var_ ?(annot: typeannotation = NoAnnotation) ?(pos: position = NoPosition) (idx: index) : term =
  Var(idx, annot, pos)

let avar_ ?(annot: typeannotation = NoAnnotation) ?(pos: position = NoPosition) () : term =
  AVar(annot, pos)

let name_ ?(annot: typeannotation = NoAnnotation) ?(pos: position = NoPosition) (name: name) : term =
  TName(name, annot, pos)

let lambda_ ?(annot: typeannotation = NoAnnotation) ?(posq: position = NoPosition) ?(posl: position = NoPosition) (name: name) ?(nature: nature = Explicit) ?(ty: term = avar_ ()) (body: term) : term =
  Lambda ((name, ty, nature, posl), body, annot, posl, false)

let forall_ ?(annot: typeannotation = NoAnnotation) ?(posq: position = NoPosition) ?(posl: position = NoPosition) (name: name) ?(nature: nature = Explicit) ?(ty: term = avar_ ()) (body: term) : term =
  Forall ((name, ty, nature, posl), body, annot, posl, false)

let app_ ?(annot: typeannotation = NoAnnotation) ?(pos: position = NoPosition) f args =
  App (f, args, annot, pos, false)

(* function for deconstructing/constructing contiguous lambdas *)
let rec destruct_lambda (te: term) : ((name * term * nature * position) * typeannotation * position) list * term =
  match te with
    | Lambda (q, body, annot, pos, reduced) ->
      let l, te = destruct_lambda body in
      ((q, annot, pos) :: l, te)
    | _ -> ([], te)

let rec destruct_forall (te: term) : ((name * term * nature * position) * typeannotation * position) list * term =
  match te with
    | Forall (q, body, annot, pos, reduced) ->
      let l, te = destruct_forall body in
      ((q, annot, pos) :: l, te)
    | _ -> ([], te)

let rec construct_lambda (qs: ((name * term * nature * position) * typeannotation * position) list) (body: term) : term =
  match qs with
    | [] -> body
    | (hd, annot, pos) :: tl -> Lambda (hd, construct_lambda tl body, annot, pos, false)

(* functions to get/set term annotation *)
let get_term_typeannotation (te: term) : typeannotation =
  match te with
    | Universe (ty, lvl, pos) -> NoAnnotation
    | Cste (n, ty, pos, reduced) -> ty
    | Var (i, ty, pos) -> ty
    | AVar (ty, pos) -> ty
    | TName (n, ty, pos) -> ty
    | Lambda (q, te, ty, pos, reduced) -> ty
    | Forall (q, te, ty, pos, reduced) -> ty
    | Let (q, te, ty, pos, reduced) -> ty
    | App (f, args, ty, pos, reduced) -> ty
    | Match (te, des, ty, pos, reduced) -> ty

let set_term_typeannotation (te: term) (ty: typeannotation) : term =
  match te with
    | Universe (ty, lvl, pos) -> 
      Universe (ty, lvl, pos)
    | Cste (n, _, pos, reduced) ->
      Cste (n, ty, pos, reduced)
    | Var (i, _, pos) ->
      Var (i, ty, pos)
    | AVar (_, pos) ->
      AVar (ty, pos)
    | TName (n, _, pos) ->
      TName (n, ty, pos)
    | Lambda (q, te, _, pos, reduced) ->
      Lambda (q, te, ty, pos, reduced)
    | Forall (q, te, _, pos, reduced) ->
      Forall (q, te, ty, pos, reduced)
    | Let (q, te, _, pos, reduced) ->
      Let (q, te, ty, pos, reduced)
    | App (f, args, _, pos, reduced) ->
      App (f, args, ty, pos, reduced)
    | Match (te, des, _, pos, reduced) ->
      Match (te, des, ty, pos, reduced)

let set_term_typedannotation (te: term) (ty: term) : term =
  set_term_typeannotation te (TypedAnnotation ty)

let set_term_annotation (te: term) (ty: term) : term =
  set_term_typeannotation te (Annotation ty)

let set_term_typed (te: term) (ty: term) : term =
  set_term_typeannotation te (Typed ty)

let set_term_noannotation (te: term) : term =
  set_term_typeannotation te NoAnnotation


(* the set of free variable in a term *)
let rec fv_term (te: term) : IndexSet.t =
  match te with
    | Universe _ | AVar _ | TName _ -> IndexSet.empty
    | Cste (_, ty, _, _) -> fv_typeannotation ty
    | Var (i, ty, _) when i < 0 -> IndexSet.union (IndexSet.singleton i) (fv_typeannotation ty)
    | Var (i, ty, _) when i >= 0 -> fv_typeannotation ty
    | Lambda ((_, ty, _, _), te, aty, _, _) ->
      IndexSet.union (fv_typeannotation aty) (IndexSet.union (fv_term ty) (fv_term te))
    | Forall ((_, ty, _, _), te, aty, _, _) ->
      IndexSet.union (fv_typeannotation aty) (IndexSet.union (fv_term ty) (fv_term te))
    | Let ((_, te1, _), te2, aty, _, _) ->
      IndexSet.union (fv_typeannotation aty) (IndexSet.union (fv_term te1) (fv_term te2))
    | App (te, args, aty, _, _) -> List.fold_left (fun acc (te, _) -> IndexSet.union acc (fv_term te)) (IndexSet.union (fv_typeannotation aty) (fv_term te)) args
    | Match (te, des, aty, _, _) ->
      List.fold_left (fun acc (_, eq) -> IndexSet.union acc (fv_term eq)) (IndexSet.union (fv_typeannotation aty) (fv_term te)) des

and fv_typeannotation (ty: typeannotation) : IndexSet.t =
  match ty with
    | NoAnnotation -> IndexSet.empty
    | Annotation te -> fv_term te
    | TypedAnnotation te -> fv_term te
    | Typed te -> fv_term te
  

(* shift a set of variable *)
let shift_vars (vars: IndexSet.t) (delta: int) : IndexSet.t =
  IndexSet.fold (fun e acc ->
    if (e >= 0 && e + delta < 0) || e < 0 then acc
    else IndexSet.add (e + delta) acc      
  ) vars IndexSet.empty

(* size in PName of a pattern *)
let rec pattern_size (p: pattern) : int =
  match p with
    | PAvar -> 0
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
    | PAvar -> []
    | PName s -> [s]
    | PCste _ -> []
    | PApp (_, args) ->
      List.fold_left (fun acc arg -> acc @ pattern_vars (fst arg)) [] args

let rec patterns_vars (ps: pattern list) : name list =
  List.fold_left (fun acc p -> 
    if pattern_vars p != acc then raise (Failure "patterns_vars: all patterns does not have the same list of names");
    acc
  ) (pattern_vars (List.hd ps)) (List.tl ps)

(* the set of bounded variable in a term NB: does not take into account vars in type annotation *)
let rec bv_term (te: term) : IndexSet.t =
  match te with
    | Universe _ | AVar _ | TName _ -> IndexSet.empty
    | Cste (_, aty, _, _) ->  bv_typeannotation aty
    | Var (i, aty, _) when i < 0 -> bv_typeannotation aty
    | Var (i, aty, _) when i >= 0 -> IndexSet.union (bv_typeannotation aty) (IndexSet.singleton i)
    | Lambda ((_, ty, _, _), te, aty, _, _) ->
      IndexSet.union (bv_typeannotation aty) (IndexSet.union (bv_term ty) (shift_vars (bv_term te) (-1)))
    | Forall ((_, ty, _, _), te, aty, _, _) ->
      IndexSet.union (bv_typeannotation aty) (IndexSet.union (bv_term ty) (shift_vars (bv_term te) (-1)))
    | Let ((_, te1, _), te2, aty, _, _) ->
      IndexSet.union (bv_typeannotation aty) (IndexSet.union (bv_term te1) (shift_vars (bv_term te2) (-1)))
    | App (te, args, aty, _, _) -> List.fold_left (fun acc (te, _) -> IndexSet.union acc (bv_term te)) (IndexSet.union (bv_typeannotation aty) (bv_term te)) args
    | Match (te, des, _, _, _) ->
      List.fold_left (fun acc eq -> IndexSet.union acc (destructor_bv_term eq)) (bv_term te) des

and destructor_bv_term (des: (pattern list * term)) : IndexSet.t =
    (shift_vars (bv_term (snd des)) (patterns_size (fst des)))

and bv_typeannotation (ty: typeannotation) : IndexSet.t =
  match ty with
    | NoAnnotation -> IndexSet.empty
    | Annotation te -> bv_term te
    | TypedAnnotation te -> bv_term te
    | Typed te -> bv_term te


(* function that map symbol into string *)
let notation2string (name: string) (op: op) =
  let (pre, post) = 
    match op with
      | Nofix -> "", ""
      | Prefix _ -> "[", ")"
      | Infix _ -> "(", ")"
      | Postfix _ -> "(", "]"
  in
  String.concat "" [pre; name; post]

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

(* *)
let pos_from_position (p: position) : pos =
  match p with
    | NoPosition -> nopos
    | Position (p, _) -> p

(* *)
let pos_to_position (p: pos) : position =
  Position (p, [])

(* get/set the outermost term position *)
let get_term_pos (te: term) : position =
  match te with
    | Universe (ty, lvl, pos) -> pos
    | Cste (n, ty, pos, reduced) -> pos
    | Var (i, ty, pos) -> pos
    | AVar (ty, pos) -> pos
    | TName (n, ty, pos) -> pos
    | Lambda (q, te, ty, pos, reduced) -> pos
    | Forall (q, te, ty, pos, reduced) -> pos
    | Let (q, te, ty, pos, reduced) -> pos
    | App (f, args, ty, pos, reduced) -> pos
    | Match (te, des, ty, pos, reduced) -> pos

let set_term_pos (te: term) (pos: position) : term =
  match te with
    | Universe (ty, lvl, _) ->
      Universe (ty, lvl, pos)
    | Cste (n, ty, _, reduced) ->
      Cste (n, ty, pos, reduced)
    | Var (i, ty, _) ->
      Var (i, ty, pos)
    | AVar (ty, _) ->
      AVar (ty, pos)
    | TName (n, ty, _) ->
      TName (n, ty, pos)
    | Lambda (q, te, ty, _, reduced) ->
      Lambda (q, te, ty, pos, reduced)
    | Forall (q, te, ty, _, reduced) ->
      Forall (q, te, ty, pos, reduced)
    | Let (q, te, ty, _, reduced) ->
      Let (q, te, ty, pos, reduced)
    | App (f, args, ty, _, reduced) ->
      App (f, args, ty, pos, reduced)
    | Match (te, des, ty, _, reduced) ->
      Match (te, des, ty, pos, reduced)

  
(* build an implication: no shifting in types !!! (used by the parser) *)
let build_impl (symbols: (name * pos) list) (ty: term) (nature: nature) (body: term) : term =
  List.fold_right (fun (s, pos) acc -> 
    Forall (
      (s, ty, nature, Position (pos, [])), 
      acc, 
      NoAnnotation,
      Position ((fst pos, snd (pos_from_position (get_term_pos acc))), []),
      false
    )
  ) symbols body

(* build a Forall: no shifting in types !!! (used by the parser) *)
let build_impls (qs: ((name * pos) list * term * nature) list) (body: term) : term =
  List.fold_right (fun (s, ty, n) acc -> build_impl s ty n acc) qs body

(* build a Lambda: no shifting in types !!! *)
let build_lambda (symbols: (name * pos) list) (ty: term) (nature: nature) (body: term) : term =
  List.fold_right (fun (s, pos) acc -> 
    Lambda (
      (s, ty, nature, Position (pos, [])), 
      acc, 
      NoAnnotation,
      Position ((fst pos, snd (pos_from_position (get_term_pos acc))), []),
      false
    )
  )symbols body


(* build a Lambda: no shifting in types !!! (used by the parser) *)
let build_lambdas (qs: ((name * pos) list * term * nature) list) (body: term) : term =
  List.fold_right (fun (s, ty, n) acc -> build_lambda s ty n acc) qs body

(* returns if a term is reduced *)
let get_term_reduced (te: term) : reduced =
  match te with
    | Universe (ty, lvl, pos) -> true
    | Cste (n, ty, pos, reduced) -> reduced
    | Var (i, ty, pos) -> true
    | AVar (ty, pos) -> true
    | TName (n, ty, pos) -> true
    | Lambda (q, te, ty, pos, reduced) -> reduced
    | Forall (q, te, ty, pos, reduced) -> reduced
    | Let (q, te, ty, pos, reduced) -> reduced
    | App (f, args, ty, pos, reduced) -> reduced
    | Match (te, des, ty, pos, reduced) -> reduced

(* set a term as reduced *)
let rec set_term_reduced ?(recursive: bool = false) (reduced: bool) (te: term) : term =
  match te with
    | _ when get_term_reduced te = reduced && not recursive -> te

    | Universe _ | Var _ | AVar _ | TName _ -> te
    | Cste (n, ty, pos, _) -> Cste (n, (if recursive then set_typeannotation_reduced ~recursive:recursive reduced ty else ty), pos, reduced)
    | Lambda (q, te, ty, pos, _) -> 
      Lambda (q, 
	      (if recursive then set_term_reduced ~recursive:recursive reduced te else te), 
	      (if recursive then set_typeannotation_reduced ~recursive:recursive reduced ty else ty), 
	      pos, reduced)
    | Forall (q, te, ty, pos, _) -> 
      Forall (q, 
	      (if recursive then set_term_reduced ~recursive:recursive reduced te else te), 
	      (if recursive then set_typeannotation_reduced ~recursive:recursive reduced ty else ty), 
	      pos, reduced)
    | Let (q, te, ty, pos, _) -> 
      Let (q, 
	   (if recursive then set_term_reduced ~recursive:recursive reduced te else te), 
	   (if recursive then set_typeannotation_reduced ~recursive:recursive reduced ty else ty), 
	   pos, reduced)
    | App (f, args, ty, pos, _) -> 
      App ((if recursive then set_term_reduced ~recursive:recursive reduced f else f),  
	   (if recursive then (List.map (fun (te, n) -> set_term_reduced ~recursive:recursive reduced te,n) args) else args), 
	   (if recursive then set_typeannotation_reduced ~recursive:recursive reduced ty else ty), 
	   pos, reduced)
    | Match (te, des, ty, pos, _) -> 
      Match ((if recursive then set_term_reduced ~recursive:recursive reduced te else te), 
	     (if recursive then (List.map (fun (ps, te) -> ps, set_term_reduced ~recursive:recursive reduced te) des) else des), 
	     (if recursive then set_typeannotation_reduced ~recursive:recursive reduced ty else ty), 
	     pos, reduced)

and set_typeannotation_reduced ?(recursive: bool = false) (reduced: bool) (ty: typeannotation): typeannotation =
  match ty with
    | NoAnnotation -> NoAnnotation
    | Annotation te -> Annotation (set_term_reduced ~recursive:recursive reduced te)
    | TypedAnnotation te -> TypedAnnotation (set_term_reduced ~recursive:recursive reduced te)
    | Typed te -> Typed (set_term_reduced ~recursive:recursive reduced te)
 

(* get the typeannotation of a typed term *)
let get_type (te: term) : term =
  match te with
    | Universe (ty, lvl, pos) -> Universe (Type, USucc lvl, pos)
    | _ -> let Typed ty = get_term_typeannotation te in ty

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
  match te with
    | App (hd, _, _, _, _) ->
      app_head hd
    | _ -> te

let rec app_args (te: term) : (term * nature) list =
  match te with
    | App (hd, args, _, _, _) ->
      (app_args hd) @ args
    | _ -> []

let maybe_constante (te: term): name option =
  match app_head te with
    | Cste (c, _, _, _) -> Some c
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
    | PAvar -> (avar_ (), i)
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
  match te with
    | Universe _ | Cste _ | Var _ | AVar _ | TName _ -> true
    | Let _ | Lambda _ | Match _ -> false
    | Forall (_, te, _, _, _) -> is_clean_term te
    | App (f, args, _, _, _) ->
      List.fold_left (fun acc (hd, _) -> acc && is_clean_term hd) (is_clean_term f) args

(* does a constante appears negatively *)	  
let rec neg_occur_cste (te: term) (n: name) : bool = false
