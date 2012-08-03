open Calculus_def
open Extlist
open Libparser

(* Some general constante *)

(* Some general functions to build terms *)
let type_ ?(pos: position = NoPosition) (level: uLevel) : term =
  Universe(Type, level, pos)

let set_ ?(pos: position = NoPosition) (level: uLevel) : term =
  Universe(Set, level, pos)

let prop_ ?(pos: position = NoPosition) (level: uLevel) : term =
  Universe(Prop, level, pos)

let cste_ ?(annot: typeannotation = NoAnnotation) ?(pos: position = NoPosition) ?(path: path = []) (name: name) : term =
  Cste(path, name, annot, pos)

let var_ ?(annot: typeannotation = NoAnnotation) ?(pos: position = NoPosition) (idx: index) : term =
  Var(idx, annot, pos)

let avar_ ?(annot: typeannotation = NoAnnotation) ?(pos: position = NoPosition) () : term =
  AVar(annot, pos)

let name_ ?(annot: typeannotation = NoAnnotation) ?(pos: position = NoPosition) (name: name) : term =
  TName(name, annot, pos)

let lambda_ ?(annot: typeannotation = NoAnnotation) ?(posq: position = NoPosition) ?(posl: position = NoPosition) (name: name) ?(nature: nature = Explicit) ?(ty: term = avar_ ()) (body: term) : term =
  Lambda ((name, ty, nature, posl), body, annot, posl)

let forall_ ?(annot: typeannotation = NoAnnotation) ?(posq: position = NoPosition) ?(posl: position = NoPosition) (name: name) ?(nature: nature = Explicit) ?(ty: term = avar_ ()) (body: term) : term =
  Forall ((name, ty, nature, posl), body, annot, posl)

(* function for deconstructing/constructing contiguous lambdas *)
let rec destruct_lambda (te: term) : ((name * term * nature * position) * typeannotation * position) list * term =
  match te with
    | Lambda (q, body, annot, pos) ->
      let l, te = destruct_lambda body in
      ((q, annot, pos) :: l, te)
    | _ -> ([], te)

let rec construct_lambda (qs: ((name * term * nature * position) * typeannotation * position) list) (body: term) : term =
  match qs with
    | [] -> body
    | (hd, annot, pos) :: tl -> Lambda (hd, construct_lambda tl body, annot, pos)

(* functions to get/set term annotation *)
let get_term_annotation (te: term) : typeannotation =
  match te with
    | Universe (ty, lvl, pos) -> NoAnnotation
    | Cste (p, n, ty, pos) -> ty
    | Var (i, ty, pos) -> ty
    | AVar (ty, pos) -> ty
    | TName (n, ty, pos) -> ty
    | Lambda (q, te, ty, pos) -> ty
    | Forall (q, te, ty, pos) -> ty
    | Let (q, te, ty, pos) -> ty
    | App (f, args, ty, pos) -> ty
    | Match (te, des, ty, pos) -> ty

let set_term_annotation (te: term) (ty: term) : term =
  match te with
    | Universe (ty, lvl, pos) -> 
      Universe (ty, lvl, pos)
    | Cste (p, n, _, pos) ->
      Cste (p, n, Annotation ty, pos)
    | Var (i, _, pos) ->
      Var (i, Annotation ty, pos)
    | AVar (_, pos) ->
      AVar (Annotation ty, pos)
    | TName (n, _, pos) ->
      TName (n, Annotation ty, pos)
    | Lambda (q, te, _, pos) ->
      Lambda (q, te, Annotation ty, pos)
    | Forall (q, te, _, pos) ->
      Forall (q, te, Annotation ty, pos)
    | Let (q, te, _, pos) ->
      Let (q, te, Annotation ty, pos)
    | App (f, args, _, pos) ->
      App (f, args, Annotation ty, pos)
    | Match (te, des, _, pos) ->
      Match (te, des, Annotation ty, pos)

(* the set of free variable in a term *)
let rec fv_term (te: term) : IndexSet.t =
  raise (Failure "fv_term: NYI")

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
    | PCstor (_, args) ->
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
    | PCstor (_, args) ->
      List.fold_left (fun acc arg -> acc @ pattern_vars (fst arg)) [] args

let rec patterns_vars (ps: pattern list) : name list =
  List.fold_left (fun acc p -> 
    if pattern_vars p != acc then raise (Failure "patterns_vars: all patterns does not have the same list of names");
    acc
  ) (pattern_vars (List.hd ps)) (List.tl ps)

(* the set of bounded variable in a term NB: does not take into account vars in type annotation *)
let rec bv_term (te: term) : IndexSet.t =
  match te with
    | Universe _ | Cste _ | AVar _ | TName _ -> IndexSet.empty
    | Var (i, _, _) when i < 0 -> IndexSet.empty
    | Var (i, _, _) when i >= 0 -> IndexSet.singleton i
    | Lambda ((_, ty, _, _), te, _, _) ->
      IndexSet.union (bv_term ty) (shift_vars (bv_term te) (-1))
    | Forall ((_, ty, _, _), te, _, _) ->
      IndexSet.union (bv_term ty) (shift_vars (bv_term te) (-1))
    | Let ((_, te1, _), te2, _, _) ->
      IndexSet.union (bv_term te1) (shift_vars (bv_term te2) (-1))
    | App (te, args, _, _) -> List.fold_left (fun acc (te, _) -> IndexSet.union acc (bv_term te)) (bv_term te) args
    | Match (te, des, _, _) ->
      List.fold_left (fun acc eq -> IndexSet.union acc (des_equation eq)) (bv_term te) des

and des_equation (des: (pattern list * term)) : IndexSet.t =
    (shift_vars (bv_term (snd des)) (patterns_size (fst des)))


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
    | Cste (p, n, ty, pos) -> pos
    | Var (i, ty, pos) -> pos
    | AVar (ty, pos) -> pos
    | TName (n, ty, pos) -> pos
    | Lambda (q, te, ty, pos) -> pos
    | Forall (q, te, ty, pos) -> pos
    | Let (q, te, ty, pos) -> pos
    | App (f, args, ty, pos) -> pos
    | Match (te, des, ty, pos) -> pos

let set_term_pos (te: term) (pos: position) : term =
  match te with
    | Universe (ty, lvl, _) ->
      Universe (ty, lvl, pos)
    | Cste (p, n, ty, _) ->
      Cste (p, n, ty, pos)
    | Var (i, ty, _) ->
      Var (i, ty, pos)
    | AVar (ty, _) ->
      AVar (ty, pos)
    | TName (n, ty, _) ->
      TName (n, ty, pos)
    | Lambda (q, te, ty, _) ->
      Lambda (q, te, ty, pos)
    | Forall (q, te, ty, _) ->
      Forall (q, te, ty, pos)
    | Let (q, te, ty, _) ->
      Let (q, te, ty, pos)
    | App (f, args, ty, _) ->
      App (f, args, ty, pos)
    | Match (te, des, ty, _) ->
      Match (te, des, ty, pos)

  
(* build an implication: no shifting in types !!! (used by the parser) *)
let build_impl (symbols: (name * pos) list) (ty: term) (nature: nature) (body: term) : term =
  List.fold_right (fun (s, pos) acc -> 
    Forall (
      (s, ty, nature, Position (pos, [])), 
      acc, 
      NoAnnotation,
      Position ((fst pos, snd (pos_from_position (get_term_pos acc))), [])
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
      Position ((fst pos, snd (pos_from_position (get_term_pos acc))), [])
    )
  )symbols body


(* build a Lambda: no shifting in types !!! (used by the parser) *)
let build_lambdas (qs: ((name * pos) list * term * nature) list) (body: term) : term =
  List.fold_right (fun (s, ty, n) acc -> build_lambda s ty n acc) qs body
