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

let rec construct_lambda (qs: ((name * term * nature * position) * typeannotation * position) list) (body: term) : term =
  match qs with
    | [] -> body
    | (hd, annot, pos) :: tl -> Lambda (hd, construct_lambda tl body, annot, pos, false)

(* functions to get/set term annotation *)
let get_term_annotation (te: term) : typeannotation =
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

let set_term_annotation (te: term) (ty: term) : term =
  match te with
    | Universe (ty, lvl, pos) -> 
      Universe (ty, lvl, pos)
    | Cste (n, _, pos, reduced) ->
      Cste (n, Annotation ty, pos, reduced)
    | Var (i, _, pos) ->
      Var (i, Annotation ty, pos)
    | AVar (_, pos) ->
      AVar (Annotation ty, pos)
    | TName (n, _, pos) ->
      TName (n, Annotation ty, pos)
    | Lambda (q, te, _, pos, reduced) ->
      Lambda (q, te, Annotation ty, pos, reduced)
    | Forall (q, te, _, pos, reduced) ->
      Forall (q, te, Annotation ty, pos, reduced)
    | Let (q, te, _, pos, reduced) ->
      Let (q, te, Annotation ty, pos, reduced)
    | App (f, args, _, pos, reduced) ->
      App (f, args, Annotation ty, pos, reduced)
    | Match (te, des, _, pos, reduced) ->
      Match (te, des, Annotation ty, pos, reduced)

let set_term_tannotation (te: term) (ty: term) : term =
  match te with
    | Universe (ty, lvl, pos) -> 
      Universe (ty, lvl, pos)
    | Cste (n, _, pos, reduced) ->
      Cste (n, TypedAnnotation ty, pos, reduced)
    | Var (i, _, pos) ->
      Var (i, TypedAnnotation ty, pos)
    | AVar (_, pos) ->
      AVar (TypedAnnotation ty, pos)
    | TName (n, _, pos) ->
      TName (n, TypedAnnotation ty, pos)
    | Lambda (q, te, _, pos, reduced) ->
      Lambda (q, te, TypedAnnotation ty, pos, reduced)
    | Forall (q, te, _, pos, reduced) ->
      Forall (q, te, TypedAnnotation ty, pos, reduced)
    | Let (q, te, _, pos, reduced) ->
      Let (q, te, TypedAnnotation ty, pos, reduced)
    | App (f, args, _, pos, reduced) ->
      App (f, args, TypedAnnotation ty, pos, reduced)
    | Match (te, des, _, pos, reduced) ->
      Match (te, des, TypedAnnotation ty, pos, reduced)

let set_term_type (te: term) (ty: term) : term =
  match te with
    | Universe (ty, lvl, pos) -> 
      Universe (ty, lvl, pos)
    | Cste (n, _, pos, reduced) ->
      Cste (n, Typed ty, pos, reduced)
    | Var (i, _, pos) ->
      Var (i, Typed ty, pos)
    | AVar (_, pos) ->
      AVar (Typed ty, pos)
    | TName (n, _, pos) ->
      TName (n, Typed ty, pos)
    | Lambda (q, te, _, pos, reduced) ->
      Lambda (q, te, Typed ty, pos, reduced)
    | Forall (q, te, _, pos, reduced) ->
      Forall (q, te, Typed ty, pos, reduced)
    | Let (q, te, _, pos, reduced) ->
      Let (q, te, Typed ty, pos, reduced)
    | App (f, args, _, pos, reduced) ->
      App (f, args, Typed ty, pos, reduced)
    | Match (te, des, _, pos, reduced) ->
      Match (te, des, Typed ty, pos, reduced)

let set_term_noannotation (te: term) : term =
  match te with
    | Universe (ty, lvl, pos) -> 
      Universe (ty, lvl, pos)
    | Cste (n, _, pos, reduced) ->
      Cste (n, NoAnnotation, pos, reduced)
    | Var (i, _, pos) ->
      Var (i, NoAnnotation, pos)
    | AVar (_, pos) ->
      AVar (NoAnnotation, pos)
    | TName (n, _, pos) ->
      TName (n, NoAnnotation, pos)
    | Lambda (q, te, _, pos, reduced) ->
      Lambda (q, te, NoAnnotation, pos, reduced)
    | Forall (q, te, _, pos, reduced) ->
      Forall (q, te, NoAnnotation, pos, reduced)
    | Let (q, te, _, pos, reduced) ->
      Let (q, te, NoAnnotation, pos, reduced)
    | App (f, args, _, pos, reduced) ->
      App (f, args, NoAnnotation, pos, reduced)
    | Match (te, des, _, pos, reduced) ->
      Match (te, des, NoAnnotation, pos, reduced)


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
let is_reduced (te: term) : reduced =
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
let set_reduced (te: term) : term =
  match te with
    | _ when is_reduced te -> te

    | Universe _ | Var _ | AVar _ | TName _ -> te
    | Cste (n, ty, pos, _) -> Cste (n, ty, pos, true)
    | Lambda (q, te, ty, pos, reduced) -> Lambda (q, te, ty, pos, true)
    | Forall (q, te, ty, pos, reduced) -> Forall (q, te, ty, pos, true)
    | Let (q, te, ty, pos, reduced) -> Let (q, te, ty, pos, true)
    | App (f, args, ty, pos, reduced) -> App (f, args, ty, pos, true)
    | Match (te, des, ty, pos, reduced) -> Match (te, des, ty, pos, true)

(* get the typeannotation of a typed term *)
let get_type (te: term) : term =
  match te with
    | Universe (ty, lvl, pos) -> Universe (Type, USucc lvl, pos)
    | _ -> let Typed ty = get_term_annotation te in ty

(* an empty context *)
let empty_context = {
  bvs = [];
  fvs = []::[];
  conversion_hyps = []::[];
  lvl_cste = [];
}
    
