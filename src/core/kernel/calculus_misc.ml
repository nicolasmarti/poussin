open Calculus_def
open Extlist

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



(* function to get term position *)
let get_term_position (te: term) : position =
  raise (Failure "get_term_position: NYI")

(* functions to get/set term annotation *)
let get_term_annotation (te: term) : typeannotation =
  raise (Failure "get_term_annotation: NYI")

let set_term_annotation (te: term) (ty: term) : term =
  raise (Failure "set_term_annotation: NYI")

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


(* this is the strict equality modulo position/app/... *)
let rec eq_term (te1: term) (te2: term) : bool =
  raise (Failure "eq_term: NYI")

(* retrieve the debruijn index of a bound var through its name *)
let var_name_index (ctxt: context) (name: name) : index =
  raise (Failure "var_name_index")

(* grab the type of a bound var *)
let bvar_type (ctxt: context) (i: index) : term =
  raise (Failure "bvar_type")

(* grab the value of a free var *)
let fvar_value (ctxt: context) (i: index) : term =
  raise (Failure "fvar_lookup")

(* pushing and poping terms in the term stack 
   N.B.: with side effect
*)
let push_terms (ctxt: context ref) (tes: term list) : unit =
  let (hd::tl) = !ctxt in
  ctxt := ({hd with termstack = tes @ hd.termstack})::tl

let pop_terms (ctxt: context ref) (sz: int) : term list =
  let (hd::tl) = !ctxt in  
  ctxt := ({hd with termstack = drop sz hd.termstack})::tl;
  take sz hd.termstack

(* pushing and poping natures in the nature stack 
   N.B.: with side effect
*)
let push_nature (ctxt: context ref) (n: nature) : unit =
  let (hd::tl) = !ctxt in
  ctxt := ({hd with naturestack = n :: hd.naturestack})::tl

let pop_nature (ctxt: context ref) : nature =
    let (hd::tl) = !ctxt in  
    ctxt := ({hd with naturestack = List.tl hd.naturestack})::tl;
    List.hd hd.naturestack

(* returns only the elements that are explicit *)
let filter_explicit (l: ('a * nature) list) : 'a list =
  List.map fst (List.filter (fun (_, n) -> n = Explicit) l)
