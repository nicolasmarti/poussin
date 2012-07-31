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

let cste_ ?(annot: typeannotation = NoAnnotation) ?(pos: position = NoPosition) ?(path: path = []) (name: name) =
  Cste(path, name, annot, pos)

let var_ ?(annot: typeannotation = NoAnnotation) ?(pos: position = NoPosition) (idx: index) =
  Var(idx, annot, pos)

let avar_ ?(annot: typeannotation = NoAnnotation) ?(pos: position = NoPosition) () =
  AVar(annot, pos)

let name_ ?(annot: typeannotation = NoAnnotation) ?(pos: position = NoPosition) (name: name) =
  TName(name, annot, pos)

let lambda_ ?(annot: typeannotation = NoAnnotation) ?(posq: position = NoPosition) ?(posl: position = NoPosition) (name: name) ?(nature: nature = Explicit) ?(ty: term = avar_ ()) (body: term) =
  Quantifier(Lambda(name, ty, nature, posl), body, annot, posl)


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

