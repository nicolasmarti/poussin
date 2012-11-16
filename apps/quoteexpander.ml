open Libparser
open Parser

let parse_type_term str =
  let lines = stream_of_string str in
  let pb = build_parserbuffer lines in
  Hashtbl.clear term_hash;
  try 
    let t = Lazy.force (parse_term (get_defs ()) (-1, -1) pb) in
    from_ground_term t    
  with
    | NoMatch -> 
      let str = String.concat "" ["parsing error: "; (errors2string pb)] in
      printf "%s\n" str;
      raise (failwith "")
    | PoussinException err ->
      let str = String.concat "" ["poussin error: "; (poussin_error2string err)] in      
      printf "%s\n" str;
      raise (failwith "")
;;

let parse_formula str =
  let lines = stream_of_string str in
  let pb = build_parserbuffer lines in
  Hashtbl.clear term_hash;
  try 
    let t = Lazy.force (parse_term (get_defs ()) (-1, -1) pb) in
    formula_from_term t    
  with
    | NoMatch -> 
      let str = String.concat "" ["parsing error: "; (errors2string pb)] in
      printf "%s\n" str;
      raise (failwith "")
    | PoussinException err ->
      let str = String.concat "" ["poussin error: "; (poussin_error2string err)] in      
      printf "%s\n" str;
      raise (failwith "")
;;


(* from term to pattern *)
let fresh_names : (name, int) Hashtbl.t = Hashtbl.create 100;;

let rec get_fresh_name n : string =
  try 
    let i = Hashtbl.find fresh_names n in
    Hashtbl.replace fresh_names n (i+1);
    String.concat "" [n; string_of_int i]
  with
    | _ ->
      Hashtbl.add fresh_names n 0;
      n

let equality_conditions: (name * name) list ref = ref [];;

let rec in_list (l: 'a list) (x: 'a) : int option =
  match l with
    | [] -> None
    | hd::tl ->
      match in_list tl x with
	| None -> None
	| Some i -> Some (i+1)
;;

let rec term2pattern_loop (defs: defs) (ctxt: context ref) (vars: name list) (te: term) : string =
  let res = match te.ast with
    | Universe (Type, _) -> "{ ast = Universe (Type, _); _ }"
    | Universe (Set, _) -> "{ ast = Universe (Set, _); _ }"
    | Universe (Prop, _) -> "{ ast = Universe (Prop, _); _ }"

    | AVar -> "{ ast = AVar; _ }"

    (* case when it is a quantified var *)
    | TName n -> (
      match in_list vars n with
	| Some i ->
	  String.concat "" ["{ ast = Var "; string_of_int i; "; _}"]
	| None -> 
	  if Hashtbl.mem defs n then
	    String.concat "" ["{ ast = Cste \""; n; "\"; _}"]
	  else (
	    (*
	    let n' = get_fresh_name n in
	    equality_conditions := (n, n')::!equality_conditions;*)
	    String.concat "" ["{ ast = TName "; n; "; _}"]
	  )
    )

    | Cste c ->
      String.concat "" ["{ ast = Cste \""; c; "\"; _}"]

    | Var i when i >= 0 ->
      String.concat "" ["{ ast = Var "; string_of_int i; "; _}"]

    | Var i when i < 0 -> (
      match fvar_name ctxt i with
	| None ->
	  String.concat "" ["{ ast = _; _}"]
	| Some n ->
	  n
    )
    | Lambda ((name, ty, nature), body) ->
      (*
      let name' = get_fresh_name name in
      *)
      let nature' = nature2string nature in
      let body' = term2pattern_loop defs ctxt (name::vars) body in
      String.concat "" ["{ ast = Lambda (("; name; ", _,"; nature'; "), "; body';"); _}"]

    | Forall ((name, ty, nature), body) ->
      (*
      let name' = get_fresh_name name in
      *)
      let nature' = nature2string nature in
      let body' = term2pattern_loop defs ctxt (name::vars) body in
      String.concat "" ["{ ast = Forall (("; name; ", _,"; nature'; "), "; body';"); _}"]

    | App (f, args) ->
      String.concat "" 
	["{ ast = App (";
	 term2pattern_loop defs ctxt vars f;
	 ", [";
	 String.concat "; " (List.map (fun (arg, n) -> String.concat "" ["("; 
									 term2pattern_loop defs ctxt vars arg;
									 ", ";
									 nature2string n;
									 ")"
									]) args);
	 "]); _ }"
	] 

    | _ -> raise (failwith (term2string ctxt te))
  in
  res
and nature2string (n: nature) : string =
  match n with
    | Explicit -> "Explicit"
    | Implicit -> "Implicit"
    | NJoker -> "_"
;;

let term2pattern str =
  (*printf "str :=: %s\n" str; flush stdout;*)
  let lines = stream_of_string str in
  let pb = build_parserbuffer lines in
  Hashtbl.clear term_hash;
  try 
    let ctxt = ref empty_context in
    (* parse *)
    let te = Lazy.force (parse_term (get_defs ()) (-1, -1) pb) in
    (* type *)
    let te = typeinfer (get_defs ()) ctxt te in
    (* rewrite free vars as much as possible *)
    let s = context2subst ctxt in
    let te = term_substitution s te in
    Hashtbl.clear fresh_names;
    (*
    equality_conditions := [];
    *)
    let res = term2pattern_loop (get_defs ()) ctxt [] te in    
    (*
    let res = if false && List.length !equality_conditions > 0 then
	String.concat "" ([res; " when "; String.concat " && " (List.map (fun (n1, n2) -> String.concat "" ["String.compare "; n1; " "; n2; " = 0"]) !equality_conditions)]) else res in
    *)
    (*printf "pattern: %s\n" res; flush stdout;*)
    res

  with
    | NoMatch -> 
      let str = String.concat "" ["parsing error: "; (errors2string pb)] in
      printf "%s\n" str;
      raise (failwith "")
    | PoussinException err ->
      let str = String.concat "" ["poussin error: "; (poussin_error2string err)] in      
      printf "%s\n" str;
      raise (failwith "")
;;

open Calculus_kernel;;

let parse_process_definition str =
  Hashtbl.clear term_hash;
  let lines = stream_of_string str in
  let pb = build_parserbuffer lines in
  global_parserbuffer := pb;
  let leftmost = cur_pos pb in
  try 
    ignore (
      let _ = many (fun pb -> 
	Lazy.force (parse_definition2 (get_defs ()) leftmost pb);
	Lazy.lazy_from_val ()
      ) pb in
      let _ = eos pb in
      ()
    )
  with
    | NoMatch -> 
      printf "parsing error: '%s'\n%s\n" (Buffer.contents pb.bufferstr) (errors2string pb); flush Pervasives.stdout;
      raise Pervasives.Exit
    | Failure s -> 
      printf "error:\n%s\n" s;
      raise Pervasives.Exit
    | PoussinException err ->
      (*pp_option := {!pp_option with show_type = true};*)
      printf "poussin_error:\n%s\n%s\n" (trace2string !trace) (poussin_error2string err);
      raise Pervasives.Exit
;;

let quotexpander_def s =
  "parse_process_definition \""^(String.escaped s)^"\""

let quotexpander_term s =
  "parse_type_term \""^(String.escaped s)^"\"";;

let quotexpander_formula s =
  "parse_formula \""^(String.escaped s)^"\"";;

Quotation.add "term" (Quotation.ExStr (fun x -> 
  if x then
    quotexpander_term
  else 
    failwith ":term only for typed term"
))
;;

Quotation.add "pat" (Quotation.ExStr (fun x -> 
  if x then
    failwith ":pat only for typed term"
  else 
    term2pattern
))
;;

Quotation.add "def" (Quotation.ExStr (fun x -> 
  if x then
    quotexpander_def
  else 
    raise (failwith "no pattern mode for defs")
))
;;

Quotation.add "formula" (Quotation.ExStr (fun x -> 
  if x then
    quotexpander_formula
  else 
    raise (failwith "no pattern mode for formula")
))
;;


