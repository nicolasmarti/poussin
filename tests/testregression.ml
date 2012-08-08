open Printf
open Libpprinter
open Libparser

open Calculus_def
open Calculus_misc
open Calculus_substitution
open Calculus_reduction
open Calculus_typecheck

open Calculus_pprinter
open Calculus_parser

let () = printf "calculus regression tests\n";;

let ctxt = ref empty_context;;

let te1 : term = lambda_ "x" (var_ (-1));;
printf "%s\n" (term2string ctxt te1);;

let te2 : term = forall_ "x" ~ty:(type_ (UName "")) (forall_ "x" ~ty:(var_ 0) (var_ 0));;
printf "%s\n" (term2string ctxt te2);;

let parse_definition_from_string (str: string) : definition  =
  let lines = stream_of_string str in
  let pb = build_parserbuffer lines in
  let leftmost = cur_pos pb in
  try 
    let result = parse_definition (Hashtbl.create 100) leftmost pb in
    result
  with
    | NoMatch -> 
      printf "parsing error: '%s'\n%s\n" (Buffer.contents pb.bufferstr) (errors2string pb); flush Pervasives.stdout;
      raise Pervasives.Exit
    | Failure s -> 
      printf "error:\n%s\n" s;
      raise Pervasives.Exit
;;

let defs = ["Inductive True : Prop";
	    "Constructor I: True";
	    "Inductive False : Prop";
	    "Inductive Not (P: Prop) : Prop";
	    "Constructor Contradiction  {P}: (P -> False) -> Not P";
	    "Inductive And (A B: Prop) : Prop";
	    "Constructor conj {A} {B}: A -> B -> And A B";
	    "Inductive Or (A B: Prop) : Prop";
	    "Constructor left {A} {B}: A -> Or A B";
	    "Constructor right {A} {B}: B -> Or A B";
	    "Inductive eq {A: Set} (a: A): A -> Prop";
	    "Constructor eq_refl {A} a: eq a a";
	    "Definition Relation (A: Set) : Type := A -> A -> Prop";
	    "Inductive ReflexiveRel : Set";
	    "Constructor build_ReflexiveRel: (A: Set) -> (rel: Relation A) -> (refl: (x: A) -> rel x x) -> ReflexiveRel";
	    "Definition ReflexiveRel_t {rel: ReflexiveRel} : Set :=  match rel with | build_ReflexiveRel A _ _ := A end";
	   ] in List.map (fun def -> let def = parse_definition_from_string def in
				     printf "%s\n" (definition2string def ctxt)) defs;;

let defs = Hashtbl.create 100;;

let parse_and_typecheck_from_string (str: string) : unit  =
  let lines = stream_of_string str in
  let pb = build_parserbuffer lines in
  let leftmost = cur_pos pb in
  try 
    let result = parse_definition (Hashtbl.create 100) leftmost pb in
    let ctxt = ref empty_context in
    match result with
      | DefInductive (n, ty) -> 
	let ty = typeinfer defs ctxt ty in
	let [ty] = flush_fvars defs ctxt [ty] in 
	Hashtbl.add defs n (Inductive ([], ty));
	printf "%s: %s\n" n (term2string ctxt ty)
      | DefConstructor (n, ty) -> 
	let ty = typeinfer defs ctxt ty in
	let [ty] = flush_fvars defs ctxt [ty] in 
	Hashtbl.add defs n (Constructor ty);
	printf "%s: %s\n" n (term2string ctxt ty)
      | _ -> raise (Failure "parse_and_typecheck_from_string: NYI")

  with
    | NoMatch -> 
      printf "parsing error: '%s'\n%s\n" (Buffer.contents pb.bufferstr) (errors2string pb); flush Pervasives.stdout;
      raise Pervasives.Exit
    | Failure s -> 
      printf "error:\n%s\n" s;
      raise Pervasives.Exit
    | PoussinException err ->
      printf "poussin_error:\n%s\n" (poussin_error2string err);
      raise Pervasives.Exit
;;

let defs = ["Inductive True : Prop";
	    "Constructor I: True";
	    "Inductive False : Prop";
	    "Inductive Not (P: Prop) : Prop";
	    "Constructor Contradiction  {P}: (P -> False) -> Not P";
	    "Inductive And (A B: Prop) : Prop";
	    "Constructor conj {A} {B}: A -> B -> And A B";
	    "Inductive Or (A B: Prop) : Prop";
	    "Constructor left {A} {B}: A -> Or A B";
	    "Constructor right {A} {B}: B -> Or A B";
	    "Inductive eq {A: Set} (a: A): A -> Prop";
	    "Constructor eq_refl {A} (a: A): eq a a";
	    "Inductive ReflexiveRel : Set";
	    "Constructor build_ReflexiveRel: (A: Set) -> (rel: A -> A -> Prop) -> (refl: (x: A) -> rel x x) -> ReflexiveRel"
	   ] in List.map (fun def -> parse_and_typecheck_from_string def) defs;;
