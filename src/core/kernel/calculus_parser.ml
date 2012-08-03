open Calculus_def
open Calculus_misc

open Extlist
open Libparser

open Str
open Printf

let at_start_pos (startp: (int * int)) (p: 'a parsingrule) : 'a parsingrule =
  fun pb ->
    let curp = cur_pos pb in
    if (snd startp > snd curp) then (
      (*printf "%d > %d\n" (snd startp) (snd curp);*)
      raise NoMatch
    );
    p pb

let after_start_pos (startp: (int * int)) (p: 'a parsingrule) : 'a parsingrule =
  fun pb ->
    let curp = cur_pos pb in
    if (snd startp >= snd curp) then (
      (*printf "%d >= %d\n" (snd startp) (snd curp);*)
      raise NoMatch
    );
    p pb

let with_pos (p: 'a parsingrule) : ('a * pos) parsingrule =
  fun pb ->
    let startp = cur_pos pb in
    let res = p pb in
    let endp = cur_pos pb in
    (res, (startp, endp))

let keywords = ["Type"; "Set"; "Prop"; ":"; ":="; "->"; "match"; "with"; "end"; "Definition"; "Inductive"; "Constructor"; "Definition"]

let parse_reserved : unit parsingrule =
  foldp (List.map (fun x -> keyword x ()) keywords)

let name_parser : name parsingrule = applylexingrule (regexp "[a-zA-Z][_a-zA-Z0-9]*", 
						      fun (s:string) -> 
							if List.mem s keywords then raise NoMatch else s
)

let parse_avar : unit parsingrule = applylexingrule (regexp "_", 
						     fun (s:string) -> ()
)

(* these are the whole term set 
   - term_lvlx "->" term
*)
let rec parse_term (defs: defs) (leftmost: (int * int)) (pb: parserbuffer) : term = begin
  (* parsing a forall *)
  tryrule (fun pb ->
    let () = whitespaces pb in
    let startpos = cur_pos pb in
    let (names, ty, nature) = parse_impl_lhs defs leftmost pb in
    let () = whitespaces pb in
    let () = at_start_pos leftmost (word "->") pb in
    let () = whitespaces pb in
    let body = parse_term defs leftmost pb in
    let endpos = cur_pos pb in
    let () = whitespaces pb in
    set_term_pos (build_impl names ty nature body) (pos_to_position (startpos, endpos))
  ) 
  (* parsing a lambda *)
  <|> tryrule (fun pb ->
    let () = whitespaces pb in
    let startpos = cur_pos pb in
    let () = at_start_pos leftmost (word "\\") pb in
    let () = whitespaces pb in
    let qs = many1 (parse_lambda_lhs defs leftmost) pb in
    let () = whitespaces pb in
    let () = at_start_pos leftmost (word "->") pb in
    let () = whitespaces pb in
    let body = parse_term defs leftmost pb in
    let endpos = cur_pos pb in
    let () = whitespaces pb in
    set_term_pos (build_lambdas qs body) (pos_to_position (startpos, endpos))
  ) 
  <|> parse_term_lvl0 defs leftmost
end pb

and parse_impl_lhs (defs: defs) (leftmost: (int * int)) (pb: parserbuffer) : ((name * pos) list * term * nature) = begin
  (* first case 
     with paren
  *)
  tryrule (paren (fun pb ->
    let names = many1 (fun pb ->
      let () = whitespaces pb in
      let startpos = cur_pos pb in
      let n = at_start_pos leftmost name_parser pb in
      let endpos = cur_pos pb in
      let () = whitespaces pb in
      n, (startpos, endpos)
    ) pb in
    let () = whitespaces pb in
    let () = at_start_pos leftmost (word ":") pb in
    let () = whitespaces pb in
    let ty = parse_term defs leftmost pb in
    (List.map (fun (n, p) -> n, p) names, ty, Explicit)
   )
  )
  (* or the same but with bracket *)
  <|> tryrule (bracket (fun pb ->
    let names = many1 (fun pb ->
    let () = whitespaces pb in
    let startpos = cur_pos pb in
    let n = at_start_pos leftmost name_parser pb in
    let endpos = cur_pos pb in
    let () = whitespaces pb in
    n, (startpos, endpos)
    ) pb in
    let () = whitespaces pb in
    let () = at_start_pos leftmost (word ":") pb in
    let () = whitespaces pb in
    let ty = parse_term defs leftmost pb in
    (List.map (fun (n, p) -> n, p) names, ty, Implicit)
  )
  )
  (* or just a type -> anonymous arguments *)
  <|> (fun pb -> 
    let ty = parse_term_lvl0 defs leftmost pb in
    (["_", nopos], ty, Explicit)        
  )
  <|> (fun pb -> 
    let () = whitespaces pb in
    let ty = at_start_pos leftmost (paren (parse_term_lvl0 defs leftmost)) pb in
    (["_", nopos], ty, Explicit)        
  )
  <|> (fun pb -> 
    let () = whitespaces pb in
    let ty = at_start_pos leftmost (bracket (parse_term_lvl0 defs leftmost)) pb in
    (["_", nopos], ty, Implicit)        
  )
end pb

and parse_lambda_lhs (defs: defs) (leftmost: (int * int)) (pb: parserbuffer) : ((name * pos) list * term * nature) = begin
  (* first case 
     with paren
  *)
  tryrule (paren (fun pb ->
    let names = many1 (fun pb ->
      let () = whitespaces pb in
      let startpos = cur_pos pb in
      let n = at_start_pos leftmost name_parser pb in
      let endpos = cur_pos pb in
      let () = whitespaces pb in
      n, (startpos, endpos)
    ) pb in
    let () = whitespaces pb in
    let () = at_start_pos leftmost (word ":") pb in
    let () = whitespaces pb in
    let ty = parse_term defs leftmost pb in
    (List.map (fun (n, p) -> n, p) names, ty, Explicit)
   )
  )
  (* or the same but with bracket *)
  <|> tryrule (bracket (fun pb ->
    let names = many1 (fun pb ->
    let () = whitespaces pb in
    let startpos = cur_pos pb in
    let n = at_start_pos leftmost name_parser pb in
    let endpos = cur_pos pb in
    let () = whitespaces pb in
    n, (startpos, endpos)
    ) pb in
    let ty = match (mayberule (fun pb ->
      let () = whitespaces pb in
      let () = at_start_pos leftmost (word ":") pb in
      let () = whitespaces pb in
      let ty = parse_term defs leftmost pb in
      ty
    ) pb) with
      | None -> AVar (NoAnnotation, NoPosition)
      | Some ty -> ty in
    (List.map (fun (n, p) -> n, p) names, ty, Implicit)
  )
  )
  <|> (fun pb -> 
    let () = whitespaces pb in
    let startpos = cur_pos pb in
    let n = at_start_pos leftmost name_parser pb in
    let endpos = cur_pos pb in
    let () = whitespaces pb in
    ([n, (startpos, endpos)], AVar (NoAnnotation, NoPosition), Explicit)        
  )

end pb

(* this is term resulting for the application of term_lvl2 *)
and parse_term_lvl0 (defs: defs) (leftmost: (int * int)) (pb: parserbuffer) : term = begin
  fun pb -> 
    (* first we parse the application head *)
    let startpos = cur_pos pb in
    let head = parse_term_lvl1 defs leftmost pb in    
    let () = whitespaces pb in
    (* then we parse the arguments *)
    let args = many (
      fun pb ->
	parse_arguments defs leftmost pb
    ) pb in
    let endpos = cur_pos pb in
    match args with
      | [] -> head
      | _ -> 
	App (head, args, NoAnnotation, Position ((startpos, endpos), []))
end pb

(* arguments: term_lvl2 with possibly brackets *)
and parse_arguments (defs: defs) (leftmost: (int * int)) (pb: parserbuffer) : (term * nature) = begin
  (fun pb -> 
    let () = whitespaces pb in
    let te = at_start_pos leftmost (bracket (parse_term_lvl1 defs leftmost)) pb in
    (te, Implicit)
  )
  <|> (fun pb -> 
    let te = parse_term_lvl1 defs leftmost pb in
    (te, Explicit)
  )
end pb

(* these are the most basic terms + top-level terms in parenthesis *)
and parse_term_lvl1 (defs: defs) (leftmost: (int * int)) (pb: parserbuffer) : term = begin
  tryrule (fun pb -> 
    let () = whitespaces pb in
    let (), pos = at_start_pos leftmost (with_pos (word "Type")) pb in
    let () = whitespaces pb in
    Universe (Type, UName "", pos_to_position pos)
  ) 
  <|> tryrule (fun pb -> 
    let () = whitespaces pb in
    let (), pos = at_start_pos leftmost (with_pos (word "Set")) pb in
    let () = whitespaces pb in
    Universe (Set, UName "", pos_to_position pos)
  ) 
  <|> tryrule (fun pb -> 
    let () = whitespaces pb in
    let (), pos = at_start_pos leftmost (with_pos (word "Prop")) pb in
    let () = whitespaces pb in
    Universe (Prop, UName "", pos_to_position pos)
  ) 
  <|> tryrule (fun pb ->
    let () =  whitespaces pb in
    let (), pos = at_start_pos leftmost (with_pos parse_avar) pb in
    let () =  whitespaces pb in
    AVar (NoAnnotation, pos_to_position pos)
  ) 
  (* parsing of math: TODO extends for having more than one pattern per destructor *)
  <|> tryrule (fun pb ->
    let () =  whitespaces pb in
    let startpos = cur_pos pb in    
    let () = at_start_pos leftmost (word "match") pb in
    let () =  whitespaces pb in
    let te = parse_term defs leftmost pb in
    let () =  whitespaces pb in
    let () = at_start_pos leftmost (word "with") pb in
    let eqs = many (fun pb ->
      let () = whitespaces pb in
      let () = at_start_pos leftmost (word "|") pb in
      let () = whitespaces pb in
      let p = at_start_pos leftmost (parse_pattern defs leftmost) pb in
      let () = whitespaces pb in
      let () = at_start_pos leftmost (word ":=") pb in
      let startpos = cur_pos pb in
      let () = whitespaces pb in
      let te = parse_term defs startpos pb in
      (p::[]), te
    ) pb in
    let () =  whitespaces pb in
    let () = at_start_pos leftmost (word "end") pb in
    let endpos = cur_pos pb in    
    Match (te, eqs, NoAnnotation, pos_to_position (startpos, endpos))
  )
  <|> tryrule (fun pb ->
    let () = whitespaces pb in
    let n, pos = at_start_pos leftmost (with_pos name_parser) pb in
    let () = whitespaces pb in
    TName (n, NoAnnotation, pos_to_position pos)
  )
  <|> (fun pb -> 
    let () = whitespaces pb in
    at_start_pos leftmost (paren (parse_term defs leftmost)) pb)
end pb

and parse_pattern (defs: defs) (leftmost: (int * int)) (pb: parserbuffer) : pattern = begin
  tryrule (fun pb -> 
    (* first we parse the application head *)
    let () = whitespaces pb in
    let s, pos = at_start_pos leftmost (with_pos name_parser) pb in    
    let () = whitespaces pb in
    (* then we parse the arguments *)
    let args = List.flatten (
      many (
	fun pb ->
	  parse_pattern_arguments defs leftmost pb
      ) pb) in
    PCstor (s, args)	  
  )
  <|> tryrule (parse_pattern_lvl1 defs leftmost)
end pb


and parse_pattern_arguments (defs: defs) (leftmost: (int * int)) (pb: parserbuffer) : (pattern * nature) list = begin
  tryrule (paren (fun pb ->
    let patterns = many1 (fun pb ->
      let () = whitespaces pb in
      let n = parse_pattern_lvl1 defs leftmost pb in
      let () = whitespaces pb in
      n
    ) pb in
    List.map (fun p -> p, Explicit) patterns
  )
  )
  (* or the same but with bracket *)
  <|> tryrule (bracket (fun pb ->
    let patterns = many1 (fun pb ->
    let () = whitespaces pb in
    let n =  parse_pattern_lvl1 defs leftmost pb in
    let () = whitespaces pb in
    n
    ) pb in
    List.map (fun p -> p, Implicit) patterns
  )
  )
  <|>(fun pb -> 
    let () = whitespaces pb in
    let te = at_start_pos leftmost (bracket (parse_pattern defs leftmost)) pb in
    [te, Implicit]
  )
  <|>(fun pb -> 
    let () = whitespaces pb in
    let te = at_start_pos leftmost (paren (parse_pattern defs leftmost)) pb in
    [te, Explicit]
  )
  <|> (fun pb -> 
    let te = parse_pattern_lvl1 defs leftmost pb in
    [te, Explicit]
  )
end pb
  
and parse_pattern_lvl1 (defs: defs) (leftmost: (int * int)) (pb: parserbuffer) : pattern = begin
  tryrule (fun pb ->
    let () =  whitespaces pb in
    let () = at_start_pos leftmost parse_avar pb in
    let () =  whitespaces pb in
    PAvar 
  ) 
  <|> tryrule (fun pb -> 
    let () =  whitespaces pb in
    let name = at_start_pos leftmost name_parser pb in
    let () =  whitespaces pb in    
    PName name
  )
  <|> tryrule (fun pb ->
    let () =  whitespaces pb in    
    at_start_pos leftmost (paren (parse_pattern defs leftmost)) pb    
  )
end pb

type definition = DefSignature of name * term
		  | DefDefinition of name * term
		  | DefInductive of name * term
		  | DefConstructor of name * term


let rec parse_definition (defs: defs) (leftmost: int * int) : definition parsingrule =
  (* an inductive *)
  tryrule (fun pb ->
    let () = whitespaces pb in
    let _ = at_start_pos leftmost (word "Inductive") pb in
    let () = whitespaces pb in
    let s = at_start_pos leftmost name_parser pb in
    let () = whitespaces pb in
    let qs = many (parse_lambda_lhs defs leftmost) pb in
    let () = whitespaces pb in
    let () = at_start_pos leftmost (word ":") pb in
    let startpos = cur_pos pb in
    let () = whitespaces pb in
    let ty = parse_term defs startpos pb in
    let endpos = cur_pos pb in
    DefInductive (s, set_term_pos (build_impls qs ty) (pos_to_position (startpos, endpos)))
  )
  (* a constructor *)
  <|> tryrule (fun pb ->
    let () = whitespaces pb in
    let _ = at_start_pos leftmost (word "Constructor") pb in
    let () = whitespaces pb in
    let s = at_start_pos leftmost name_parser pb in
    let () = whitespaces pb in
    let qs = many (parse_lambda_lhs defs leftmost) pb in
    let () = whitespaces pb in
    let () = at_start_pos leftmost (word ":") pb in
    let startpos = cur_pos pb in
    let () = whitespaces pb in
    let ty = parse_term defs startpos pb in
    let endpos = cur_pos pb in
    DefConstructor (s, set_term_pos (build_impls qs ty) (pos_to_position (startpos, endpos)))
  )
  (* a signature *)
  <|> tryrule (fun pb ->
    let () = whitespaces pb in
    let _ = at_start_pos leftmost (word "Signature") pb in
    let () = whitespaces pb in
    let s = at_start_pos leftmost name_parser pb in
    let () = whitespaces pb in
    let qs = many (parse_lambda_lhs defs leftmost) pb in
    let () = whitespaces pb in
    let () = at_start_pos leftmost (word ":") pb in
    let startpos = cur_pos pb in
    let () = whitespaces pb in
    let ty = parse_term defs startpos pb in
    let endpos = cur_pos pb in
    DefSignature (s, set_term_pos (build_impls qs ty) (pos_to_position (startpos, endpos)))
  )
  (* a definition *)
  <|> tryrule (fun pb ->
    let () = whitespaces pb in
    let _ = at_start_pos leftmost (word "Definition") pb in
    let () = whitespaces pb in
    let s = at_start_pos leftmost name_parser pb in
    let () = whitespaces pb in
    let qs = many (parse_lambda_lhs defs leftmost) pb in
    let () = whitespaces pb in
    let () = at_start_pos leftmost (word ":") pb in
    let startpos = cur_pos pb in
    let () = whitespaces pb in
    let ty = parse_term defs startpos pb in
    let endpos = cur_pos pb in
    let () = whitespaces pb in
    let () = at_start_pos leftmost (word ":=") pb in
    let startpos2 = cur_pos pb in
    let () = whitespaces pb in
    let te = parse_term defs startpos pb in
    let endpos2 = cur_pos pb in
    DefDefinition (s, 
		  (set_term_annotation 
		     (set_term_pos 
			(build_lambdas qs te) 
			(pos_to_position (startpos2, endpos2))
		     )
		     (set_term_pos 
			(build_impls qs ty) 
			(pos_to_position (startpos, endpos))
		     )
		  )
    )
  )
      
