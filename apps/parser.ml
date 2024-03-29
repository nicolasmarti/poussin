open Calculus_kernel

open Libparser
open Pprinter
open Str
open Printf
open Def

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
    Lazy.lazy_from_fun (fun () -> (Lazy.force res, (startp, endp)))

let int_parser : int parsingrule = applylexingrule_regexp ("[0-9]+", 
							     fun (s:string) -> 
							       Lazy.lazy_from_val (int_of_string s)
)

let keywords = ["Type"; "Set"; "Prop"; ":"; ":="; "->"; "match"; "with"; "end"; "Definition"; "Inductive"; "Constructor"; "Signature"; "Compute"; "let"; "in"; "exact"; "Decreasing"; "Recursive"; "Compute"; "Check"
]

let parse_reserved : unit parsingrule =
  foldp (List.map (fun x -> keyword x ()) keywords)

let name_parser : name parsingrule = applylexingrule_regexp ("[a-zA-Z][_a-zA-Z0-9]*", 
							     fun (s:string) -> 
							       if List.mem s keywords then raise NoMatch else Lazy.lazy_from_val s
)

let parse_avar : unit parsingrule = applylexingrule_string ("_", 
							    fun (s:string) -> Lazy.lazy_from_val ()
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

let term_hash : (int, (term Lazy.t * int)) Hashtbl.t = Hashtbl.create 100

let memo_term (p: term parsingrule) pb : term Lazy.t =
  memoize_parser p term_hash pb


(* these are the whole term set 
   - term_lvlx "->" term
*)
let rec parse_term (defs: defs) (leftmost: (int * int)) (pb: parserbuffer) : term Lazy.t = memo_term begin
  (* parsing a forall *)
  tryrule (fun pb ->
    let _ = whitespaces pb in
    let te = parse_term' defs leftmost pb in
    let _ = whitespaces pb in
    let ty = mayberule (fun pb ->
      let _ = whitespaces pb in
      let _ = at_start_pos leftmost (word ":") pb in
      let _ = whitespaces pb in
      let ty = parse_term defs leftmost pb in
      ty
    ) pb in
    Lazy.lazy_from_fun (fun () ->
      let te = Lazy.force te in
      let ty = Lazy.force ty in
      match ty with
	| None -> te
	| Some ty -> set_term_annotation te ty
    )
  )
end pb

and parse_term' (defs: defs) (leftmost: (int * int)) (pb: parserbuffer) : term Lazy.t = memo_term begin
  (* parsing a forall *)
  tryrule (fun pb ->
    let _ = whitespaces pb in
    let startpos = cur_pos pb in
    let q = parse_impl_lhs defs leftmost pb in
    let _ = whitespaces pb in
    let _ = at_start_pos leftmost (word "->") pb in
    let _ = whitespaces pb in
    let body = parse_term defs leftmost pb in
    let endpos = cur_pos pb in
    let _ = whitespaces pb in
    Lazy.lazy_from_fun (fun () ->
      let (names, ty, nature) = Lazy.force q in
      set_term_pos (build_impl names ty nature (Lazy.force body)) (pos_to_position (startpos, endpos)))
  ) 
  (* parsing a lambda *)
  <|> tryrule (fun pb ->
    let _ = whitespaces pb in
    let startpos = cur_pos pb in
    let _ = at_start_pos leftmost (word "\\") pb in
    let _ = whitespaces pb in
    let qs = many1 (parse_lambda_lhs defs leftmost) pb in
    let _ = whitespaces pb in
    let _ = at_start_pos leftmost (word "->") pb in
    let _ = whitespaces pb in
    let body = parse_term defs leftmost pb in
    let endpos = cur_pos pb in
    let _ = whitespaces pb in
    Lazy.lazy_from_fun (fun () ->
      set_term_pos (build_lambdas (Lazy.force qs) (Lazy.force body)) (pos_to_position (startpos, endpos))
    )
  ) 
  <|> (parse_term_lvl0 defs leftmost)
end pb

and parse_impl_lhs (defs: defs) (leftmost: (int * int)) (pb: parserbuffer) : ((name * pos) list * term * nature) Lazy.t = begin
  (* first case 
     with paren
  *)
  tryrule (paren (fun pb ->
    let names = many1 (fun pb ->
      let _ = whitespaces pb in
      let startpos = cur_pos pb in
      let n = at_start_pos leftmost name_parser pb in
      let endpos = cur_pos pb in
      let _ = whitespaces pb in
      Lazy.lazy_from_fun (fun () ->
	Lazy.force n, (startpos, endpos)
      )
    ) pb in
    let _ = whitespaces pb in
    let _ = at_start_pos leftmost (word ":") pb in
    let _ = whitespaces pb in
    let ty = parse_term defs leftmost pb in
    Lazy.lazy_from_fun (fun () ->
      (List.map (fun (n, p) -> n, p) (Lazy.force names), (Lazy.force ty), Explicit)
    )
   )
  )
  (* or the same but with bracket *)
  <|> tryrule (bracket (fun pb ->
    let names = many1 (fun pb ->
      let _ = whitespaces pb in
      let startpos = cur_pos pb in
      let n = at_start_pos leftmost name_parser pb in
      let endpos = cur_pos pb in
      let _ = whitespaces pb in
      Lazy.lazy_from_fun (fun () ->
	Lazy.force n, (startpos, endpos)
      )
    ) pb in
    let _ = whitespaces pb in
    let _ = at_start_pos leftmost (word ":") pb in
    let _ = whitespaces pb in
    let ty = parse_term defs leftmost pb in
    Lazy.lazy_from_fun (fun () ->
      (List.map (fun (n, p) -> n, p) (Lazy.force names), (Lazy.force ty), Implicit)
    )
   )
  )
  (* or just a type -> anonymous arguments *)
  <|> (fun pb -> 
    let ty = parse_term_lvl0 defs leftmost pb in
    Lazy.lazy_from_fun (fun () -> (["_", nopos], (Lazy.force ty), Explicit))
  )
  <|> (fun pb -> 
    let _ = whitespaces pb in
    let ty = at_start_pos leftmost (paren (parse_term defs leftmost)) pb in
    Lazy.lazy_from_fun (fun () -> (["_", nopos], (Lazy.force ty), Explicit))
  )
  <|> (fun pb -> 
    let _ = whitespaces pb in
    let ty = at_start_pos leftmost (bracket (parse_term defs leftmost)) pb in
    Lazy.lazy_from_fun (fun () -> (["_", nopos], (Lazy.force ty), Implicit))
  )
end pb

and parse_lambda_lhs (defs: defs) (leftmost: (int * int)) (pb: parserbuffer) : ((name * pos) list * term * nature) Lazy.t = begin
  (* first case 
     with paren
  *)
  tryrule (paren (fun pb ->
    let names = many1 (fun pb ->
      let _ = whitespaces pb in
      let startpos = cur_pos pb in
      let n = at_start_pos leftmost name_parser pb in
      let endpos = cur_pos pb in
      let _ = whitespaces pb in
      Lazy.lazy_from_fun (fun () ->
	Lazy.force n, (startpos, endpos)
      )
    ) pb in
    let _ = whitespaces pb in
    let _ = at_start_pos leftmost (word ":") pb in
    let _ = whitespaces pb in
    let ty = parse_term defs leftmost pb in
    Lazy.lazy_from_fun (fun () ->
      (List.map (fun (n, p) -> n, p) (Lazy.force names), (Lazy.force ty), Explicit)
    )
   )
  )
  (* or the same but with bracket *)
  <|> tryrule (bracket (fun pb ->
    let names = many1 (fun pb ->
    let _ = whitespaces pb in
    let startpos = cur_pos pb in
    let n = at_start_pos leftmost name_parser pb in
    let endpos = cur_pos pb in
    let _ = whitespaces pb in
    Lazy.lazy_from_fun (fun () ->
      Lazy.force n, (startpos, endpos)
    )
    ) pb in
    let ty = mayberule (fun pb ->
      let _ = whitespaces pb in
      let _ = at_start_pos leftmost (word ":") pb in
      let _ = whitespaces pb in
      let ty = parse_term defs leftmost pb in
      ty
    ) pb in
    Lazy.lazy_from_fun (fun () ->
      (List.map (fun (n, p) -> n, p) (Lazy.force names), (match Lazy.force ty with | None -> avar_ () | Some ty -> ty), Implicit)
    )
  )
  )
  <|> (fun pb -> 
    let _ = whitespaces pb in
    let startpos = cur_pos pb in
    let n = at_start_pos leftmost name_parser pb in
    let endpos = cur_pos pb in
    let _ = whitespaces pb in
    Lazy.lazy_from_fun (fun () ->
      ([Lazy.force n, (startpos, endpos)], avar_ (), Explicit)        
    )
  )

end pb

(* this is term resulting for the application of term_lvl2 *)
and parse_term_lvl0 (defs: defs) (leftmost: (int * int)) (pb: parserbuffer) : term Lazy.t = memo_term begin
  fun pb -> 
    (* first we parse the application head *)
    let startpos = cur_pos pb in
    let head = parse_term_lvl1 defs leftmost pb in    
    let _ = whitespaces pb in
    (* then we parse the arguments *)
    let args = many (
      fun pb ->
	parse_arguments defs leftmost pb
    ) pb in
    let endpos = cur_pos pb in
    Lazy.lazy_from_fun (fun () ->
      match Lazy.force args with
	| [] -> Lazy.force head
	| args -> 
	  app_ ~pos:(Position ((startpos, endpos), [])) (Lazy.force head) args
    )
end pb

(* arguments: term_lvl2 with possibly brackets *)
and parse_arguments (defs: defs) (leftmost: (int * int)) (pb: parserbuffer) : (term * nature) Lazy.t = begin
  (fun pb -> 
    let _ = whitespaces pb in
    let te = at_start_pos leftmost (bracket ((parse_term defs leftmost))) pb in
    Lazy.lazy_from_fun (fun () ->
      (Lazy.force te, Implicit)
    )
  )
  <|> (fun pb -> 
    let te = (parse_term_lvl1 defs leftmost) pb in
    Lazy.lazy_from_fun (fun () ->
      (Lazy.force te, Explicit)
    )
  )
end pb

(* these are the most basic terms + top-level terms in parenthesis *)
and parse_term_lvl1 (defs: defs) (leftmost: (int * int)) (pb: parserbuffer) : term Lazy.t = memo_term begin
  (fun pb -> 
    let _ = whitespaces pb in
    at_start_pos leftmost (paren (parse_term defs leftmost)) pb)
  <|> (*tryrule*) (fun pb ->
    let _ = whitespaces pb in
    let pos = at_start_pos leftmost (with_pos name_parser) pb in
    let _ = whitespaces pb in
    Lazy.lazy_from_fun (fun () ->
      let n, pos = Lazy.force pos in
      name_ ~pos:(pos_to_position pos) n
    )
  )
  <|> (*tryrule*) (fun pb -> 
    let _ = whitespaces pb in
    let pos = at_start_pos leftmost (with_pos (word "Type")) pb in
    let _ = whitespaces pb in
    Lazy.lazy_from_fun (fun () ->
      type_ ~pos:(pos_to_position (snd (Lazy.force pos))) (UName "")
    )
  ) 
  <|> (*tryrule*) (fun pb -> 
    let _ = whitespaces pb in
    let pos = at_start_pos leftmost (with_pos (word "Set")) pb in
    let _ = whitespaces pb in
    Lazy.lazy_from_fun (fun () ->
      set_ ~pos:(pos_to_position (snd (Lazy.force pos))) (UName "")
    )
  ) 
  <|> (*tryrule*) (fun pb -> 
    let _ = whitespaces pb in
    let pos = at_start_pos leftmost (with_pos (word "Prop")) pb in
    let _ = whitespaces pb in
    Lazy.lazy_from_fun (fun () ->
      prop_ ~pos:(pos_to_position (snd (Lazy.force pos))) (UName "")
    )
  ) 
  <|> (*tryrule*) (fun pb ->
    let _ =  whitespaces pb in
    let pos = at_start_pos leftmost (with_pos parse_avar) pb in
    let _ = whitespaces pb in
    Lazy.lazy_from_fun (fun () ->
      avar_ ~pos:(pos_to_position (snd (Lazy.force pos))) ()
    )
  ) 
  <|> (*tryrule*) (parse_match defs leftmost)
  <|> (*tryrule*) (parse_let defs leftmost)
end pb

and parse_let (defs: defs) (leftmost: (int * int)) (pb: parserbuffer) : term Lazy.t = (
    let _ = whitespaces pb in
    let startpos = cur_pos pb in    
    let _ = at_start_pos leftmost (word "let") pb in
    let _ = whitespaces pb in
    let n = at_start_pos leftmost name_parser pb in
    let _ = whitespaces pb in
    let _ = at_start_pos leftmost (word ":=") pb in
    let _ = whitespaces pb in
    let te = parse_term defs leftmost pb in
    let _ = whitespaces pb in
    let _ = at_start_pos leftmost (word "in") pb in
    let _ = whitespaces pb in
    let te2 = parse_term defs leftmost pb in
    let endpos = cur_pos pb in    
    let _ = whitespaces pb in
    Lazy.lazy_from_fun (fun () ->
      let_ ~pos:(pos_to_position (startpos, endpos)) (Lazy.force n) (Lazy.force te) (Lazy.force te2)
    )
)

and parse_match (defs: defs) (leftmost: (int * int)) (pb: parserbuffer) : term Lazy.t = (
  let _ = whitespaces pb in
  let startpos = cur_pos pb in    
  let _ = at_start_pos leftmost (word "match") pb in
  let _ = whitespaces pb in
  let te = parse_term defs leftmost pb in
  let _ = whitespaces pb in
  let _ = at_start_pos leftmost (word "with") pb in
  let eqs = many (fun pb ->
    let _ = whitespaces pb in
    let _ = at_start_pos leftmost (word "|") pb in
    let _ = whitespaces pb in
    let newleftmost = cur_pos pb in
    let p = at_start_pos leftmost (parse_pattern defs leftmost) pb in
    let _ = whitespaces pb in
    let _ = at_start_pos leftmost (word ":=") pb in
    let _ = whitespaces pb in
    let te = parse_term defs newleftmost pb in
    Lazy.lazy_from_fun (fun () ->
      ((Lazy.force p)::[]), (Lazy.force te)
    )
  ) pb in
  let _ = whitespaces pb in
  let _ = at_start_pos leftmost (word "end") pb in
  let endpos = cur_pos pb in    
  Lazy.lazy_from_fun (fun () ->
    match_ ~pos:(pos_to_position (startpos, endpos)) (Lazy.force te) (Lazy.force eqs)
  )
)

and parse_pattern (defs: defs) (leftmost: (int * int)) (pb: parserbuffer) : pattern Lazy.t = begin
  tryrule (fun pb -> 
    (* first we parse the application head *)
    let _ = whitespaces pb in
    let pos = at_start_pos leftmost (with_pos name_parser) pb in    
    let _ = whitespaces pb in
    (* then we parse the arguments *)
    let args = 
      many1 (
	fun pb ->
	  parse_pattern_arguments defs leftmost pb
      ) pb in
    Lazy.lazy_from_fun (fun () ->   
      let s, _ = Lazy.force pos in   
      PApp (s, List.flatten (Lazy.force args))	  
  )
  )
  <|> tryrule (parse_pattern_lvl1 defs leftmost)
end pb


and parse_pattern_arguments (defs: defs) (leftmost: (int * int)) (pb: parserbuffer) : (pattern * nature) list Lazy.t = begin
  (fun pb -> 
    let _ = whitespaces pb in
    let te = at_start_pos leftmost (bracket (parse_pattern defs leftmost)) pb in
    Lazy.lazy_from_fun (fun () ->   
      [Lazy.force te, Implicit]
    )
  )
  <|>(fun pb -> 
    let _ = whitespaces pb in
    let te = at_start_pos leftmost (paren (parse_pattern defs leftmost)) pb in
    Lazy.lazy_from_fun (fun () ->   
      [Lazy.force te, Explicit]
    )
  )
  <|> (fun pb -> 
    let te = parse_pattern_lvl1 defs leftmost pb in
    Lazy.lazy_from_fun (fun () ->   
      [Lazy.force te, Explicit]
    )
  )
end pb
  
and parse_pattern_lvl1 (defs: defs) (leftmost: (int * int)) (pb: parserbuffer) : pattern Lazy.t = begin
  tryrule (fun pb ->
    let _ = whitespaces pb in
    let _ = at_start_pos leftmost parse_avar pb in
    let _ = whitespaces pb in
    Lazy.lazy_from_val PAvar 
  ) 
  <|> tryrule (fun pb -> 
    let _ = whitespaces pb in
    let name = at_start_pos leftmost name_parser pb in
    let _ = whitespaces pb in    
    Lazy.lazy_from_fun (fun () ->   
      let name = Lazy.force name in
      try 
	match Hashtbl.find defs name with
	  | Constructor _ -> PCste name
	  | _ -> PName name
      with
	| Not_found -> PName name
    )
  )
  <|> tryrule (fun pb ->
    let _ = whitespaces pb in    
    at_start_pos leftmost (paren (parse_pattern defs leftmost)) pb    
  )
end pb


let rec parse_definition (defs: defs) (leftmost: int * int) : definition parsingrule =
  (* an inductive *)
  tryrule (fun pb ->
    let _ = whitespaces pb in
    let _ = at_start_pos leftmost (word "Inductive") pb in
    let _ = whitespaces pb in
    let s = at_start_pos leftmost name_parser pb in
    let _ = whitespaces pb in
    let qs = many (parse_lambda_lhs defs leftmost) pb in
    let _ = whitespaces pb in
    let _ = at_start_pos leftmost (word ":") pb in
    let startpos = cur_pos pb in
    let _ = whitespaces pb in
    let ty = parse_term defs leftmost pb in
    let endpos = cur_pos pb in
    let _ = whitespaces pb in
    let _ = at_start_pos leftmost (word ":=") pb in

    let _ = whitespaces pb in
    let _ = at_start_pos leftmost (mayberule (word "|")) pb in

    let cstors = separatedBy (fun pb ->
      let _ = whitespaces pb in
      let s = at_start_pos leftmost name_parser pb in
      let _ = whitespaces pb in
      let qs = many (parse_lambda_lhs defs leftmost) pb in
      let _ = whitespaces pb in
      let _ = at_start_pos leftmost (word ":") pb in
      let startpos = cur_pos pb in
      let _ = whitespaces pb in
      let ty = parse_term defs leftmost pb in
      let endpos = cur_pos pb in
      Lazy.lazy_from_fun (fun () ->   
	(Lazy.force s), set_term_pos (build_impls (Lazy.force qs) (Lazy.force ty)) (pos_to_position (startpos, endpos))
      )
    )
      (fun pb -> 
	let _ = whitespaces pb in
	let _ = at_start_pos leftmost (word "|") pb in
	let _ = whitespaces pb in
	Lazy.lazy_from_val ()
      ) pb in
    
    
    Lazy.lazy_from_fun (fun () ->   
      DefInductive (
	(Lazy.force s), 
	set_term_pos (build_impls (Lazy.force qs) (Lazy.force ty)) (pos_to_position (startpos, endpos)),
	Lazy.force cstors
      )
    )
  )
  (* a signature *)
  <|> tryrule (fun pb ->
    let _ = whitespaces pb in
    let _ = at_start_pos leftmost (word "Signature") pb in
    let _ = whitespaces pb in
    let s = at_start_pos leftmost name_parser pb in
    let _ = whitespaces pb in
    let qs = many (parse_lambda_lhs defs leftmost) pb in
    let _ = whitespaces pb in
    let _ = at_start_pos leftmost (word ":") pb in
    let startpos = cur_pos pb in
    let _ = whitespaces pb in
    let ty = parse_term defs leftmost pb in
    let endpos = cur_pos pb in
    Lazy.lazy_from_fun (fun () ->   
      DefSignature ((Lazy.force s), set_term_pos (build_impls (Lazy.force qs) (Lazy.force ty)) (pos_to_position (startpos, endpos)))
    )
  )
  (* a definition *)
  <|> tryrule (fun pb ->
    let _ = whitespaces pb in
    let _ = at_start_pos leftmost (word "Definition") pb in
    let _ = whitespaces pb in
    let s = at_start_pos leftmost name_parser pb in
    let _ = whitespaces pb in
    let qs = many (parse_lambda_lhs defs leftmost) pb in
    let _ = whitespaces pb in
    let ty = mayberule (fun pb ->
      let _ = at_start_pos leftmost (word ":") pb in
      let startpos = cur_pos pb in
      let _ = whitespaces pb in
      let ty = parse_term defs leftmost pb in
      let endpos = cur_pos pb in
      Lazy.lazy_from_fun (fun () ->   
	(set_term_pos (Lazy.force ty) (pos_to_position (startpos, endpos)))
      )
    ) pb in
    let _ = whitespaces pb in
    let _ = at_start_pos leftmost (word ":=") pb in
    let startpos2 = cur_pos pb in
    let _ = whitespaces pb in
    let te = parse_term defs leftmost pb in
    let endpos2 = cur_pos pb in
    Lazy.lazy_from_fun (fun () ->   
      let te = Lazy.force te in
      let qs = Lazy.force qs in
      let s = Lazy.force s in
      let te = match (Lazy.force ty) with
	| None -> 
	  (set_term_pos 
	     (build_lambdas qs te) 
	     (pos_to_position (startpos2, endpos2))
	  )
	| Some ty -> 
	  (set_term_annotation 
	     (set_term_pos 
		(build_lambdas qs (set_term_annotation te ty)) 
		(pos_to_position (startpos2, endpos2))
	     )
	     (build_impls qs ty)
	  ) in
      
      DefDefinition (s, te)
    )
  )
  (* a decreasing information *)
  <|> tryrule (fun pb ->
    let _ = whitespaces pb in
    let _ = at_start_pos leftmost (word "Decreasing") pb in
    let _ = whitespaces pb in
    let s = at_start_pos leftmost name_parser pb in
    let _ = whitespaces pb in
    let _ = at_start_pos leftmost (word "[") pb in
    let _ = whitespaces pb in
    let lst = separatedBy int_parser
      (fun pb -> 
	let _ = whitespaces pb in
	let _ = at_start_pos leftmost (word ",") pb in
	let _ = whitespaces pb in
	Lazy.lazy_from_val ()
      ) pb in
    let _ = whitespaces pb in
    let _ = at_start_pos leftmost (word "]") pb in
    let _ = whitespaces pb in
    Lazy.lazy_from_fun (fun () ->   
      DefDecreasing (Lazy.force s, Lazy.force lst)
    )
  )
  (* a computation *)
  <|> tryrule (fun pb ->
    let _ = whitespaces pb in
    let _ = at_start_pos leftmost (word "Compute") pb in
    let _ = whitespaces pb in
    let te = parse_term defs leftmost pb in
    let _ = whitespaces pb in
    Lazy.lazy_from_fun (fun () ->   
      DefCompute (Lazy.force te)
    )
  )
      

let rec parse_definition2 (defs: defs) (leftmost: int * int) : unit parsingrule =
  (* an inductive *)
  tryrule (fun pb ->
    let _ = whitespaces pb in
    let _ = at_start_pos leftmost (word "Inductive") pb in
    let _ = whitespaces pb in
    let s = at_start_pos leftmost name_parser pb in
    let _ = whitespaces pb in
    let qs = many (parse_lambda_lhs defs leftmost) pb in
    let _ = whitespaces pb in
    let _ = at_start_pos leftmost (word ":") pb in
    let startpos = cur_pos pb in
    let _ = whitespaces pb in
    let ty = parse_term defs leftmost pb in
    let endpos = cur_pos pb in
    let _ = whitespaces pb in
    let _ = at_start_pos leftmost (word ":=") pb in

    let _ = whitespaces pb in
    let _ = at_start_pos leftmost (mayberule (word "|")) pb in

    let cstors = separatedBy (fun pb ->
      let _ = whitespaces pb in
      let s = at_start_pos leftmost name_parser pb in
      let _ = whitespaces pb in
      let qs = many (parse_lambda_lhs defs leftmost) pb in
      let _ = whitespaces pb in
      let _ = at_start_pos leftmost (word ":") pb in
      let startpos = cur_pos pb in
      let _ = whitespaces pb in
      let ty = parse_term defs leftmost pb in
      let endpos = cur_pos pb in
      Lazy.lazy_from_fun (fun () ->   
	(Lazy.force s), set_term_pos (build_impls (Lazy.force qs) (Lazy.force ty)) (pos_to_position (startpos, endpos))
      )
    )
      (fun pb -> 
	let _ = whitespaces pb in
	let _ = at_start_pos leftmost (word "|") pb in
	let _ = whitespaces pb in
	Lazy.lazy_from_val ()
      ) pb in
    
    
    Lazy.lazy_from_fun (fun () ->   
      let s = Lazy.force s in
      let ty = set_term_pos (build_impls (Lazy.force qs) (Lazy.force ty)) (pos_to_position (startpos, endpos)) in
      let cstors = Lazy.force cstors in
      define_inductive s ty cstors
    )
  )
  (* a definition *)
  <|> tryrule (fun pb ->
    let _ = whitespaces pb in
    let _ = at_start_pos leftmost (word "Definition") pb in
    let _ = whitespaces pb in
    let s = at_start_pos leftmost name_parser pb in
    let _ = whitespaces pb in
    let qs = many (parse_lambda_lhs defs leftmost) pb in
    let _ = whitespaces pb in
    let ty = mayberule (fun pb ->
      let _ = at_start_pos leftmost (word ":") pb in
      let startpos = cur_pos pb in
      let _ = whitespaces pb in
      let ty = parse_term defs leftmost pb in
      let endpos = cur_pos pb in
      Lazy.lazy_from_fun (fun () ->   
	(set_term_pos (Lazy.force ty) (pos_to_position (startpos, endpos)))
      )
    ) pb in
    let _ = whitespaces pb in
    let _ = at_start_pos leftmost (word ":=") pb in
    let startpos2 = cur_pos pb in
    let _ = whitespaces pb in
    let te = parse_term defs leftmost pb in
    let endpos2 = cur_pos pb in
    Lazy.lazy_from_fun (fun () ->   
      let te = Lazy.force te in
      let qs = Lazy.force qs in
      let s = Lazy.force s in
      let te = match (Lazy.force ty) with
	| None -> 
	  (set_term_pos 
	     (build_lambdas qs te) 
	     (pos_to_position (startpos2, endpos2))
	  )
	| Some ty -> 
	  (set_term_annotation 
	     (set_term_pos 
		(build_lambdas qs (set_term_annotation te ty)) 
		(pos_to_position (startpos2, endpos2))
	     )
	     (build_impls qs ty)
	  ) in
      
      define_definition s te
    )
  )
  (* a recursive definition *)
  <|> tryrule (fun pb ->
    let _ = whitespaces pb in
    let _ = at_start_pos leftmost (word "Recursive") pb in
    let _ = whitespaces pb in
    let s = at_start_pos leftmost name_parser pb in
    let _ = whitespaces pb in
    let qs = many (parse_lambda_lhs defs leftmost) pb in
    let _ = whitespaces pb in
    let _ = at_start_pos leftmost (word "[") pb in
    let _ = whitespaces pb in
    let lst = separatedBy int_parser
      (fun pb -> 
	let _ = whitespaces pb in
	let _ = at_start_pos leftmost (word ",") pb in
	let _ = whitespaces pb in
	Lazy.lazy_from_val ()
      ) pb in
    let _ = whitespaces pb in
    let _ = at_start_pos leftmost (word "]") pb in
    let _ = whitespaces pb in
    let _ = at_start_pos leftmost (word ":") pb in
    let _ = whitespaces pb in
    let ty = parse_term defs leftmost pb in
    let _ = whitespaces pb in
    let _ = at_start_pos leftmost (word ":=") pb in
    let startpos2 = cur_pos pb in
    let _ = whitespaces pb in
    let te = parse_term defs leftmost pb in
    let endpos2 = cur_pos pb in
    let _ = whitespaces pb in
    Lazy.lazy_from_fun (fun () ->   
      let te = Lazy.force te in
      let ty = Lazy.force ty in
      let lst = Lazy.force lst in
      let qs = Lazy.force qs in
      let s = Lazy.force s in
      let te = 
	  (set_term_annotation 
	     (set_term_pos 
		(build_lambdas qs (set_term_annotation te ty)) 
		(pos_to_position (startpos2, endpos2))
	     )
	     (build_impls qs ty)
	  ) in
      let ty = (build_impls qs ty) in
      define_recursive s ty te lst
    )
  )
  (* a computation definition *)
  <|> tryrule (fun pb ->
    let _ = whitespaces pb in
    let _ = at_start_pos leftmost (word "Compute") pb in
    let _ = whitespaces pb in
    let te = parse_term defs leftmost pb in
    let _ = whitespaces pb in
    Lazy.lazy_from_fun (fun () ->
      let te = Lazy.force te in
      let te2 = from_ground_term te in
      let te3 = reduce te2 in
      (*printf "Computation done\n"; flush stdout;*)
      printf "Compute %s := %s : %s\n" (term2string (ref empty_context) te)  (term2string (ref empty_context) (to_ground_term te3)) (term2string (ref empty_context) (to_ground_term (type_of te3)))
					       
    )
  )
  (* a computation definition *)
  <|> tryrule (fun pb ->
    let _ = whitespaces pb in
    let _ = at_start_pos leftmost (word "Check") pb in
    let _ = whitespaces pb in
    let te = parse_term defs leftmost pb in
    let _ = whitespaces pb in
    Lazy.lazy_from_fun (fun () ->
      let te = Lazy.force te in
      let te2 = from_ground_term te in
      printf "Check %s : %s\n" (term2string (ref empty_context) te)  (term2string (ref empty_context) (to_ground_term (type_of te2)))
    )
  )
;;      
