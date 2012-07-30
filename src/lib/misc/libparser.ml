(*
  
  This file is free software: you can redistribute it and/or modify
  it under the terms of the GNU General Public License as published by
  the Free Software Foundation, either version 3 of the License, or
  (at your option) any later version.
  
  This file is distributed in the hope that it will be useful,
  but WITHOUT ANY WARRANTY; without even the implied warranty of
  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
  GNU General Public License for more details.
  
  You should have received a copy of the GNU General Public License
  along with this file.  If not, see <http://www.gnu.org/licenses/>.
  
  Copyright (C) Nicolas Marti
*)

open Stream;;
open Printf;;
open Str;;
open Buffer;;
open Hashtbl;;


type parserbuffer = {
  mutable inputstream: string Stream.t; 
  mutable bufferstr: Buffer.t;
  mutable beginpointer: int;    
  mutable error: ((int * int) * (int * int) * (int * int) * string) list
};;

let build_parserbuffer stream = {
  inputstream = stream;
  bufferstr = Buffer.create 0;
  beginpointer = 0;
  error = [];
};;

let current_buffer (pb: parserbuffer) =
  let s = Buffer.contents pb.bufferstr in
  String.sub s (pb.beginpointer) (String.length s - pb.beginpointer)
    
(* test if we reach the end of the buffer *)
let endofbuffer (pb:parserbuffer) = 
  (pb.beginpointer = Buffer.length pb.bufferstr)
    
let pos_coo (pb: parserbuffer) (pos: int) : (int * int) =
  let nb_row = ref 0 in
  let cur_index = ref 0 in
  let last_index = ref 0 in
  let s = Buffer.contents pb.bufferstr in
  try 
    while !cur_index <= pos do
      last_index := !cur_index;
      cur_index := String.index_from s !cur_index '\n';
      cur_index := !cur_index + 1;
      if !cur_index <= pos then nb_row := !nb_row + 1 else ();
    done;
    (!nb_row, pos - !last_index)
  with
    | Not_found -> (!nb_row, pos - !last_index)
;;

let cur_pos pb = pos_coo pb pb.beginpointer
;;

type pos = ((int * int) * (int * int))
;;

let nopos = (-1, -1), (-1, -1)

exception NoMatch;;

(* match a regular expression on a buffer:
   
   takes: * r: a regular expression of Str module
   * pb: a parserbuffer (defined above)
   
   returns: * if the regular expression is matched at the current position of the parserbuffer, the string corresponding
   * otherwise, when the regular expression cannot be matched, raise NoMatch
   
*)
let rec match_regexp (r: regexp) (pb:parserbuffer) : string =
  
  (* if our begin pointer is at the end of the buffer, we should grab another line *)
  if endofbuffer pb then (
    try 
      let str = Stream.next pb.inputstream in
      Buffer.add_string pb.bufferstr str;
      Buffer.add_string pb.bufferstr "\n"          
    with
      | Stream.Failure -> 
        raise NoMatch;
        
  ) else ();    
  (* first look if we can find the expression on the buffer *)
  if string_match r (Buffer.contents pb.bufferstr) pb.beginpointer then
    (* we found it, we grab the string and return it after moving the begin pointer forward*)
    let str = matched_string (Buffer.contents pb.bufferstr) in
    let newpos = pb.beginpointer + String.length str in
    if newpos = Buffer.length pb.bufferstr then (
      
      try 
        let str = Stream.next pb.inputstream in
        Buffer.add_string pb.bufferstr str;
        Buffer.add_string pb.bufferstr "\n";
        match_regexp r pb
	  
      with
        | Stream.Failure -> 
          pb.beginpointer <- pb.beginpointer + String.length str;
          str
	    
    ) else (
      
      pb.beginpointer <- pb.beginpointer + String.length str;
      str
    )
      
  else (
    (* else, maybe we just have the beginning, and need one more line *)
    if string_partial_match r (Buffer.contents pb.bufferstr) pb.beginpointer then (
      (try 
         let str = Stream.next pb.inputstream in
         Buffer.add_string pb.bufferstr str;
         Buffer.add_string pb.bufferstr "\n"
       with
         | Stream.Failure -> raise NoMatch
      ); match_regexp r pb
    ) else (
      raise NoMatch
    )
      
  )
;;


(* 
   definition of lexing rule and how to apply it
   + a little example for int
*)

type 'a lexingrule = regexp * (string -> 'a)
;;

let rec applylexingrule (r: 'a lexingrule) (pb:parserbuffer) : 'a =
  let str = match_regexp (fst r) pb in
  (snd r) str
;;

(* parsing rules *)

type 'a parsingrule = parserbuffer -> 'a
;;

(* the parser that return a constante *)
let parsecste (v: 'a) (pb: parserbuffer) : 'a =
  v
;;

(* try to apply a parsing rule, if it fails it restore the original beginpointer *)

let tryrule (r: 'a parsingrule) (pb:parserbuffer) : 'a =
  let savebegin = pb.beginpointer in
  try 
    r pb
  with
    | NoMatch -> 
      pb.beginpointer <- savebegin;
      raise NoMatch
;;

let mayberule (r: 'a parsingrule) (pb:parserbuffer) : 'a option =
  let savebegin = pb.beginpointer in
  try 
    Some (r pb)
  with
    | NoMatch -> 
      pb.beginpointer <- savebegin;
      None
;;

(* one of *)
let rec one_of (l: string list): string parsingrule =
  fun pb ->
    let savebegin = pb.beginpointer in
    match l with
      | [] -> raise NoMatch
      | hd::tl ->
	try
	  applylexingrule (regexp_string hd, (fun s -> s)) pb
	with
	  | NoMatch -> 
	    pb.beginpointer <- savebegin;
	    one_of tl pb
;;

(* we try some parsing rule, but without changing the pointer to the parsing buffer or raising NoMAtch exception *)
let predictrule (r: 'a parsingrule) (pb:parserbuffer) : ('a * int) option =
  let savebegin = pb.beginpointer in
  try 
    let res = r pb in
    let saveend = pb.beginpointer in
    pb.beginpointer <- savebegin;
    Some (res, saveend)        
  with
    | NoMatch -> 
      pb.beginpointer <- savebegin;
      None
;;


(* disjunction of two parsingrules *)
let orrule (r1: 'a parsingrule) (r2: 'a parsingrule) (pb: parserbuffer) : 'a =
  let savebegin = pb.beginpointer in
  try 
    r1 pb
  with
    | NoMatch -> 
      pb.beginpointer <- savebegin;
      r2 pb
;;

let (<|>) r1 r2 pb = orrule r1 r2 pb;;

(* conjunction of two parsingrules *)
let andrule (r1: ('a -> 'b) parsingrule) (r2: 'a parsingrule) (pb: parserbuffer) : 'b =
  let res1 = r1 pb in
  let res2 = r2 pb in
  res1 res2
;;

let (>>) r1 r2 = andrule r1 r2;;

let thenrule (r1: 'a parsingrule) (r2: 'b parsingrule) (pb: parserbuffer) : 'b =
  let _ = r1 pb in
  let res2 = r2 pb in
  res2
;;

let (>>>) r1 r2 = thenrule r1 r2;;

(* not combinator *)
let notp (r: 'a parsingrule) (pb: parserbuffer) : unit =
  let savebegin = pb.beginpointer in
  let res = (
    try 
      let _ = (tryrule r) pb in
      false
    with
      | NoMatch -> true
  ) in
  if res then ()
  else (
    pb.beginpointer <- savebegin;
    raise NoMatch
  )
;;

(* always returns NoMatch *)
let nokp (pb: parserbuffer) =
  raise NoMatch
;;

(* always returns () *)
let okp (pb: parserbuffer) =
  ()
;;

(* a parser for spaces *)
let spaces : ('a -> 'a) parsingrule = 
  fun pb ->
    try    
      (* it seems a miss something ... but what ?? *)
      applylexingrule (regexp "[\t \r \n]*", fun (s:string) -> fun x -> x) pb
    with
      | NoMatch -> fun x -> x      
;;

let whitespaces : unit parsingrule = 
  fun pb ->
    try    
      (* it seems a miss something ... but what ?? *)
      applylexingrule (regexp "[\t \r \n]*", fun (s:string) -> 
	(*printf "whitespaces := '%s'\n" s;*)
	()) pb
    with
      | NoMatch -> ()      
;;


let keyword (s: string) (v: 'a) : 'a parsingrule =
  fun pb ->
    (spaces >> (applylexingrule (regexp_string s, (fun _ -> v)))) pb
;;

let word (s: string) : unit parsingrule =
  (applylexingrule (regexp_string s, (fun _ -> ())))
;;

let words (s: string) : string parsingrule =
  (applylexingrule (regexp_string s, (fun s -> s)))
;;

let paren (p: 'a parsingrule) : 'a parsingrule =
  spaces >>> (
    fun pb ->
      let _ = applylexingrule (regexp "(", fun (s:string) -> ()) pb in
      let _ = whitespaces pb in
      let res = 
	try 
	  p pb 
	with 
	  | NoMatch -> raise NoMatch
      in
      let _ = whitespaces pb in
      let _ = applylexingrule (regexp ")", fun (s:string) -> ()) pb in
      res
  )
;;

let bracket (p: 'a parsingrule) : 'a parsingrule =
  spaces >>> (
    fun pb ->
      let _ = whitespaces pb in
      let _ = applylexingrule (regexp "{", fun (s:string) -> ()) pb in
      let _ = whitespaces pb in
      let res = 
	try 
	  p pb 
	with 
	  | NoMatch -> raise NoMatch
      in
      let _ = whitespaces pb in
      let _ = applylexingrule (regexp "}", fun (s:string) -> ()) pb in
      res
  )
;;


(* parser asserting that next there is not a string inside the list *)
let notpl (l: string list) : unit parsingrule =
  notp (List.fold_left (
    fun acc hd ->
      let parse = word hd in
      orrule acc parse 
  ) nokp l)
;;


(* many combinator *)
let rec many (r: 'a parsingrule) (pb: parserbuffer) : 'a list =
  let hd = (
    try 
      Some (r pb)
    with
      | NoMatch -> None
  ) in
  match hd with
    | None -> []
    | Some hd -> 
      let tl = many r pb in
      hd::tl
;;

let many1 (r: 'a parsingrule) (pb: parserbuffer) : 'a list =
  let hd = r pb in
  let tl = many r pb in
  hd::tl
;;

let many2 (r: 'a parsingrule) (pb: parserbuffer) : 'a list =
  let savebegin = pb.beginpointer in
  try 
    let hd1 = r pb in
    let hd2 = r pb in
    let tl = many r pb in
    hd1::hd2::tl
  with
    | NoMatch ->
      (
        pb.beginpointer <- savebegin;
        raise NoMatch
      )
;;

(* parse any character (except newline, and the token in the list) *)
let any_except_nl : string list -> string parsingrule = 
  fun l pb ->
    let s = many (fun pb ->
      let () = notpl l pb in
      applylexingrule (regexp ".", fun (s:string) -> s) pb
    ) pb in
    String.concat "" s
;;

let any_except : string list -> string parsingrule = 
  fun l pb ->
    let s = many (fun pb ->
      let () = notpl l pb in
      applylexingrule (regexp ".\\|[\r \n]", fun (s:string) -> s) pb
    ) pb in
    String.concat "" s
;;

(* do an until NoMatch *)
let rec fixpoint (p: 'a -> 'a parsingrule) (a: 'a) (pb: parserbuffer) : 'a =
  try 
    let res = p a pb in
    fixpoint p res pb
  with
    | NoMatch -> a
;;


let (|>) v p = (parsecste v) >> p
;;

let rec separatedBy (elem: 'a parsingrule) (sep: 'b parsingrule) (pb: parserbuffer) : 'a list =
  let hd = elem pb in
  let tl = try (
    let _ = sep pb in
    separatedBy elem sep pb
  ) with
    | NoMatch -> [] in
  hd :: tl
;; 

(*
let rec separatedBy (elem: 'a parsingrule) (sep: 'b parsingrule) (pb: parserbuffer) : 'a list =
  (
    (tryrule
       (
	 ((fun x l -> x::l) |> 
	     elem) >> (separatedBy elem sep)
       )
    ) <|> (parsecste [])
  ) pb
;;
*)
(* fold on parser, they are all tried, and it fails if none hold *)
let foldp (l: ('a parsingrule) list) : 'a parsingrule =
  (List.fold_left (
    fun acc hd ->
      orrule acc (tryrule hd) 
   ) nokp l)
;;

(* operator precedence *)
type associativity =
  | LeftAssoc
  | RightAssoc
  | NoAssoc
;;

(*
  fold : ('a -> 'b -> 'c -> 'c) -> ('a, 'b) t -> 'c -> 'c
*)

let op_pos_parser (opdef: (string, (int * associativity * ('d -> 'b -> 'b -> 'c))) Hashtbl.t) : (string * pos) parsingrule =
  Hashtbl.fold ( fun key value acc ->
    (spaces >> ((fun b s e -> (s, (b, e))) |> cur_pos >> (applylexingrule (regexp_string key, (fun _ -> key))) >> cur_pos)) 
    <|> acc             
  ) opdef nokp
;;


let op_par_pos_parser (opdef: (string, (int * associativity * ('d -> 'b -> 'b -> 'c))) Hashtbl.t) : (string * pos) parsingrule =
  Hashtbl.fold ( fun key value acc ->
    (spaces >> ((fun b s e -> (s, (b, e))) |> cur_pos >> (applylexingrule (regexp_string (String.concat "" ["("; key; ")"]), (fun _ -> key))) >> cur_pos)) 
    <|> acc             
  ) opdef nokp
;;

let rec operator_precedence (opparse: ('a * 'd) parsingrule) (opdef: ('a, (int * associativity * ('d -> 'b -> 'b -> 'c))) Hashtbl.t) (primary: 'b parsingrule) : 'c parsingrule =
  fun pb ->
    let lhs = primary pb in
    let min_pred = 0 in
    operator_precedence_loop opparse opdef primary lhs min_pred pb
and operator_precedence_loop (opparse: ('a * 'd) parsingrule) (opdef: ('a, (int * associativity * ('d -> 'b -> 'b -> 'c))) Hashtbl.t) (primary: 'b parsingrule) (lhs: 'b) (min_pred: int) : 'c parsingrule =
  fun pb ->
    try 
      match predictrule ((fun x y -> (x, y)) |> opparse >> primary) pb with 
        | None -> lhs
        | Some (((op, p), rhs), ptr) ->
          let (pred, _, f) = Hashtbl.find opdef op in
          if (pred < min_pred) then lhs else (
            pb.beginpointer <- ptr;
            let rhs = (
              match predictrule opparse pb with
                | None -> rhs
                | Some ((nop, p), _) ->
                  let (npred, nassoc, _) = Hashtbl.find opdef nop in
                  if (npred > pred || (npred = pred && nassoc = RightAssoc)) then
                    operator_precedence_loop opparse opdef primary rhs npred pb      
                  else
                    rhs
            ) in
            let lhs = f p lhs rhs in
            operator_precedence_loop opparse opdef primary lhs min_pred pb      
	  )
    with 
      | Not_found -> lhs
        
	
(* this combinator push an error message in the parserbuffer if the parser fails *)
let error (p: 'a parsingrule) (s: string) : 'a parsingrule =
  fun pb ->
    let savebegin = pb.beginpointer in
    try 
      p pb 
    with
      | NoMatch -> 
        let errend = pb.beginpointer in
	if (savebegin = errend) then (
	  let _ = applylexingrule (regexp ".", fun (s:string) -> s) pb in
	  ()
	);
        let errend = pb.beginpointer in
        pb.error <- ((pos_coo pb savebegin),(pos_coo pb errend), (savebegin, errend), s)::pb.error;
	pb.beginpointer <- savebegin;
        raise NoMatch;
;;


let (<!>) p s pb = error p s pb;;

let keyworderr (s: string) (v: 'a) : 'a parsingrule =
  let error = String.concat "" ["error. string '"; s; "' cannot be parse"] in
  fun pb ->
    (spaces >> (applylexingrule (regexp_string s, (fun _ -> v))) <!> error) pb
;;

let (<!!>) p s pb =
  try 
    p pb
  with
    | NoMatch -> 
      let coo = pos_coo pb pb.beginpointer in
      printf "%s" (String.concat "" [s; " @ "; string_of_int (snd coo); "\n"]); raise NoMatch
;;

let rec errors2string (pb: parserbuffer) : string =
  try (
  let errors = 
    let cmp (e1, _, _, _) (e2, _, _, _) =
      if (fst e2) > (fst e1) then 1 else 
	if (fst e2) < (fst e1) then -1 else
	  (snd e2) - (snd e1)
	in
    List.sort cmp pb.error
  in
  String.concat "\n" (
    List.map (
      fun ((b1,e1), (b2, e2), (b, e), s) -> String.concat "" ["("; 
							      "("; string_of_int b1; ","; string_of_int e1; ")";
							      "-- '"; (Buffer.sub pb.bufferstr b (e - b)); "' -->";
							      "("; string_of_int b2; ","; string_of_int e2; ")";
							      "): "; s]
    ) errors
  )
  )
  with 
    | Invalid_argument "Buffer.sub" -> "Buffer.sub error"
;;


let markerror (pb: parserbuffer) : string =
  let errors = 
    let cmp (e1, _, _, _) (e2, _, _, _) =
      if (fst e2) > (fst e1) then 1 else 
	if (fst e2) < (fst e1) then -1 else
	  (snd e2) - (snd e1)
	in
    List.sort cmp pb.error
  in
  match errors with
    | [] -> Buffer.contents pb.bufferstr
    | ((b1,e1), (b2, e2), (b,e), s)::_ ->
      let s1 = Buffer.sub pb.bufferstr 0 b in
      let se = Buffer.sub pb.bufferstr b (e - b) in
      let s2 = Buffer.sub pb.bufferstr (e+1) (Buffer.length pb.bufferstr - e - 1) in
      String.concat "" [s1; " >>> "; se; " <<< "; s2; "\n"; 
                        string_of_int b1; ":"; string_of_int e1;"-";
                        string_of_int b2; ":"; string_of_int e2;" = ";
                        s]
;;


(* New version for prefix / infix parsing *)

(* the structure which contains:
   1) the primary subset parser
   2) list of the prefix
   3) list of the infix
*)
type priority = int;;

type 'a opparser = {
  primary: 'a parsingrule;
  (* pos prefix -> the position of the operator *)
  prefixes: (string, (priority * (pos -> 'a -> 'a))) Hashtbl.t;
  infixes: (string, (priority * associativity * (pos -> 'a -> 'a -> 'a))) Hashtbl.t;
  postfixes: (string, (priority * (pos -> 'a -> 'a))) Hashtbl.t;  
  reserved: unit parsingrule;
};;

(* the last arguments point to the father node *)
type 'a parsetree = Leaf of ('a parsetree) option
                    | Node of 'a node * ('a parsetree) option
			
(* the option indicate which child point to this node *)
and 'a node = | PrimaryNode of 'a
              | PrefixNode of string * priority * ('a -> 'a) * ('a parsetree) option
              | InfixNode of string * priority * associativity * ('a -> 'a -> 'a) * ('a parsetree) option * ('a parsetree) option
              | PostfixNode of string * priority * ('a -> 'a) * ('a parsetree) option
;;

(* create a basic node from a prefix *)
let node_from_prefix (prefix: (string * priority * ('a -> 'a))) : 'a node =
  let (name, p, f) = prefix in
  PrefixNode (name, p, f, Some (Leaf None))
;;

(* create a basic node from a prefix *)
let node_from_postfix (postfix: (string * priority * ('a -> 'a))) : 'a node =
  let (name, p, f) = postfix in
  PostfixNode (name, p, f, Some (Leaf None))
;;

(* create a basic node from an infix *)
let node_from_infix (infix: (string * priority * associativity * ('a -> 'a -> 'a))) : 'a node =
  let (name, p, a, f) = infix in
  InfixNode (name, p, a, f, Some (Leaf None), Some (Leaf None))
;;

(* go up one level *)
let zip_up_parsetree (t: 'a parsetree) : 'a parsetree =
  match t with
    (* we are in a leaf *)
    | Leaf (Some root) -> (
      (* we inspect the father node *)
      match root with
	(* it is a PrefixNode *)
        | Node (PrefixNode (name, prio, f, None), 
                root
        ) -> 
          Node (
            PrefixNode (name, prio, f, 
                        Some (Leaf None)
            ), 
            root
          )
	(* it is a PostfixNode *)
        | Node (PostfixNode (name, prio, f, None), 
                root
        ) -> 
          Node (
            PostfixNode (name, prio, f, 
                         Some (Leaf None)
            ), 
            root
          )
	(* it is an infix, and we are the left node *)
        | Node (InfixNode (name, prio, assoc, f, None, Some right), 
                root
        ) -> 
          Node (InfixNode (name, prio, assoc, f, 
                           Some (Leaf None), 
                           Some right
          ), 
                root
          )
	(* it is an infix, and we are the right node *)
        | Node (InfixNode (name, prio, assoc, f, Some left, None), 
                root
        ) -> 
          Node (InfixNode (name, prio, assoc, f, Some left, 
                           Some (Leaf None)
          ), root)
    )
    (* we are a node *)
    | Node (node, Some root) -> (
      (* look at the root *) 
      match root with
	(* it is a prefix *)
        | Node (PrefixNode (name, prio, f, None), 
                root
        ) -> 
          Node (
            PrefixNode (name, prio, f, 
                        Some (Node (node, None))
            ), 
            root
          )
	(* it is a postfix *)
        | Node (PostfixNode (name, prio, f, None), 
                root
        ) -> 
          Node (
            PostfixNode (name, prio, f, 
                         Some (Node (node, None))
            ), 
            root
          )
	(* it is an infix, we are the left child *)
        | Node (InfixNode (name, prio, assoc, f, None, Some right), 
                root
        ) -> 
          Node (InfixNode (name, prio, assoc, f, 
                           Some (Node (node, None)), 
                           Some right
          ), 
                root
          )
	(* it is an infix, we are the right child *)
        | Node (InfixNode (name, prio, assoc, f, Some left, None), 
                root
        ) -> 
          Node (InfixNode (name, prio, assoc, f, Some left, 
                           Some (Node (node, None))
          ), root)
    )
;;

let rec zip_up_parsetree_until_root (t: 'a parsetree) : 'a parsetree =
  match t with
    | Node (node, Some root) -> zip_up_parsetree_until_root (zip_up_parsetree t)
    | _ -> t
;;


(* go down on prefix *)
let zip_down_prefix (t: 'a parsetree) : 'a parsetree =
  let Node (PrefixNode (name, prio, f, Some child), root) = t in
  match child with
    | Leaf None ->
      Leaf (Some (Node (PrefixNode (name, prio, f, None), root)))
    | Node (node, None) ->
      Node (node, Some (Node (PrefixNode (name, prio, f, None), root)))
;;

(* go down on postfix *)
let zip_down_postfix (t: 'a parsetree) : 'a parsetree =
  let Node (PostfixNode (name, prio, f, Some child), root) = t in
  match child with
    | Leaf None ->
      Leaf (Some (Node (PostfixNode (name, prio, f, None), root)))
    | Node (node, None) ->
      Node (node, Some (Node (PostfixNode (name, prio, f, None), root)))
;;

(* go down on infix. True with choice: left, False: right *)
let zip_down_infix_choice (t: 'a parsetree) (child: bool) : 'a parsetree =
  let Node (InfixNode (name, prio, assoc, f, Some left, Some right), root) = t in
  if child then (
    match left with
      | Leaf None ->
        Leaf (Some (Node (InfixNode (name, prio, assoc, f, None, Some right), root)))
      | Node (node, None) -> 
        Node (node, Some (Node (InfixNode (name, prio, assoc, f, None, Some right), root)))
  ) else (
    match right with
      | Leaf None ->
        Leaf (Some (Node (InfixNode (name, prio, assoc, f, Some left, None), root)))
      | Node (node, None) ->
        Node (node, Some (Node (InfixNode (name, prio, assoc, f, Some left, None), root)))
  )
;;

(* go down an infix on first available child (need one to be a leaf) *)
let zip_down_infix (t: 'a parsetree) : 'a parsetree =
  match t with
    | Node (InfixNode (name, prio, assoc, f, Some (Leaf None), Some right), root) ->
      zip_down_infix_choice t true
    | Node (InfixNode (name, prio, assoc, f, Some left, Some (Leaf None)), root) ->
      zip_down_infix_choice t false
;;

(* we can only insert primary on Leaf *)
let insert_primary (a: 'a) (t: 'a parsetree) : 'a parsetree =
  (*printf "Insert primary\n";*)
  match t with
    | Leaf root ->
      Node (PrimaryNode a, root)
    | _ -> printf "insert_primary: not a Leaf root\n"; raise NoMatch
;;

(* inserting a prefix: the next place to add is the Leaf *)
let insert_prefix (prefix: (string * priority * ('a -> 'a))) (t: 'a parsetree) : 'a parsetree =
  (*let (n, _, _) = prefix in printf "Insert prefix: '%s'\n" n;*)
  match t with 
    | Leaf root ->
      let newroot = Node (node_from_prefix prefix, root) in
      zip_down_prefix newroot
;;

(* inserting a postfix: TODO *)
let rec insert_postfix (postfix: (string * priority * ('a -> 'a))) (t: 'a parsetree) : 'a parsetree =
  (*let (n, _, _) = prefix in printf "Insert prefix: '%s'\n" n;*)
  let (name, prio, f) = postfix in
  match t with
    (* we are on a primary value, without root *)
    | Node (PrimaryNode a, None) as r ->
      Node (PostfixNode (name, prio, f, Some r), None)
    (* we are on a primary value, with root *)
    | Node (PrimaryNode a, Some root) ->
      insert_postfix postfix (zip_up_parsetree t)
    (* we are on a prefix, if we bind more we insert ourself inbetween, else we zipup (or becoming root if there's not) *)
    | Node (PrefixNode (name2, prio2, f2, child), root) as r -> (

      if (prio > prio2) then (
	
	let newroot = Node (PrefixNode 
			      (name2, prio2, f2, 
			       Some (Node (PostfixNode (name, prio, f, child), None))
			      ), root) in
	zip_up_parsetree newroot

      ) else (

	match root with
	  | None -> Node (PostfixNode (name, prio, f, 
				       Some r), None)
	  | Some _ ->
	    insert_postfix postfix (zip_up_parsetree t)
	      
      )
    )
    (* we are on a prefix: either we bind more, and then insert on the right child
       either we bind less and we insert after zipping up (or become root if there's not)
    *)
    | Node (InfixNode (name2, prio2, assoc2, f2, childl, childr), root) as r -> (

      if (prio > prio2) then (
	
	Node (InfixNode (name2, prio2, assoc2, f2, childl, 
			 Some (
			   Node (PostfixNode (name, prio, f, childr), None)
			 )), root
	)

      ) else (

	match root with
	  | None -> Node (PostfixNode (name, prio, f, Some r), None)

	  | Some _ ->
	    insert_postfix postfix (zip_up_parsetree t)
      )

    )
;;

(* we insert an infix in the tree, depending the case we might need to go up / down in the tree*)
let rec insert_infix (infix: (string * priority * associativity * ('a -> 'a -> 'a))) (t: 'a parsetree) : 'a parsetree =
  (*let (n, _, _, _) = infix in printf "Insert infix: '%s'\n" n;*)
  let (name, prio, assoc, f) = infix in
  match t with
    (* we are on a primary without root, we create an infix with the primary as the left child and go down the left one*)
    | Node (PrimaryNode a, None) ->
      let newroot = Node (InfixNode (name, prio, assoc, f, Some (Node (PrimaryNode a, None)), Some (Leaf None)), None) in
      zip_down_infix_choice newroot false
	
    (* we are on a primary with a root, we zip_up the tree and redo *)
    | Node (PrimaryNode a, Some root) ->
      let newroot = zip_up_parsetree t in
      insert_infix infix newroot

    (* we are on a prefix *)
    | Node (PrefixNode (name2, prio2, f2, Some child), root) ->
      (* if it binds less than the infix, we insert the infix as its new child (its previous child becomes the infix left child) *)
      if (prio2 < prio) then (
	
        let newroot = Node (PrefixNode (name2, prio2, f2, Some (
          Node (InfixNode (name, prio, assoc, f, 
                           Some child,
                           Some (Leaf None)
          ),
                None
          )
        )
        ), 
                            root
        ) in
        zip_down_infix_choice (zip_down_prefix newroot) false
	  
      ) else (
	
	(* else the infix becomes replace the current node, which becomes its left child *)
        match root with
          | None -> (
	    
            let newroot = Node (InfixNode (name, prio, assoc, f, 
                                           Some (Node (PrefixNode (name2, prio2, f2, Some child), 
                                                       None
                                           )
                                           ),
                                           Some (Leaf None)
            ),
                                None
            ) in
            zip_down_infix_choice newroot false
          )
          | Some root ->
            let newroot = zip_up_parsetree t in
            insert_infix infix newroot                  
      )

    (* we are on a postfix --> it becomes our child *)
    | Node (PostfixNode (name2, prio2, f2, Some child), root) ->
      let newroot = Node (InfixNode (name, prio, assoc, f,
				     Some (Node (PostfixNode (name2, prio2, f2, Some child), None)),
				     Some (Leaf None)
      ),
			  root
      ) in
      zip_down_infix_choice newroot false

    (* we are on an infix *) 
    | Node (InfixNode (name2, prio2, assoc2, f2, Some left, Some right), root) ->
      (* which either bind more, or both are of equal prio and assoc = LeftAssoc*)
      if (prio2 > prio || (prio2 = prio && assoc = LeftAssoc)) then (
	
        match root with
	  (* the current node is the root of the tree*)
          | None -> (
            (* the current node become the left child of the inserted infix*)
            let newroot = Node (InfixNode (name, prio, assoc, f, 
                                           Some (Node (InfixNode (name2, prio2, assoc2, f2, Some left, Some right), 
                                                       None 
                                           )
                                           ),
                                           Some (Leaf None)
            ),
                                None
            ) in
            zip_down_infix_choice newroot false
	      
          )
	  (* there is a root, so we zip up the tree*)
          | Some root -> (
	    
            let newroot = zip_up_parsetree t in
            insert_infix infix newroot                  
              
          )
	    
      ) else (
	
	(* else the new infix is place at the right hand of the current node, the previous right child becoming its right one*)
        let newroot = Node (InfixNode (name2, prio2, assoc2, f2,
                                       Some left,
                                       Some (Node (InfixNode (name, prio, assoc, f, 
                                                              Some right,
                                                              Some (Leaf None)
                                       ),
                                                   None
                                       )
                                       )
        ),
                            root
        ) in
        
        zip_down_infix_choice (zip_down_infix_choice newroot false) false
	  
      )
;;


let rec tree_semantics (t: 'a parsetree) : 'a =
  match t with
    | Node (PrimaryNode a, _) -> a
    | Node (PrefixNode (_, _, f, Some child), _) ->
      f (tree_semantics child)
    | Node (PostfixNode (_, _, f, Some child), _) ->
      f (tree_semantics child)
    | Node (InfixNode (_, _, _, f, Some left, Some right), _) ->
      f (tree_semantics left) (tree_semantics right)
    | Node (PrefixNode (_, _, f, None), _) ->
      (*printf "PrefixNode without child\n";*) raise Failure
    | Node (PostfixNode (_, _, f, None), _) ->
      (*printf "PostfixNode without child\n";*) raise Failure
    | Node (InfixNode (_, _, _, f, None, Some right), _) ->
      (*printf "InfixNode without left child\n";*) raise Failure
    | Node (InfixNode (_, _, _, f, _, None), _) ->
      (*printf "InfixNode without right child\n";*) raise Failure
    | Leaf None -> (*printf "there is a leaf None\n";*) raise Failure
    | Leaf (Some _) -> (*printf "there is a leaf not zipped up\n";*) raise Failure
;;

(* fold : ('a -> 'b -> 'c -> 'c) -> ('a, 'b) t -> 'c -> 'c 
   sort : ('a -> 'a -> int) -> 'a list -> 'a list
   (increasing, 0 = (=), 1 = (>), -1 = (<))
*)
let parse_primary (p: 'a parsingrule) : 'a parsetree -> ('a parsetree) parsingrule =
  fun t ->
    (
      fun pb ->
	let _ = whitespaces pb in
        let res = p pb in
	let _ = whitespaces pb in
	(*printf "parsed primary: ??\n";*)
        try
          insert_primary res t
        with
          | NoMatch -> raise NoMatch
    )
;;


let parse_prefix (op: 'a opparser) (t: 'a parsetree) :  ('a parsetree) parsingrule =
  let list = Hashtbl.fold (fun key (value1, value2) acc ->
    (key, value1, value2)::acc
  ) op.prefixes [] in
  let sorted_list = List.sort (fun (x1, y1, z1) (x2, y2, z2) -> 
    if String.length x1 < String.length x2 then (                                 
      if x1 = String.sub x2 (String.length x1) 0 then
        if String.length x1 = String.length x2 then 0 else 1
      else
        -1
    ) else (
      if x2 = String.sub x1 (String.length x2) 0 then
        if String.length x1 = String.length x2 then 0 else -1
      else
        1
    )
  ) list in
  let parser_list = List.map (fun (x, y, z) -> ( 
    (fun pb ->
      let _ = whitespaces pb in
      let () = notp op.reserved pb in
      let startp = cur_pos pb in
      let _ = keyword x () pb in
      let endp = cur_pos pb in
      let _ = whitespaces pb in
      (*printf "parsed prefix: %s\n" x;*)
      try
        insert_prefix (x, y, z (startp, endp)) t
      with
        | _ -> raise NoMatch
    )
  )
  ) sorted_list in
  foldp parser_list
;;

let parse_postfix (op: 'a opparser) (t: 'a parsetree) :  ('a parsetree) parsingrule =
  let list = Hashtbl.fold (fun key (value1, value2) acc ->
    (key, value1, value2)::acc
  ) op.postfixes [] in
  let sorted_list = List.sort (fun (x1, y1, z1) (x2, y2, z2) -> 
    if String.length x1 < String.length x2 then (                                 
      if x1 = String.sub x2 (String.length x1) 0 then
        if String.length x1 = String.length x2 then 0 else 1
      else
        -1
    ) else (
      if x2 = String.sub x1 (String.length x2) 0 then
        if String.length x1 = String.length x2 then 0 else -1
      else
        1
    )
  ) list in
  let parser_list = List.map (fun (x, y, z) -> ( 
    (fun pb ->
      let _ = whitespaces pb in
      let () = notp op.reserved pb in
      let startp = cur_pos pb in
      let _ = keyword x () pb in
      let endp = cur_pos pb in
      let _ = whitespaces pb in
      (*printf "parsed postfix: %s\n" x;*)
      try
        insert_postfix (x, y, z (startp, endp)) t
      with
        | _ -> raise NoMatch
    )
  )
  ) sorted_list in
  foldp parser_list
;;

let parse_infix (op: 'a opparser) (t: 'a parsetree) : ('a parsetree) parsingrule =
  let list = Hashtbl.fold (fun key (value1, value2, value3) acc ->
    (key, value1, value2, value3)::acc
  ) op.infixes [] in
  let sorted_list = List.sort (fun (x1, _, _, _) (x2, _, _, _) -> 
    if String.length x1 < String.length x2 then (                                 
      if x1 = String.sub x2 (String.length x1) 0 then
        if String.length x1 = String.length x2 then 0 else 1
      else
        -1
    ) else (
      if x2 = String.sub x1 (String.length x2) 0 then
        if String.length x1 = String.length x2 then 0 else -1
      else
        1
    )
  ) list in
  let parser_list = List.map (fun (x, y, z, w) ->  
    (fun pb ->
      let _ = whitespaces pb in
      let () = notp op.reserved pb in
      let startp = cur_pos pb in
      let _ = keyword x () pb in
      let endp = cur_pos pb in
      let _ = whitespaces pb in
      (*printf "parsed infix: %s\n" x;*)
      try
        insert_infix (x, y, z, w (startp, endp)) t
      with
        | _ -> raise NoMatch
    )
  ) sorted_list in
  foldp parser_list
;;


let rec opparse (op: 'a opparser) : 'a parsingrule =
  (fun pb -> 
    let parser1 = parse_primary ((tryrule (paren (opparse op))) <|> (tryrule op.primary)) in
    let parser2 = parse_prefix op in
    let parser3 = parse_infix op in
    let parser4 = parse_postfix op in
    let total_parser = fun (t: 'a parsetree) -> ((tryrule (parser1 t)) <|> (tryrule (parser2 t)) <|> (tryrule (parser3 t)) <|> (tryrule (parser4 t))) in
    let init_tree = Leaf None in
    let final_tree = fixpoint total_parser init_tree pb in
    let final_tree = (try 
			zip_up_parsetree_until_root final_tree
      with
	| _ -> (*printf "catastrophic: cannot zip up\n";*) raise NoMatch	 
    )
    in
    try
      tree_semantics final_tree
    with
      | _ -> (*printf "catastrophic: tree without semantics\n";*) raise NoMatch
  ) <!> "not a primary/infix/prefix formula"
;;

let line_stream_of_channel channel =
  Stream.from
    (fun _ ->
      try Some (input_line channel) with End_of_file -> None)

let stream_of_string s =
  Stream.from
    (fun x ->
      match x with
	| 0 -> Some s
	| _ -> None
    )

(* eos *)
let eos (pb: parserbuffer) : unit =
  try
    Stream.empty pb.inputstream
  with
    | Stream.Failure -> raise NoMatch


(* assert that pos1 contains pos2 *)
let pos_in (pos1: pos) (pos2: pos) : bool =
  let ((begin_line1, begin_col1), (end_line1, end_col1)) = pos1 in
  let ((begin_line2, begin_col2), (end_line2, end_col2)) = pos2 in
  (* the start of pos2 must be equal or after the start of pos1 *)
  ((begin_line2 > begin_line1) || (begin_line1 = begin_line2 && begin_col2 >= begin_col1))
  (* and the end of pos2 must be equal or before the end of pos 1*)
  && ((end_line2 < end_line1) || (end_line1 = end_line2 && end_col2 <= end_col1))

(* choose a position between two possibilities *)
let best_pos (p1: pos) (p2: pos) : pos =
  match p1, p2 with
    | _ when p1 = nopos -> p2
    | _ when p2 = nopos  -> p1
    | _ when pos_in p1 p2 -> p2
    | _ -> p1
