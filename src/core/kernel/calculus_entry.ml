open Printf
open Libpprinter
open Libparser

open Calculus_def
open Calculus_misc
open Calculus_substitution
open Calculus_engine

open Calculus_pprinter
open Calculus_parser

let defs = Hashtbl.create 100;;

let process_definition (def: definition) : unit =
  let ctxt = ref empty_context in
  if !mk_trace then trace := [];
  let time_start = Sys.time () in
  (* initialization of a few globals *)
  
  
  (* *)
  match def with
    | DefSignature (n, ty) -> 	
      let ty = (
	try 
	  match Hashtbl.find defs n with
	    | _ -> raise (PoussinException (FreeError (
	      String.concat "" ["term "; n; " is already defined"]
	    )))
	with
	  | Not_found -> typeinfer defs ctxt ty
      ) in
      let ty = typecheck defs ctxt ty (type_ (UName "")) in
      let [ty] = flush_fvars defs ctxt [ty] in 
      Hashtbl.add defs n (Axiom ty);
      let time_end = Sys.time () in
      printf "processed in %g sec.\n" (time_end -. time_start); flush stdout; 
      printf "Signature %s: %s\n\n" n (term2string ctxt ty);  flush stdout
    | DefInductive (n, ty) -> 	
      let ty = (
	try 
	  match Hashtbl.find defs n with
	    | Axiom ty' -> 
	      let ty = typecheck defs ctxt ty (type_ (UName "")) in
	      unification defs ctxt true ty ty' 
	    | _ -> raise (PoussinException (FreeError (
	      String.concat "" ["term "; n; " is already defined"]
	    )))
	with
	  | Not_found -> typeinfer defs ctxt ty
      ) in
      let [ty] = flush_fvars defs ctxt [ty] in 
      Hashtbl.add defs n (Inductive ([], ty));
      let time_end = Sys.time () in
      printf "processed in %g sec.\n" (time_end -. time_start); flush stdout; 
      printf "Inductive %s: %s\n\n" n (term2string ctxt ty); flush stdout 
    | DefConstructor (n, ty) -> 
      (* typecheck the constructor type *)
      let ty = (
	try 
	  match Hashtbl.find defs n with
	    | Axiom ty' -> 
	      let ty = typecheck defs ctxt ty (type_ (UName "")) in
	      unification defs ctxt true ty ty' 
	    | _ -> raise (PoussinException (FreeError (
	      String.concat "" ["term "; n; " is already defined"]
	    )))
	with
	  | Not_found -> typeinfer defs ctxt ty
      ) in
      (* flush free vars *)
      let [ty] = flush_fvars defs ctxt [ty] in 
      (* ensure that conclusion head is an Inductive *)
      let hd = head (snd (destruct_forall ty)) in
      let ind = 
	match hd with
	  | Cste (n, _, _, _) -> ignore(get_inductive defs n); n
	  | _ -> raise (PoussinException (FreeError (
	      String.concat "" ["constructor conclusion head is not an Inductive"]
	    ))) in
      (* next ensure that the inductive does not appear negatively *)
      if neg_occur_cste ty ind then raise (PoussinException (FreeError (
	String.concat "" ["constructor type has a negative occurence of the Inductive"]
      )));
      (* everything is ok *)
      Hashtbl.add defs n (Constructor (ind, ty));
      let time_end = Sys.time () in
      printf "processed in %g sec.\n" (time_end -. time_start); flush stdout; 
      printf "Constructor %s: %s\n\n" n (term2string ctxt ty); flush stdout
    | DefDefinition (n, te) -> 
      let te = (
	try 
	  match Hashtbl.find defs n with
	    | Axiom ty -> 
	      typecheck defs ctxt te ty		
	    | _ -> raise (PoussinException (FreeError (
	      String.concat "" ["term "; n; " is already defined"]
	    )))
	with
	  | Not_found -> typeinfer defs ctxt te
      ) in
      let [te] = flush_fvars defs ctxt [te] in 
      Hashtbl.add defs n (Definition te);
      let time_end = Sys.time () in
      printf "processed in %g sec.\n" (time_end -. time_start); flush stdout; 
      printf "Definition %s:= %s : %s \n\n" n (term2string ctxt te) (term2string ctxt (get_type te)); flush stdout
    | DefCompute te ->
      let te = typeinfer defs ctxt te in
      let [te] = flush_fvars defs ctxt [te] in 
      printf "Computation %s : %s := " (term2string ctxt te) (term2string ctxt (get_type te)); flush stdout;
      let te' = reduction_term defs ctxt
	{ beta = Some BetaWeak; delta = Some DeltaWeak; iota = true; zeta = true; eta = true }
	te in
      let time_end = Sys.time () in
      printf "%s\n" (term2string ctxt te'); flush stdout;
      printf "processed in %g sec.\n\n" (time_end -. time_start); flush stdout


let process_stream (str: string Stream.t) : unit  =
  let pb = build_parserbuffer str in
  let leftmost = cur_pos pb in
  try 
    ignore (
      many (fun pb ->
	let def = parse_definition defs leftmost pb in
	(*
	let () = 
	  match def with
	    | DefSignature (n, ty) -> printf "Inductive %s: %s\n\n" n (term2string (ref empty_context) ty)
	    | DefInductive (n, ty) -> printf "Inductive %s: %s\n\n" n (term2string (ref empty_context) ty)
	    | DefConstructor (n, ty) -> printf "Constructor %s: %s\n\n" n (term2string (ref empty_context) ty)
	    | DefDefinition (n, te) -> printf "Definition %s:= %s \n\n" n (term2string (ref empty_context) te)
	in
	*)	
	process_definition def
      ) pb
    )
  with
    | NoMatch -> 
      printf "parsing error: '%s'\n%s\n" (Buffer.contents pb.bufferstr) (errors2string pb); flush Pervasives.stdout;
      raise Pervasives.Exit
    | Failure s -> 
      printf "error:\n%s\n" s;
      raise Pervasives.Exit
    | PoussinException err ->
      printf "poussin_error:\n%s\n%s\n" (trace2string !trace) (poussin_error2string err);
      raise Pervasives.Exit
;;

let process_string (str: string) : unit  =
  let lines = stream_of_string str in
  process_stream lines;;

let process_file (filename: string) : unit  =
  let chan = open_in filename in
  let lines = line_stream_of_channel chan in
  process_stream lines;;

let process_stdin () : unit =
  let lines = line_stream_of_channel stdin in
  process_stream lines;;
