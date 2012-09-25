open Printf
open Libpprinter
open Libparser
open Extlist
open Parser
open Pprinter

open Calculus_kernel

(* the global parserbuffer *)
let global_parserbuffer : parserbuffer ref = ref (build_parserbuffer (Stream.of_list []))

let rec parse_interactive (defs: defs) (pb: parserbuffer) : term = begin
  (* an exact term *)
  tryrule (fun pb ->
    let () = whitespaces pb in
    let startpos = cur_pos pb in
    let () = whitespaces pb in
    let _ = word "exact" pb in
    let () = whitespaces pb in
    let te = parse_term defs startpos pb in
    te
  )
end pb

let init_interactive =
  (* we add the interactive oracle at the end of the list *)
  registered_oracles := !registered_oracles @ (fun defs ctxt var ty -> 
    (* we just modify the frame of the context, in order to have all bounded variables accessible by a fresh name *)
    printf "|frames| = %d\n" (List.length ctxt.bvs);
    let _, frames = List.fold_right (fun ({name = n; ty = ty } as frame) (ln, acc)  ->
      let n' = fresh_name_list ~basename:(if String.compare n "_" == 0 then "H" else n) ln in
      (n'::ln), {frame with name = n'}::acc
    ) ctxt.bvs ([], []) in
    (* build a ref of the context *)
    let ctxt' = ref { ctxt with bvs = frames } in
    (* as the substitution is lazy, we force the possible substitution on the goal type for it to be readable *)
    let s, f = conversion_hyps2subst ~dec_order:true ctxt.conversion_hyps in
    let s = append_substitution s (context2subst ctxt') in
    (* we show the goal *)
    printf "------------------------------------------\n";
    ignore(map_nth (fun i -> 
      let i' = i - 1 in
	printf "(%d) %s: %s\n" i' (bvar_name ctxt' i') (term2string ctxt' (term_substitution s (bvar_type ctxt' i')))
  ) (List.length !ctxt'.bvs));
    printf "------------------------------------------\n";
    let fvs = fv_term ty in
    let fvs = List.map (fun i -> 
      let (ty, te) = get_fvar ctxt' i in
      String.concat "" [string_of_int i; " : "; term2string ctxt' ty; " := "; match te with | None -> "??" | Some te -> term2string ctxt' te]
    ) (IndexSet.elements fvs) in
    printf "%s\n" (String.concat "\n" fvs);
    printf "------------------------------------------\n";
    printf "facts: %s\n" (conversion_hyps2string ctxt' (!ctxt'.conversion_hyps));
    printf "==========================================\n\n";
    printf "(%s) : %s\n\n" (match var with | None -> "?" | Some i -> string_of_int i) (term2string ctxt' (term_substitution s ty));
    (* we parse an answer. TODO: better way to manage the input parser *)
    let pb = !global_parserbuffer in
    try
      let res = tryrule (parse_interactive defs) pb in
      global_parserbuffer := pb;
      (* we return the proposed term *)
      Some res
    with
      | NoMatch -> None
  )::[];;

let env : env = {
  defs = Hashtbl.create 100;
  deps = Hashtbl.create 100;
};;

let type_simplification_strat = {
  beta = Some BetaStrong;
  delta = Some DeltaWeak;
  iota = true;
  zeta = true;
  eta = true;
}


let process_definition (def: definition) : unit =
  let ctxt = ref empty_context in
  if !mk_trace then trace := [];
  let time_start = Sys.time () in
  (* initialization of a few globals *)
  unmatched_pattern := [];
  registered_calls := [];
  (* *)
  match def with
    | DefSignature (n, ty) -> 	
      let ty = (
	try 
	  match Hashtbl.find env.defs n with
	    | _ -> raise (PoussinException (FreeError (
	      String.concat "" ["term "; n; " is already defined"]
	    )))
	with
	  | Not_found -> typeinfer env.defs ctxt ty
      ) in
      let ty = typecheck env.defs ctxt ty (type_ (UName "")) in
      let [ty] = flush_fvars env.defs ctxt [ty] in 
      Hashtbl.add env.defs n (Axiom ty);
      let time_end = Sys.time () in
      printf "processed in %g sec.\n" (time_end -. time_start); flush stdout; 
      printf "Signature %s: %s\n\n" n (term2string ctxt ty);  flush stdout
    | DefInductive (n, ty) -> 	
      let ty = (
	try 
	  match Hashtbl.find env.defs n with
	    | Axiom ty' -> 
	      let ty = typecheck env.defs ctxt ty (type_ (UName "")) in
	      unification env.defs ctxt ty ty' 
	    | _ -> raise (PoussinException (FreeError (
	      String.concat "" ["term "; n; " is already defined"]
	    )))
	with
	  | Not_found -> typeinfer env.defs ctxt ty
      ) in
      let [ty] = flush_fvars env.defs ctxt [ty] in 
      Hashtbl.add env.defs n (Inductive ([], ty));
      let time_end = Sys.time () in
      printf "processed in %g sec.\n" (time_end -. time_start); flush stdout; 
      printf "Inductive %s: %s\n\n" n (term2string ctxt ty); flush stdout 
    | DefConstructor (n, ty) -> 
      (* typecheck the constructor type *)
      let ty = (
	try 
	  match Hashtbl.find env.defs n with
	    | Axiom ty' -> 
	      let ty = typecheck env.defs ctxt ty (type_ (UName "")) in
	      unification env.defs ctxt ty ty' 
	    | _ -> raise (PoussinException (FreeError (
	      String.concat "" ["term "; n; " is already defined"]
	    )))
	with
	  | Not_found -> typeinfer env.defs ctxt ty
      ) in
      (* flush free vars *)
      let [ty] = flush_fvars env.defs ctxt [ty] in 
      (* ensure that conclusion head is an Inductive *)
      let hd = app_head (snd (destruct_forall ty)) in
      let ind = 
	match hd.ast with
	  | Cste n -> ignore(get_inductive env.defs n); n
	  | _ -> raise (PoussinException (FreeError (
	      String.concat "" ["constructor conclusion head is not an Inductive"]
	    ))) in
      (* next ensure that the inductive does not appear negatively *)
      if neg_occur_cste ty ind then raise (PoussinException (FreeError (
	String.concat "" ["constructor type has a negative occurence of the Inductive"]
      )));
      (* everything is ok, add the constructor and update the type *)      
      Hashtbl.add env.defs n (Constructor (ind, ty));
      let Inductive (lst, ty) = Hashtbl.find env.defs ind in
      Hashtbl.add env.defs ind (Inductive (lst @ [n], ty));
      let time_end = Sys.time () in
      printf "processed in %g sec.\n" (time_end -. time_start); flush stdout; 
      printf "Constructor %s: %s\n\n" n (term2string ctxt ty); flush stdout
    | DefDefinition (n, te) -> 
      let te = (
	try 
	  match Hashtbl.find env.defs n with
	    | Axiom ty -> 
	      typecheck env.defs ctxt te ty		
	    | _ -> raise (PoussinException (FreeError (
	      String.concat "" ["term "; n; " is already defined"]
	    )))
	with
	  | Not_found -> typeinfer env.defs ctxt te
      ) in
      let [te] = flush_fvars env.defs ctxt [te] in 
      let te = { te with annot = Typed (reduction_term env.defs ctxt type_simplification_strat (get_type te))} in
      Hashtbl.add env.defs n (Definition te);
      let time_end = Sys.time () in
      printf "processed in %g sec.\n" (time_end -. time_start); flush stdout; 
      printf "Definition %s := %s\n: %s \n\n" n (if true then (term2string ctxt te) else "...") (term2string ctxt (get_type te)); flush stdout
    | DefCompute te ->
      let te = typeinfer env.defs ctxt te in
      let [te] = flush_fvars env.defs ctxt [te] in 
      printf "Computation %s : %s := " (term2string ctxt te) (term2string ctxt (get_type te)); flush stdout;
      let te' = reduction_term env.defs ctxt
	{ beta = Some BetaWeak; delta = Some DeltaWeak; iota = true; zeta = true; eta = true }
	te in
      let time_end = Sys.time () in
      printf "%s\n" (term2string ctxt te'); flush stdout;
      printf "processed in %g sec.\n\n" (time_end -. time_start); flush stdout


let process_stream (str: string Stream.t) : unit  =
  let pb = build_parserbuffer str in
  global_parserbuffer := pb;
  let leftmost = cur_pos pb in
  try 
    ignore (
      let _ = many (fun pb ->
	let time_start = Sys.time () in
	let def = parse_definition env.defs leftmost pb in
	(*let () = 
	  match def with
	  | DefSignature (n, ty) -> printf "Inductive %s: %s\n\n" n (term2string (ref empty_context) ty)
	  | DefInductive (n, ty) -> printf "Inductive %s: %s\n\n" n (term2string (ref empty_context) ty)
	  | DefConstructor (n, ty) -> printf "Constructor %s: %s\n\n" n (term2string (ref empty_context) ty)
	  | DefDefinition (n, te) -> printf "Definition %s:= %s \n\n" n (term2string (ref empty_context) te)
	  in*)
	let time_end = Sys.time () in
	printf "parsed in %g sec.\n\n" (time_end -. time_start); flush stdout;
	process_definition def
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


let main = 
  if Array.length Sys.argv < 2 then
    process_stdin ()
  else 
    process_file Sys.argv.(1);;

init_interactive;;

main;;
