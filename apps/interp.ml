open Printf
open Libpprinter
open Libparser
open Extlist
open Parser
open Pprinter
open Def
open Calculus_kernel
open Fm

(* the global parserbuffer *)
let global_parserbuffer : parserbuffer ref = ref (build_parserbuffer (Stream.of_list []))

let rec parse_interactive (defs: defs) (pb: parserbuffer) : term Lazy.t = begin
  (* an exact term *)
  tryrule (fun pb ->
    let _ = whitespaces pb in
    let startpos = cur_pos pb in
    let _ = whitespaces pb in
    let _ = word "exact" pb in
    let _ = whitespaces pb in
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
      Some (Lazy.force res)
    with
      | NoMatch -> None
  )::[];;


type well_formness = {
  mutable terminating: bool;
  mutable total: bool;
  mutable positive: bool;
  mutable stratified: bool;
  mutable proof_irrelevance: bool;
}

type env = {
  defs: defs;
  decreasing: (name, int list) Hashtbl.t;
  wf_env: (name, well_formness) Hashtbl.t
}

let env : env = {
  defs = Hashtbl.create 100;
  decreasing = Hashtbl.create 100;
  wf_env = Hashtbl.create 100;
};;

let type_simplification_strat = {
  beta = Some BetaStrong;
  delta = Some DeltaWeak;
  iota = true;
  zeta = true;
  eta = true;
}

let processing_time : float ref = ref 0.0;;

(* well formness *)

(* totality *)
let totality_check () : unit =
  List.iter (fun (ctxt, p, te, ret_ty) ->
    let ctxt' = ref ctxt in
    let s, f = conversion_hyps2subst ~dec_order:true ctxt.conversion_hyps in
    let s = append_substitution s (context2subst ctxt') in
    let te = term_substitution s te in
    let ty = term_substitution s (get_type te) in
    raise (PoussinException (FreeError (
      String.concat "" ["error: missing pattern in\n\tmatch "; (term2string ctxt' te); " : "; (term2string ctxt' ty); " with\n\t| "; (pattern2string ctxt' p);" := ???\n\n"]
    )))
  ) !unmatched_pattern 

(* terminaison *)
let rec term_to_nexpr defs (te: term) : nexpr =
  match te.ast with
    | Cste c when is_irreducible defs te -> Ncons 1
    | App (_, args) when (is_irreducible defs (app_head te)) ->
      List.fold_right (fun (hd, n) acc ->
	Nplus (term_to_nexpr defs hd, acc)
      ) args (Ncons 1)
    | Var i -> Nvar (String.concat "" ["@"; string_of_int i])

let terminaison_check n env : unit =
  (* first we filter the registered_calls *)
  let lst = List.filter (fun (_, n', _) ->
    match Hashtbl.find env.defs n' with
      | Axiom _ when String.compare n n' = 0 -> true
      | Axiom _ -> 
	printf "warning: No recursive calls to undefined term yet supported"; false
	  (*raise (PoussinException (FreeError "No recursive calls to undefined term yet supported"))*)
      | _ -> false
  ) !registered_calls in
  (* then we grab the decreasing arguments of decreasing in n *)
  let dec = 
    try 
      Hashtbl.find env.decreasing n 
    with
      | _ -> 
	printf "warning: No decreasing arguments"; []
	  (*raise (PoussinException (FreeError "No decreasing arguments"))*)
  in
  if List.length lst != 0 && List.length dec != 0 then (
    List.iter (fun (ctxt, n, args) ->
      printf "checking:\n%s|-\n%s\n\n" (ctxt2string (ref ctxt)) (term2string (ref ctxt) (app_ (cste_ n) args));
      (* first build hypothesis from conversion hyps *)
      let hyps = List.fold_right (fun (te1, te2) acc -> 
	try
	  Band (acc, Beq (term_to_nexpr env.defs te1, term_to_nexpr env.defs te2)) 
	with
	  | _ -> acc
      ) ctxt.conversion_hyps BTrue in
      (* we build the needed condition *)
      let ccl = Blt (
	(* the sum of rec. call args *)
	List.fold_right (fun hd acc -> Nplus (acc, term_to_nexpr env.defs hd)) (List.map (fun i -> fst (List.nth args i)) dec) (Ncons 0),
	(* the sum of the vars *)
	List.fold_right (fun hd acc -> Nplus (acc, Nvar (String.concat "" ["@"; string_of_int hd]))) (List.map (fun i -> List.length ctxt.bvs - i - 1) dec) (Ncons 0)	  
      ) in
      
      (* final formula *)
      let f = bimpl hyps ccl in
      printf "formula := %s\n" (bexpr2string f);
      if fm_dp f then
	printf "terminaison checked!\n\n"
      else
	printf "terminaison checking failed!\n\n"
    ) lst
  )

(* processing definitions *)

let process_signature env n ty : term =
  (* initialization of a few globals *)
  unmatched_pattern := [];
  registered_calls := [];
  let ctxt = ref empty_context in
  (* typecheck the type *)
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

  (* some extra check *)
  assert (List.length !ctxt.bvs = 0);

  (* well-formness *)
  totality_check ();
  terminaison_check n env;

  (* updating the env *)
  Hashtbl.add env.defs n (Axiom ty);
  ty

let process_constructor env n ty ind : term =
  (* initialization of a few globals *)
  unmatched_pattern := [];
  registered_calls := [];
  let ctxt = ref empty_context in
  (* typecheck the type *)
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
  
  (* some extra check *)
  assert (List.length !ctxt.bvs = 0);

  (* well-formness *)
  totality_check ();
  terminaison_check n env;

  (* ensure that conclusion head is an Inductive *)
  let hd = app_head (snd (destruct_forall ty)) in
  (match hd.ast with
      | Cste n when String.compare n ind = 0 -> ()
      | _ -> raise (PoussinException (FreeError (
	String.concat "" ["constructor conclusion head is not the Inductive "; ind]
      )))
  );
  
  ty

let process_inductive env n ty cstors: term * (name * term) list =
  (* initialization of a few globals *)
  unmatched_pattern := [];
  registered_calls := [];
  let ctxt = ref empty_context in
  (* typecheck the type *)
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

  (* some extra check *)
  assert (List.length !ctxt.bvs = 0);

  (* well-formness *)
  totality_check ();
  terminaison_check n env;

  (* updating the env *)
  Hashtbl.add env.defs n (Inductive ([], ty));

  try
  (* then trying to typecheck all the constructors *)
    let cstors = List.map (fun (n', ty) ->
      (n', process_constructor env n' ty n)
    ) cstors in

  (* everything is ok, add the constructor and update the type *)      
    List.iter (fun (n', ty) -> 
      Hashtbl.add env.defs n' (Constructor (n, ty))
    ) cstors;

  (* update the inductive def in the env *)
  Hashtbl.replace env.defs n (Inductive (List.map fst cstors, ty));

  ty, cstors

  with
    | err -> 
      Hashtbl.remove env.defs n;
      raise err

let process_definition env n te : term =
  (* initialization of a few globals *)
  unmatched_pattern := [];
  registered_calls := [];
  let ctxt = ref empty_context in
      (* typecheck the term *)
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

  (* some extra check *)
  assert (List.length !ctxt.bvs = 0);

  (* well-formness *)
  totality_check ();
  terminaison_check n env;
  
  let te = { te with annot = Typed (reduction_term env.defs ctxt type_simplification_strat (get_type te))} in
  Hashtbl.add env.defs n (Definition te);
  te

let process_definition (def: definition) : unit =
  if !mk_trace then trace := [];
  let time_start = Sys.time () in
  (* *)
  (match def with
    | DefSignature (n, ty) -> 	
      let ty = process_signature env n ty in
      let time_end = Sys.time () in
      processing_time := !processing_time +. (time_end -. time_start);
      printf "processed in %g sec.\n" (time_end -. time_start); flush stdout; 
      printf "%s\n\n" (definition2string (DefSignature (n, ty)) (ref empty_context));  flush stdout

    | DefInductive (n, ty, cstors) -> 	
      let ty, cstors = process_inductive env n ty cstors in
      let time_end = Sys.time () in
      processing_time := !processing_time +. (time_end -. time_start);
      printf "processed in %g sec.\n" (time_end -. time_start); flush stdout; 
      printf "%s\n\n" (definition2string (DefInductive (n, ty, cstors)) (ref empty_context)); flush stdout

    | DefDefinition (n, te) -> 
      let te = process_definition env n te in
      let time_end = Sys.time () in
      processing_time := !processing_time +. (time_end -. time_start);
      printf "processed in %g sec.\n" (time_end -. time_start); flush stdout; 
      printf "%s\n\n" (definition2string (DefDefinition (n, te)) (ref empty_context)); flush stdout

    | DefDecreasing (n ,lst) ->
      Hashtbl.replace env.decreasing n lst;
      let time_end = Sys.time () in
      processing_time := !processing_time +. (time_end -. time_start);
      printf "processed in %g sec.\n" (time_end -. time_start); flush stdout; 
      printf "%s\n\n" (definition2string (DefDecreasing (n, lst)) (ref empty_context)); flush stdout
   
    | DefCompute te ->
      let ctxt = ref empty_context in
      let te = typeinfer env.defs ctxt te in
      let [te] = flush_fvars env.defs ctxt [te] in 
      printf "Computation %s : %s := " (term2string ctxt te) (term2string ctxt (get_type te)); flush stdout;
      let te' = reduction_term env.defs ctxt
	{ beta = Some BetaWeak; delta = Some DeltaWeak; iota = true; zeta = true; eta = true }
	te in
      let time_end = Sys.time () in
      processing_time := !processing_time +. (time_end -. time_start);
      printf "%s\n" (term2string ctxt te'); flush stdout;
      printf "processed in %g sec.\n\n" (time_end -. time_start); flush stdout
  )

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
	process_definition (Lazy.force def);
	Lazy.lazy_from_val ()
      ) pb in
      let _ = eos pb in
      printf "total processing time in %g sec.\n\n" !processing_time; flush stdout;
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

let parse_process_term str =
  let lines = stream_of_string str in
  let pb = build_parserbuffer lines in
  global_parserbuffer := pb;
  let leftmost = cur_pos pb in
  Lazy.force (parse_term env.defs leftmost pb);;

let parse_process_definition str =
  let lines = stream_of_string str in
  process_stream lines
;;

let main = 
  if Array.length Sys.argv < 2 then
    process_stdin ()
  else 
    process_file Sys.argv.(1);;

init_interactive;;

main;;
