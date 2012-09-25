open Libparser

open Calculus_parser
open Calculus_pprinter
open Calculus_def
open Calculus_substitution
open Calculus_misc
open Calculus_entry

open Printf
open Extlist

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
