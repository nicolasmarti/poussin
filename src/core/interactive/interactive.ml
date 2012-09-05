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
  oracles := !oracles @ (fun defs ctxt ty -> 
    (* build a ref of the context *)
    let ctxt' = ref ctxt in
    (* as the substitution is lazy, we force the possible substitution on the goal type for it to be readable *)
    let s, f = conversion_hyps2subst ~dec_order:true ctxt.conversion_hyps in
    let s = append_substitution s (context2subst ctxt') in
    (* we show the goal *)
    printf "------------------------------------------\n";
    ignore(map_nth (fun i -> 
      let i' = i - 1 in
      let n = (bvar_name ctxt' i') in
      if String.compare n "_" = 0 then
	()
      else
	printf "%s: %s\n" (bvar_name ctxt' i') (term2string ctxt' (term_substitution s (bvar_type ctxt' i')))
  ) (List.length !ctxt'.bvs));
    printf "------------------------------------------\n";
    printf "facts: %s\n" (conversion_hyps2string ctxt' f);
    printf "==========================================\n\n";
    printf "%s\n\n" (term2string ctxt' (term_substitution s ty));
    (* we parse an answer. TODO: better way to manage the input parser *)
    let pb = !global_parserbuffer in
    let res = parse_interactive defs pb in
    global_parserbuffer := pb;
    (* we return the proposed term *)
    Some res
  )::[];;
