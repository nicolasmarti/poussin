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
  oracle := (fun defs ctxt ty -> 
    let ctxt' = ref ctxt in
    let s, f = conversion_hyps2subst ~dec_order:true ctxt.conversion_hyps in
    let s = append_substitution s (context2subst ctxt') in
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

    (* *)
    let pb = !global_parserbuffer in
    let res = parse_interactive defs pb in
    global_parserbuffer := pb;
    res
  );;
