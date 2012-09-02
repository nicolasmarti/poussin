open Printf
open Libpprinter
open Libparser
open Extlist

open Calculus_def
open Calculus_misc
open Calculus_substitution
open Calculus_pprinter
open Calculus_entry

let main = 
  oracle := (fun defs ctxt ty -> 
    let ctxt' = ref ctxt in
    let s, f = conversion_hyps2subst ~dec_order:true ctxt.conversion_hyps in
    let s = append_substitution s (context2subst ctxt') in
    printf "------------------------------------------\n";
    ignore(map_nth (fun i -> 
      let n = (bvar_name ctxt' i) in
      if String.compare n "_" = 0 then
	()
      else
	printf "%s: %s\n" (bvar_name ctxt' i) (term2string ctxt' (term_substitution s (bvar_type ctxt' i)))
     ) (List.length !ctxt'.bvs - 1));
    printf "------------------------------------------\n";
    printf "facts: %s\n" (conversion_hyps2string ctxt' f);
    printf "==========================================\n\n";
    printf "%s\n\n" (term2string ctxt' (term_substitution s ty));
    raise (Failure "no oracle mode set")
  );
  if Array.length Sys.argv < 2 then
    process_stdin ()
  else 
    process_file Sys.argv.(1);;

main
