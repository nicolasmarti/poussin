open Printf
open Libpprinter
open Libparser
open Extlist

open Calculus_entry
open Interactive

let main = 
  if Array.length Sys.argv < 2 then
    process_stdin ()
  else 
    process_file Sys.argv.(1);;

init_interactive;;

main;;
