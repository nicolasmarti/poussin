open Printf
open Libpprinter
open Libparser

open Calculus_entry

let main = 
  if Array.length Sys.argv < 2 then
    process_stdin ()
  else 
    process_file Sys.argv.(1);;

main
