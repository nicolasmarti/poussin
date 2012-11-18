open Interp;;

let main = 
  if false then (
    if Array.length Sys.argv < 2 then
      process_stdin ()
    else 
      process_file Sys.argv.(1)
  ) else (
    if Array.length Sys.argv < 2 then
      process_stdin2 ()
    else 
      process_file2 Sys.argv.(1)
  );;

init_interactive;;

main;;
