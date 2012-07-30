open Pycaml

(* module type for a language *)
module type Lang = sig
    
  (* the name of the language *)
  val name: string

  (* the error and exception, plus a format function *)
  type error
  exception Exception of error
      
  val error2string: error -> string

    
  (* the values and types *)
  type ty
  type value

  (* functions to create a string from types and values *)
  val ty2string: ty -> string
  val value2string: value -> string

  (* initialization *)
  val init: unit -> unit

  (* equality over two values *)
  val eq_value: value -> value -> bool

  (* marshalling from/to python*)
  val marshal_to_python: value -> pyobject option
  val marshal_from_python: pyobject -> value option

  (* application *)
  val apply: value -> value array -> value

  (* definition: parse and update the context
     return the number of consumed charaters
  *)
  val definition: string -> int * (string * value) array

  (* undo: undo previous definitions *)
  val undo_definition: unit -> unit

  (* eval: parse and eval *)
  val eval: string -> value


end
