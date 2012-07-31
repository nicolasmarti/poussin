open Calculus_def
open Libpprinter

let rec withParen (t: token) : token =
  Box [Verbatim "("; t; Verbatim ")"]

let rec withBracket (t: token) : token =
  Box [Verbatim "{"; t; Verbatim "}"]

(* a data structure to mark the place where the term is *)
type place = InNotation of op * int (* in the sndth place of the application to the notation with op *)
	     | InApp (* in the head of application *)
	     | InArg of nature (* as an argument (Explicit) *)
	     | InAlias  (* in an alias pattern *)
	     | Alone (* standalone *)

type pp_option = {
  show_implicit : bool;
  show_indices : bool;
  show_position : bool;
  show_univ : bool;
}

let pp_option = ref {show_implicit = true; show_indices = true; show_position = false}


