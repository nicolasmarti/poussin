open Calculus_def
open Calculus_misc
open Libpprinter
open Extlist

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

let pp_option = ref {show_implicit = true; 
		     show_indices = true; 
		     show_position = false; 
		     show_univ = false;
		    }

let verbatims (l: name list) = Verbatim (String.concat "" l)

(* transform a term into a box *)
let rec term2token (vars: name list) (te: term) (p: place): token =
  match te with

    | Universe (Type, _, _) -> Verbatim "Type"
    | Universe (Set, _, _) -> Verbatim "Set"
    | Universe (Prop, _, _) -> Verbatim "Prop"

    | Cste (_, name, _, _) -> Verbatim "Name"

    | Var (i, _, _) when i >= 0 -> Verbatim (List.nth vars i)
    | Var (i, _, _) when i < 0 -> verbatims ["?"; string_of_int (-i)]

    | AVar _ -> Verbatim "_"
    | TName (name, _, _) -> verbatims ["'"; name; "'"]

    | Lambda _ ->
      (* we embed in parenthesis if 
	 - embed as some arg 
	 - ??
      *)
      (
	match p with
	  | InArg Explicit -> withParen
	  | _ -> fun x -> x
      )
	(
	  (* first decompose the lambda *)
	  let lhs, rhs = destruct_lambda te in
	  
	  (* we traverse the list of quantification and compute:
	     1 the list of boxes of the arguments
	     2 the inner variables list
	  *)
	  let vars, lhs = 
	    fold_cont (fun (vars, acc) (((s, ty, n, p), _, _)::tl) ->
	      let s = 
		match s with
		  (* the variable does not appears in the rest -> we skip it *)
		  | _ when not (IndexSet.mem 0 (bv_term (construct_lambda tl rhs))) -> "_"
		  (* it appears, we give it a fresh name if already present *)
		  | _ -> (fresh_name_list ~basename:s vars)
	      in
	      (tl, 
	       (s::vars,
		acc @ 
		  [Space 1; (if n = Implicit then withBracket else withParen) (Box [Verbatim s; Space 1; Verbatim "::"; Space 1; term2token vars ty Alone])]
	       )
	      )
	    )
	      (vars, []) lhs in

	  (* for computing the r.h.s, we just need to consider the newly created list of var *)
	  let rhs = term2token vars rhs Alone in
	  Box ([Verbatim "\\"] @ lhs @ [ Space 1; Verbatim "->"; Space 1; rhs])
	)

    | Forall ((s, ty, nature, _), te, _, _) ->
      (* we embed in parenthesis if 
	 - embed as some arg 
	 - ??
      *)
      (
	match p with
	  | InArg Explicit -> withParen
	  | _ -> fun x -> x
      )
	(
	  (* the lhs of the ->*)
	  let s, lhs = 
	    (* mostly same as for Lambda
	    *)
	    match s with
	      | _ when not (IndexSet.mem 0 (bv_term te))->
		(* we only put brackets if implicit *)
		s, (if nature = Implicit then withBracket else fun x -> x) (term2token vars ty (InArg nature))
	      | _ -> 
		(* here we put the nature marker, and select a fresh name *)
		let s = (fresh_name_list ~basename:s vars) in
		s , 
		(if nature = Implicit then withBracket else withParen)
		  (Box [Verbatim s; Space 1; Verbatim "::"; Space 1; term2token vars ty Alone])
	  in 
	  (* for computing the r.h.s, we need to push a new frame *)
	  let rhs = term2token (s::vars) te Alone in
	  Box [lhs; Space 1; Verbatim "->"; Space 1; rhs]
	)


    | _ -> raise (Failure "term2token: NYI")



(* make a string from a term *)
let term2string (vars: name list) (te: term) : string =
  let token = term2token vars te Alone in
  let box = token2box token 80 2 in
  box2string box
