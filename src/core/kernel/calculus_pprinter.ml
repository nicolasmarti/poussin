open Calculus_def
open Calculus_misc
open Calculus_parser

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
  show_type: bool;
}

let pp_option = ref {show_implicit = true; 
		     show_indices = true; 
		     show_position = false; 
		     show_univ = false;
		     show_type = false;
		    }

let verbatims (l: name list) = Verbatim (String.concat "" l)

(* transform a term into a box *)
let rec term2token (vars: name list) (te: term) (p: place): token =
  match get_term_typeannotation te with 
    | Typed ty when !pp_option.show_type ->
      Box [Verbatim "(";
	   term2token vars (set_term_noannotation te) Alone; Space 1;
	   Verbatim "::"; Space 1;
	   term2token vars ty Alone;
	   Verbatim ")"
	  ]

    | Annotation ty when !pp_option.show_type ->
      Box [Verbatim "(";
	   term2token vars (set_term_noannotation te) Alone; Space 1;
	   Verbatim ":?:"; Space 1;
	   term2token vars ty Alone;
	   Verbatim ")"
	  ]

    | TypedAnnotation ty when !pp_option.show_type ->
      Box [Verbatim "(";
	   term2token vars (set_term_noannotation te) Alone; Space 1;
	   Verbatim ":?:"; Space 1;
	   term2token vars ty Alone;
	   Verbatim ")"
	  ]

    | _ ->
  match te with

    | Universe (Type, _, _) -> Verbatim "Type"
    | Universe (Set, _, _) -> Verbatim "Set"
    | Universe (Prop, _, _) -> Verbatim "Prop"

    | Cste (name, _, _, _) -> Verbatim name

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
	  | InArg Explicit | InApp -> withParen
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
		  | _ when not (IndexSet.mem 0 (bv_term (construct_lambda tl rhs))) -> s
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

    | Forall ((s, ty, nature, _), te, _, _, _) ->
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

    | Let ((s, te1, _), te2, _, _, _) ->
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
	    (* here we select a fresh name *)
	    let s = (fresh_name_list ~basename:s vars) in
	    s , (Box [Verbatim s; Space 1; Verbatim ":= "; Space 1; term2token vars te1 Alone; Space 1; Verbatim "in"])
	  in 
	  (* for computing the r.h.s, we need to push a new frame *)
	  let rhs = term2token (s::vars) te2 Alone in
	  Box [lhs; Space 1; rhs]
	)

    | App (te, args, _, _, _) ->
      (* we only embed in parenthesis if
	 - we are an argument of an application
      *)
      (match p with
	| InArg Explicit -> withParen
	| _ -> fun x -> x
      ) (
	(* simply compute the list of token for the args *)
	let args = List.map (fun (te, n) -> 
	  (if n = Implicit then withBracket else (fun x -> x))
	  (term2token vars te (InArg n))) 
	  (if !pp_option.show_implicit then args else List.filter (fun (_, nature) -> nature = Explicit) args) in
	(* the token for the function *)
	let te = term2token vars te InApp in
	(* put it all together *)
	Box (intercalate (Space 1) (te::args))
       )

    | Match (te, eqs, _, _, _) ->
      (match p with
	| InArg Explicit -> withParen
	| InApp -> withParen
	| InNotation _ -> withParen
	| _ -> fun x -> x
      ) (
	
	Box [
	  (* tthe tokens for the math ... with *)
	  Verbatim "match"; Space 1; term2token vars te Alone; Space 1; Verbatim "with"; Newline;
	  (* the tokens for the cases *)
	  Box (intercalate Newline (List.map (fun (ps, te) ->
	    Box ([Verbatim "|"; Space 1; patterns2token vars ps Alone; Space 1; Verbatim ":="; Space 1; term2token (List.rev (patterns_vars ps) @ vars) te Alone ])
	  ) eqs
	  )
	  )	  
	]
       )


    | _ -> raise (Failure "term2token: NYI")

and patterns2token (vars: name list) (patterns: pattern list) (p: place) : token =
  Box (intercalates [Space 1; Verbatim "|"; Space 1] (List.map (fun p ->
    pattern2token vars p Alone
  ) patterns ))

and pattern2token (vars: name list) (pattern: pattern) (p: place) : token =
  match pattern with
    | PAvar _ -> Verbatim "_"
    | PName s -> Verbatim s
    | PCstor (n, args) ->
      (match p with
	| InArg Explicit -> withParen
	| _ -> fun x -> x
      ) (
	(* simply compute the list of token for the args *)
	let args = List.map (fun (te, n) -> 
	  (if n = Implicit then withBracket else (fun x -> x))
	  (pattern2token vars te (InArg n))
	) (if !pp_option.show_implicit then args else List.filter (fun (_, nature) -> nature = Explicit) args) in
	(* the token for the function *)
	let te = term2token vars (Cste (n, NoAnnotation, NoPosition, true)) InApp in
	(* put it all together *)
	Box (intercalate (Space 1) (te::args))
       )
	    

let context2namelist (ctxt: context ref): name list =
  List.map (fun f -> f.name) !ctxt.bvs

(* make a string from a term *)
let term2string (ctxt: context ref) (te: term) : string =
  let token = term2token (context2namelist ctxt) te Alone in
  let box = token2box token 80 2 in
  box2string box

let rec definition2token (def: definition) (ctxt: context ref): token =
  match def with
    | DefSignature (n, ty) ->
      Box [Verbatim "Signature"; Space 1; Verbatim n; Space 1; Verbatim ":"; Space 1; term2token (context2namelist ctxt) ty Alone]
    | DefDefinition (n, te) ->
      Box [Verbatim "Definition"; Space 1; Verbatim n; Space 1; Verbatim ":="; Space 1; term2token (context2namelist ctxt) te Alone]
    | DefInductive (n, ty) ->
      Box [Verbatim "Inductive"; Space 1; Verbatim n; Space 1; Verbatim ":"; Space 1; term2token (context2namelist ctxt) ty Alone]
    | DefConstructor (n, ty) ->
      Box [Verbatim "Constructor"; Space 1; Verbatim n; Space 1; Verbatim ":"; Space 1; term2token (context2namelist ctxt) ty Alone]

let definition2string (def: definition) (ctxt: context ref): string =
  let token = definition2token def ctxt in
  let box = token2box token 80 2 in
  box2string box

let substitution2token (ctxt: context ref) (s: substitution) : token =
  Box ([Verbatim "{"] @
       intercalates [Verbatim ","; Space 1]
       (List.map ( fun (i, te) ->
	 Box [verbatims [string_of_int i; "("; term2string ctxt (var_ i); ") |-> "];
	      term2token (context2namelist ctxt) te Alone]
	) (IndexMap.bindings s)) @
       [Verbatim "}"])
      
let substitution2string (ctxt: context ref) (s: substitution) : string =
  let token = substitution2token ctxt s in
  let box = token2box token 80 2 in
  box2string box

let poussin_error2token (err: poussin_error) : token =
  match err with
    | FreeError s -> Verbatim s
    | Unshiftable_term _ -> Verbatim "Unshiftable_term"
    | UnknownCste s -> verbatims ["UnknownCste: "; s]
    | NoUnification (ctxt, te1, te2) -> 
      Box [Verbatim "NoUnification between"; Newline; 
	   term2token (context2namelist (ref ctxt)) te1 Alone; Newline; 
	   term2token (context2namelist (ref ctxt)) te2 Alone; Newline]

    | NoNatureUnification  _ -> Verbatim "NoNatureUnification"
    | UnknownUnification (ctxt, te1, te2) -> 
      Box [Verbatim "UnknownUnification between"; Newline; 
	   term2token (context2namelist (ref ctxt)) te1 Alone; Newline; 
	   Verbatim " And "; Newline;
	   term2token (context2namelist (ref ctxt)) te2 Alone; Newline]
    | NegativeIndexBVar  _ -> Verbatim "NegativeIndexBVar"
    | UnknownBVar  _ -> Verbatim "UnknownBVar"
    | UnknownFVar _ -> Verbatim "UnknownFVar"
    | NotInductiveDestruction _ -> Verbatim "NotInductiveDestruction"
	
let poussin_error2string (err: poussin_error) : string =
  let token = poussin_error2token err in
  let box = token2box token 80 2 in
  box2string box

let trace2token (trace: ty_action list) : token =
  Box (
    intercalates
      [Newline;Verbatim "-----------------------"; Newline]
      (List.map (fun hd -> 
	match hd with
	  | TC (ctxt, te, ty) ->
	    Box [ term2token (context2namelist (ref ctxt)) te Alone; Space 1;
		  Verbatim ":?"; Space 1;
		  term2token (context2namelist (ref ctxt)) ty Alone
	    ]
	  | TI (ctxt, te) ->
	    Box [ term2token (context2namelist (ref ctxt)) te Alone; Space 1;
		  Verbatim ": ???"
	    ]
	  | U (ctxt, te, ty) ->
	    Box [ term2token (context2namelist (ref ctxt)) te Alone; Space 1;
		  Verbatim "=?="; Space 1;
		  term2token (context2namelist (ref ctxt)) ty Alone
	    ]
	  | Free s -> Verbatim s
	  | Reduction (ctxt, te) ->
	    Box [ term2token (context2namelist (ref ctxt)) te Alone; Space 1;
		  Verbatim " ===> ???"
	    ]

       ) (List.rev trace)
      )     
  )

let trace2string (trace: ty_action list) : string =
  let token = trace2token trace in
  let box = token2box token 150 2 in
  box2string box
