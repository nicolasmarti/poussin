(*open Parser*)
open Libpprinter
open Extlist
open Calculus_def
open Calculus_misc
open Calculus_substitution
open Def

let rec withParen (t: token) : token =
  Box [Verbatim "("; t; Verbatim ")"]

let rec withBracket (t: token) : token =
  Box [Verbatim "{"; t; Verbatim "}"]

let rec withSquareBracket (t: token) : token =
  Box [Verbatim "["; t; Verbatim "]"]

(* a data structure to mark the place where the term is *)
type place =  InApp (* in the head of application *)
	     | InArg of nature (* as an argument (Explicit) *)
	     | InAlias  (* in an alias pattern *)
	     | Alone (* standalone *)

type pp_option = {
  mutable show_implicit : bool;
  mutable show_indices : bool;
  mutable show_position : bool;
  mutable show_univ : bool;
  mutable show_type: bool;
  mutable show_prop: bool;
}

let pp_option = {show_implicit = false; 
		 show_indices = false; 
		 show_position = false; 
		 show_univ = false;
		 show_type = false;
		 show_prop = false;
		}

let verbatims (l: name list) = Verbatim (String.concat "" l)

(* transform a term into a box *)
let rec term2token (vars: name list) (te: term) (p: place): token =
  let ty = get_term_typeannotation te in
  match ty with 
    | Typed ({ ast = _; annot = Typed { ast = Universe (Prop, _); _}; _ } as ty) when not pp_option.show_prop ->
      Box [Verbatim "(_: "; 
	   term2token vars ty Alone;
	   Verbatim ")"
	  ]
    | Typed ty when pp_option.show_type ->
      Box [Verbatim "(";
	   term2token vars (set_term_noannotation te) Alone; Space 1;
	   Verbatim ":"; Space 1;
	   term2token vars ty Alone;
	   Verbatim ")"
	  ]

    | Annotation ty when pp_option.show_type ->
      Box [Verbatim "(";
	   term2token vars (set_term_noannotation te) Alone; Space 1;
	   Verbatim ":?:"; Space 1;
	   term2token vars ty Alone;
	   Verbatim ")"
	  ]

    | TypedAnnotation ty when pp_option.show_type ->
      Box [Verbatim "(";
	   term2token vars (set_term_noannotation te) Alone; Space 1;
	   Verbatim ":?:"; Space 1;
	   term2token vars ty Alone;
	   Verbatim ")"
	  ]

    | _ ->
  match te.ast with
    | Universe (Type, _) -> Verbatim "Type"
    | Universe (Set, _) -> Verbatim "Set"
    | Universe (Prop, _) -> Verbatim "Prop"

    | Cste name -> verbatims [name]

    | Var i when i >= 0 -> (
      try
	verbatims ([List.nth vars i] @ (if pp_option.show_indices then ["("; string_of_int i ;")"] else []))
      with | _ -> verbatims ["!"; string_of_int i]
    )
    | Var i when i < 0 -> verbatims ["?"; string_of_int (-i)]

    | AVar -> Verbatim "_"
    | TName name -> (*verbatims ["'"; name; "'"]*) Verbatim name

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
	    fold_cont (fun (vars, acc) (((s, ty, n), _, _)::tl) ->
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
		  [Space 1; (match n with | Implicit -> withBracket | _ -> withParen) (Box [Verbatim s; Space 1; Verbatim ":"; Space 1; term2token vars ty Alone])]
	       )
	      )
	    )
	      (vars, []) lhs in

	  (* for computing the r.h.s, we just need to consider the newly created list of var *)
	  let rhs = term2token vars rhs Alone in
	  Box ([Verbatim "\\"] @ lhs @ [ Space 1; Verbatim "->"; Space 1; rhs])
	)

    | Forall ((s, ty, nature), te) ->
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
		s, (match nature with | Implicit -> withBracket | _ -> fun x -> x) (term2token vars ty (InArg nature))
	      | _ -> 
		(* here we put the nature marker, and select a fresh name *)
		let s = (fresh_name_list ~basename:s vars) in
		s , 
		(match nature with | Implicit -> withBracket | _ -> withParen)
		  (Box [Verbatim s; Space 1; Verbatim ":"; Space 1; term2token vars ty Alone])
	  in 
	  (* for computing the r.h.s, we need to push a new frame *)
	  let rhs = term2token (s::vars) te Alone in
	  Box [lhs; Space 1; Verbatim "->"; Space 1; rhs]
	)

    | Let ((s, te1), te2) ->
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
	    s , (Box [Verbatim "let"; Space 1; Verbatim s; Space 1; Verbatim ":= "; Space 1; term2token vars te1 Alone; Space 1; Verbatim "in"])
	  in 
	  (* for computing the r.h.s, we need to push a new frame *)
	  let rhs = term2token (s::vars) te2 Alone in
	  Box [lhs; Space 1; rhs]
	)

    | App (te, args) ->
      (* we only embed in parenthesis if
	 - we are an argument of an application
      *)
      (match p with
	| InArg Explicit -> withParen
	| InArg _ -> withParen
	| _ -> fun x -> x
      ) (
	(* simply compute the list of token for the args *)
	let args = List.map (fun (te, n) -> 
	  (match n with | Implicit -> withBracket | _ -> fun x -> x)
	  (term2token vars te (InArg n))) 
	  (if pp_option.show_implicit then args else List.filter (fun (_, nature) -> nature = Explicit) args) in
	(* the token for the function *)
	let te = term2token vars te InApp in
	(* put it all together *)
	Box ((*[Verbatim "["] @*) (intercalate (Space 1) (te::args))(* @ [Verbatim "]"]*))
       )

    | Match (te, eqs) ->
      (match p with
	| InArg Explicit -> withParen
	| InApp -> withParen
	| _ -> fun x -> x
      ) (
	
	Box [
	  (* tthe tokens for the math ... with *)
	  Verbatim "match"; Space 1; term2token vars te Alone; Space 1; Verbatim "with"; Newline;
	  (* the tokens for the cases *)
	  IBox (intercalate Newline (List.map (fun (ps, te) ->
	    Box ([Verbatim "|"; Space 1; patterns2token vars ps Alone; Space 1; Verbatim ":="; Space 1; term2token (List.rev (patterns_vars ps) @ vars) te Alone ])
	  ) eqs
	  )
	  ); Newline; Verbatim "end"	  
	]
       )

    | _ -> raise (failwith "term2token: NYI")

and patterns2token (vars: name list) (patterns: pattern list) (p: place) : token =
  Box (intercalates [Space 1; Verbatim "|"; Space 1] (List.map (fun p ->
    pattern2token vars p Alone
  ) patterns ))

and pattern2token (vars: name list) (pattern: pattern) (p: place) : token =
  match pattern with
    | PAvar _ -> Verbatim "_"
    | PName s -> Verbatim s
    | PCste c -> verbatims [(*"Cste@";*) c]
    | PApp (n, args) ->
      (match p with
	| InArg Explicit -> withParen
	| _ -> fun x -> x
      ) (
	(* simply compute the list of token for the args *)
	let args = List.map (fun (te, n) -> 
	  (match n with | Implicit -> withBracket | _ -> fun x -> x)
	  (pattern2token vars te (InArg n))
	) (if pp_option.show_implicit then args else List.filter (fun (_, nature) -> nature = Explicit) args) in
	(* the token for the function *)
	let te = term2token vars (cste_ n) InApp in
	(* put it all together *)
	Box ((*[Verbatim "["] @*) (intercalate (Space 1) (te::args))(* @ [Verbatim "]"]*))
       )
	    

let context2namelist (ctxt: context ref): name list =
  List.map (fun f -> f.name) !ctxt.bvs

(* make a string from a term *)
let term2string (ctxt: context ref) (te: term) : string =
  let token = term2token (context2namelist ctxt) te Alone in
  let box = token2box token 80 2 in
  box2string box

let pattern2string (ctxt: context ref) (p: pattern) : string =
  let token = pattern2token (context2namelist ctxt) p Alone in
  let box = token2box token 80 2 in
  box2string box

let rec definition2token (def: definition) (ctxt: context ref): token =
  match def with
    | DefSignature (n, ty) ->
      Box [Verbatim "Signature"; Space 1; Verbatim n; Space 1; Verbatim ":"; Space 1; term2token (context2namelist ctxt) ty Alone]
    | DefDefinition (n, te) ->
      Box [Verbatim "Definition"; Space 1; Verbatim n; Space 1; Verbatim ":="; Space 1; term2token (context2namelist ctxt) te Alone; Newline; Space 3; Verbatim ":"; Space 1; term2token (context2namelist ctxt) (get_type te) Alone]
    | DefInductive (n, ty, cstors) ->
      Box [Verbatim "Inductive"; Space 1; Verbatim n; Space 1; Verbatim ":"; Space 1; term2token (context2namelist ctxt) ty Alone; Space 1; Verbatim ":="; Newline;
	   Box (intercalate Newline (
	     List.map (fun (n, ty) ->
	       Box [Verbatim "|"; Space 1; Verbatim n; Space 1; Verbatim ":"; Space 1; term2token (context2namelist ctxt) ty Alone]
	     ) cstors
	   ))

	  ]
    | DefDecreasing (n, lst) ->
      Box [Verbatim "Decreasing"; Space 1; Verbatim n; Space 1; Verbatim "["; 
	   Box (intercalate (Verbatim ", ") (List.map (fun hd -> Verbatim (string_of_int hd)) lst));
	   Verbatim "]"]

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

	  | UNeg (ctxt, te, ty) ->
	    Box [ term2token (context2namelist (ref ctxt)) te Alone; Space 1;
		  Verbatim "=!="; Space 1;
		  term2token (context2namelist (ref ctxt)) ty Alone
	    ]

	  | Free s -> Verbatim s
	  | Reduction (ctxt, te, te') ->
	    Box [ term2token (context2namelist (ref ctxt)) te Alone; Space 1;
		  Verbatim " ===> ";
		  term2token (context2namelist (ref ctxt)) te' Alone
	    ]

       ) (List.rev trace)
      )     
  )

let trace2string (trace: ty_action list) : string =
  let token = trace2token trace in
  let box = token2box token 150 2 in
  box2string box

let conversion_hyps2token (ctxt: context ref) (conv: (term * term) list) : token =
  let s, f = conversion_hyps2subst ~dec_order:true !ctxt.conversion_hyps in
  let s = append_substitution s (context2subst ctxt) in
    Box (intercalates [Space 1; Verbatim "/\\"; Space 1]
	   (List.map (fun (hd1, hd2) ->
	     Box [ term2token (context2namelist ctxt) (term_substitution s hd1) Alone; Space 1;
	       Verbatim "==="; Space 1;
	       term2token (context2namelist ctxt) (term_substitution s hd2) Alone
	     ]
	    ) conv
	   )
    )

let conversion_hyps2string (ctxt: context ref) (conv: (term * term) list) : string =
  let token = conversion_hyps2token ctxt conv in
  let box = token2box token 150 2 in
  box2string box


let ctxt2token (ctxt: context ref) : token =
  let vars = Box (
    [Verbatim "------------------------------------"; Newline] @
      (List.concat (map_nth (fun i -> 
	[ Verbatim (bvar_name ctxt (i - 1)); Space 1; Verbatim ":"; Space 1; term2token (context2namelist ctxt) (bvar_type ctxt (i - 1)) Alone; Newline]
       )(List.length !ctxt.bvs))
      ) @ 
      [Verbatim "------------------------------------"; Newline] @
      (List.concat (List.map (fun (i, ty, te, n) -> 
	[ Verbatim (string_of_int i); (match n with | None -> Space 0; | Some n -> verbatims [" "; n] ); Space 1; Verbatim ":"; Space 1; term2token (context2namelist ctxt) ty Alone; Space 1; Verbatim ":="; Space 1; 
	  (match te with | None -> Verbatim "??" | Some te -> term2token (context2namelist ctxt) te Alone); 
	  Newline]
       ) !ctxt.fvs)
      )
  ) in
  Box [vars; conversion_hyps2token ctxt !ctxt.conversion_hyps; Newline; 
       Verbatim "------------------------------------"; Newline
      ]

let ctxt2string (ctxt: context ref) : string =
  let token = ctxt2token ctxt in
  let box = token2box token 150 2 in
  box2string box

let position2token (p: position) : token =
  Box (
    match p with
      | NoPosition -> []
      | Position (((startl, startc), (endl, endc)), _) ->
	[verbatims [string_of_int startl; ":"; string_of_int startc; " - "; string_of_int endl; ":"; string_of_int endc]]
  )

let rec poussin_error2token (err: poussin_error) : token =
  match err with
    | FreeError s -> Verbatim s
    | Unshiftable_term _ -> Verbatim "Unshiftable_term"
    | UnknownCste s -> verbatims ["UnknownCste: "; s]
    | NoUnification (ctxt, te1, te2) -> 
      let s, f = conversion_hyps2subst ~dec_order:true ctxt.conversion_hyps in
      let s = append_substitution s (context2subst (ref ctxt)) in
      let te1 = term_substitution s te1 in
      let te2 = term_substitution s te2 in
      Box [Verbatim "NoUnification between"; Newline; 
	   (*position2token (get_term_pos te1);*) Space 2; term2token (context2namelist (ref ctxt)) te1 Alone; Newline; 
	   Verbatim " And "; Newline;
	   (*position2token (get_term_pos te2);*) Space 2; term2token (context2namelist (ref ctxt)) te2 Alone; Newline;
	  Verbatim "under following conversion_hyps:"; Newline;
	  Space 2; conversion_hyps2token (ref ctxt) ctxt.conversion_hyps
	  ]

    | NoNatureUnification  _ -> Verbatim "NoNatureUnification"
    | UnknownUnification (ctxt, te1, te2) -> 
      let s, f = conversion_hyps2subst ~dec_order:true ctxt.conversion_hyps in
      let s = append_substitution s (context2subst (ref ctxt)) in
      let te1 = term_substitution s te1 in
      let te2 = term_substitution s te2 in
      Box [Verbatim "UnknownUnification between"; Newline; 
	   (*position2token (get_term_pos te1);*) Space 2; term2token (context2namelist (ref ctxt)) te1 Alone; Newline; 
	   Verbatim " And "; Newline;
	   (*position2token (get_term_pos te2);*) Space 2; term2token (context2namelist (ref ctxt)) te2 Alone; Newline;
	  Verbatim "under following conversion_hyps:"; Newline;
	  Space 2; conversion_hyps2token (ref ctxt) ctxt.conversion_hyps
	  ]
    | CsteNotConstructor n -> Verbatim "CsteNotConstructor"
    | CsteNotInductive n -> Verbatim "CsteNotInductive"
    | NegativeIndexBVar  _ -> Verbatim "NegativeIndexBVar"
    | UnknownBVar  _ -> Verbatim "UnknownBVar"
    | UnknownFVar _ -> Verbatim "UnknownFVar"
    | NotInductiveDestruction (ctxt, te) -> 
      let s, f = conversion_hyps2subst ~dec_order:true ctxt.conversion_hyps in
      let s = append_substitution s (context2subst (ref ctxt)) in
      let te = term_substitution s te in
      Box [Verbatim "NotInductiveDestruction: "; Newline; 
	   term2token (context2namelist (ref ctxt)) te Alone; Space 1; Verbatim ":"; Space 1; term2token (context2namelist (ref ctxt)) (get_type te) Alone; Newline]
    | InteractiveFailure ->
      Verbatim "failure in interactive mode"
    | CannotTypeCheck (ctxt, te, ty, err) ->
      let s, f = conversion_hyps2subst ~dec_order:true ctxt.conversion_hyps in
      let s = append_substitution s (context2subst (ref ctxt)) in
      let te = term_substitution s te in
      let ty = term_substitution s ty in
      Box [Verbatim "Cannot type Check"; Newline;
	   (*ctxt2token (ref ctxt); Newline;*)
	   position2token (get_term_pos te); Space 2; term2token (context2namelist (ref ctxt)) te Alone; Newline; 
	   Verbatim "with type: "; Newline; 
	   (*position2token (get_term_pos ty);*) Verbatim "    "; term2token (context2namelist (ref ctxt)) ty Alone; Newline; 
	    Verbatim "under following conversion_hyps:"; Newline;
	    Space 2; conversion_hyps2token (ref ctxt) ctxt.conversion_hyps;
	    Newline; Verbatim "reason: "; Newline;
	    poussin_error2token err
	  ]
      


let poussin_error2string (err: poussin_error) : string =
  let token = poussin_error2token err in
  let box = token2box token 80 2 in
  box2string box

