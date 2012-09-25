open Calculus_def
open Calculus_misc
open Calculus_substitution
open Calculus_pprinter
open Extlist
open Libparser
open Printf

open Fm

type beta_strength =
  | BetaStrong (* reduction under the quantifier*)
  | BetaWeak

type delta_strength =
  | DeltaStrong (* always unfold *)
  | DeltaWeak (* unfold a term only if the following reduction does not have lambdas or match *)
  | DeltaUWeak (* unfold a term only if the following reduction does not have lambdas or match *)

type reduction_strategy = {
  beta: beta_strength option;
  delta: delta_strength option;
  iota: bool; (* match reduction *)
  zeta: bool; (* let reduction *)
  eta: bool; (* not sure I will implement this one ... *)
}

let unification_strat = {
  beta = Some BetaWeak;
  delta = Some DeltaWeak;
  iota = true;
  zeta = true;
  eta = true;
}

let typeinfer_strat = {
  beta = Some BetaWeak;
  delta = Some DeltaWeak;
  iota = true;
  zeta = true;
  eta = true;
}

let simplification_strat = {
  beta = Some BetaWeak;
  delta = Some DeltaWeak;
  iota = false;
  zeta = false;
  eta = false;
}

(* this is a list of contexted unmatch patterns (with the destructed term type, and the desired return type) *)
let unmatched_pattern : (context * pattern * term * term) list ref = ref []
let print_unmatched_pattern = true

(* this is the list of all non irreducible name called *)
let registered_calls : (context * name * (term * nature) list) list ref = ref []
let print_registered_calls = false

let push_quantification (q: (name * term * nature)) (ctxt: context ref) : unit =
  let s, ty, n = q in
  ctxt := { !ctxt with
    bvs = {name = s; ty = shift_term ty 1; nature = n}::!ctxt.bvs;
    fvs = List.map (fun (i, ty, te) -> (i, shift_term ty 1, (match te with | None -> None | Some te -> Some (shift_term te 1)))) !ctxt.fvs;
    conversion_hyps = List.map (fun (hd1, hd2) -> (shift_term hd1 1, shift_term hd2 1)) !ctxt.conversion_hyps
  }

let rec context_add_substitution (defs: defs) (ctxt: context ref) (s: substitution) : unit =
  (* computes the needed shited substitution *)
  let ss = fst (mapacc (fun acc hd -> (acc, shift_substitution acc (-1))) s !ctxt.bvs) in
  let bvs = List.map2 (fun hd1 hd2 -> {hd1 with ty = term_substitution hd2 hd1.ty} ) !ctxt.bvs ss in
  let fvs = 
      List.map (fun (i, ty, te) -> 
	if IndexMap.mem i s then (
	match te with
	  | None -> (i, term_substitution s ty, Some (IndexMap.find i s))
	  | Some te -> (i, term_substitution s ty, Some (unification defs ctxt te (IndexMap.find i s)))
	) else (
	match te with
	  | None -> (i, term_substitution s ty, None)
	  | Some te -> (i, term_substitution s ty, Some (term_substitution s te))
	)
      ) !ctxt.fvs in
  ctxt := { !ctxt with fvs = fvs; bvs = bvs };
  (* we split the conv between those who contain/do not contain vars in the domain of the subtitution *)
  let untouched_conv, touched_conv = List.fold_right (fun (te1, te2) (untouched, touched) ->
    if IndexSet.is_empty (IndexSet.inter (substitution_vars s) (IndexSet.union (bv_term te1) (bv_term te2))) then ((te1, te2)::untouched, touched) else (untouched, (te1, te2)::touched)
  ) !ctxt.conversion_hyps ([], []) in
  (* just update the context *)
  ctxt := { !ctxt with conversion_hyps = untouched_conv };
  (* iter on the substituted conv, and adding them trough unification (thus possibly reducing them) *)
  List.iter (fun (te1, te2) -> 
    (* we substitute *)
    let te1' = term_substitution s te1 in
    let te2' = term_substitution s te2 in
    (* and try to unify both (gaining more precise knowledge, or aborting if the substitution introduce a false conversion) *)
    ignore(unification defs ctxt ~polarity:false te1' te2')
  ) touched_conv
  
and context_add_conversion (defs: defs) (ctxt: context ref) (te1: term) (te2: term) : unit =
  let s, _ = conversion_hyps2subst !ctxt.conversion_hyps in
  if not (IndexSet.is_empty (IndexSet.inter (substitution_vars s) (IndexSet.union (bv_term te1) (bv_term te2)))) then (
    (* if possible we rewrite the current substitutions given by the conversions *)
    let te1' = term_substitution s te1 in
    let te2' = term_substitution s te2 in  
    (* and we retry to to negatively unify them *)
    ignore (unification defs ctxt ~polarity:false te1' te2')
  ) else (
    (* otherwise , we just add them *)
    ctxt := { !ctxt with conversion_hyps = ((te1, te2)::(!ctxt.conversion_hyps)) }
  )


and flush_fvars (defs: defs) (ctxt: context ref) (tes: term list) : term list =
  (* we rewrite the conversion hypothesis in increasing order in the free vars *)
  let s, _ = conversion_hyps2subst ~dec_order:true !ctxt.conversion_hyps in
  let fvs = List.map (fun (i, ty, te) ->
    (i,
     term_substitution s ty,
     (match te with | None -> None | Some te -> Some (term_substitution s te)))
  ) !ctxt.fvs in  
  (* we rewrite all the terms *)
  let tes = List.fold_left (fun acc (i, ty, te) ->
    match te with
      | None -> acc
      | Some te -> List.map (fun te' -> term_substitution (IndexMap.singleton i te) te') acc
  ) tes fvs in
  (* update the context *)
  ctxt := {!ctxt with fvs = fvs};
  (* we compute the fvars of the terms *)
  let lfvs = List.fold_left (fun acc te -> 
    IndexSet.union acc (fv_term te)
  ) IndexSet.empty tes in  
  (* we sort the free variables *)
  let throw, keep = List.fold_right (fun ((i, ty, te) as var) (throw, keep) ->
    (* is the var to be considered (var 0 is in ty free var or we are at the root level) ? *)
    if IndexSet.mem 0 (bv_term ty) || List.length !ctxt.bvs = 0 then (
      (* yes, this variable is in the the terms free vars ? *)
      if IndexSet.mem i lfvs then (
	(* yes, we need to instantiate it *)
	match oracles_call defs ctxt ~var:(Some i) ty with
	  | None -> (* nothing there, we just raise an error *)
	    raise (PoussinException (FreeError "the oracles failed to infer a free variable"))
	  | Some _ as te -> (* we just return the answer of the oracles as the free variable value *)
	    ((i, ty, te)::throw, keep)
	
      ) else 
	(* no: we forget it*)
	(throw, keep)
    ) else (
	(* no: keep it *)
	(throw, var::keep)
    )
  ) !ctxt.fvs ([], []) in
  (* we rewrite all the terms *)
  let tes = List.fold_left (fun acc (i, ty, te) ->
    match te with
      | None -> acc
      | Some te -> List.map (fun te' -> term_substitution (IndexMap.singleton i te) te') acc
  ) tes throw in  
  (* update the context *)
  ctxt := {!ctxt with fvs = keep};
  tes

and pop_quantification (defs: defs) (ctxt: context ref) (tes: term list) : (name * term * nature) * term list =
  (* we flush the vars *)
  let tes = flush_fvars defs ctxt tes in
  (* we grab the remaining context and the popped frame *)
  let frame = List.hd (!ctxt.bvs) in
  (* we set the context *)
  ctxt := { !ctxt with 
    (* remove a frame *)
    bvs = List.tl !ctxt.bvs;
    (* shift free vars *)
    fvs = List.fold_right (fun (i, ty, te) acc ->
      try
	(i, shift_term ty (-1), 
	 (match te with
	   | None -> None
	   | Some te -> Some (shift_term te (-1))))::acc
      with
	| _ -> acc
    ) !ctxt.fvs []; 
    (* we shift the update version of the conversion_hyps *)
    conversion_hyps = 
      List.fold_left (fun acc (hd1, hd2) ->
	try 
	  acc @ (shift_term hd1 (-1), shift_term hd2 (-1))::[]
	with
	  | PoussinException (Unshiftable_term _) ->
	    acc
	      
      ) [] !ctxt.conversion_hyps;    
  };
  (* and returns the quantifier *)
  (frame.name, shift_term frame.ty (-1), frame.nature), tes  

and pop_quantifications (defs: defs) (ctxt: context ref) (tes: term list) (n: int) : (name * term * nature) list * term list =
  match n with
    | _ when n < 0 -> raise (PoussinException (FreeError "Catastrophic: negative n in pop_quantifications"))
    | 0 -> [], tes
    | _ ->
      let hd, tes = pop_quantification defs ctxt tes in
      let tl, tes = pop_quantifications defs ctxt tes (n-1) in
      hd::tl, tes

(* calls for oracles for a given type
   TODO: add parallelism
 *)
and oracles_call (defs: defs) (ctxt: context ref) ?(oracles: oracle list option = None) ?(var: index option = None) (ty: term) : term option =
  let res = fold_stop (fun () oracle ->
    try	     
      (* grab an answer from the oracle *)
      let te = oracle defs !ctxt var ty in
      (* do we have a result ?*)
      match te with
	| None -> (* nop, so try next one *) Left ()
	| Some te -> (* yep, look if the oracle's answer is correct *)
	  (* copy the context *)
	  let ctxt' = ref (!ctxt) in
	  (* typecheck it's untype version for the wanted type, and that if it is suppose to be some free var instantiation then it is consistent with the context *)
	  let te = typecheck defs ctxt' (untype_term te) ty in
	  let () = match var with
	    | None -> ()
	    | Some i -> context_add_substitution defs ctxt' (IndexMap.singleton i te)
	  in
	  (* return the context and the result *)
	  Right (!ctxt', te)
    with
      | PoussinException err -> 
	Left ()
  ) () (match oracles with | None -> !registered_oracles | Some lst -> lst) in
  match res with
    | Left () -> None
    | Right (ctxt', te) -> 
      (* modify the context *)
      ctxt := ctxt';
      Some te

(* typechecking, inference and reduction *)

and typecheck 
    (defs: defs)
    (ctxt: context ref)
    ?(polarity: bool = true)
    ?(coercion: bool = true)
    (te: term)
    (ty: term) : term =
  let te = 
    match get_term_typeannotation te with
      | Typed ty' ->
	te
      | Annotation ty' ->
	let ty' = typeinfer defs ctxt ~polarity:polarity ty' in
	let te = typeinfer defs ctxt ~polarity:polarity (set_term_typedannotation te ty') in
	te 
      | TypedAnnotation ty' ->
	let te = typeinfer defs ctxt ~polarity:polarity (set_term_typedannotation te ty') in
	te 
      | NoAnnotation ->
	let te = typeinfer defs ctxt ~polarity:polarity (set_term_typedannotation te ty) in
	te
  in
  try 
    ignore(unification defs ctxt ~polarity:polarity (get_type te) ty);
    te
  with
    (* only coercion on ground types *)
    | PoussinException err when coercion && IndexSet.is_empty (IndexSet.union (fv_term (get_type te)) (fv_term ty)) ->
      (* we where not able to unify the infered type and the desired type, let's ask to an oracle *)
      (* building a dummy variable *)
      let {ast = Var i; _} as f_ty = add_fvar ctxt in
      (* build a term of the application to the term *)
      let te' = typeinfer defs ctxt ~polarity:polarity (app_ f_ty ((te, Explicit)::[])) in
      (* unify: after that, the value of the free variable should be a function from the term to the desired type *)
      let _ = unification defs ctxt ~polarity:polarity te' ty in
      
      (* here we have two version of goal construction for the oracles 
	 1. we ask for the function directly (issue: this completely forgot the term te)
	 2. we ask for a let quantification of the function with value as te (issue: the oracle might give a term which does not contains te)
      *)
      if true then (
	
	(* we just change the Lambda, for a Forall, and we have our desired coercion type *)
	let Some {ast = Lambda (q, body); _} = fvar_subst ctxt i in
	let f_ty = typeinfer defs ctxt ~polarity:polarity (forall2_ q body) in
	match oracles_call defs ctxt f_ty  with
	  | None -> (* no term, return the same error *) raise (PoussinException err)
	  | Some f ->
	    (* we have a term which applied to te give a term of the proper type, we return it *)
	    app_ ~annot:(Typed ty) f ((te, Explicit)::[])
	      
      ) else (
	
	(* we get the quantification from the higher order unification *)
	let Some {ast = Lambda ((name, _, _), body); _} = fvar_subst ctxt i in
	let oracle_ty = let_ name te body in
	(* and ask the oracles for the term *)
	let oracle_ty = typeinfer defs ctxt ~polarity:polarity oracle_ty in
	match oracles_call defs ctxt oracle_ty with
	  | None -> (* no term, restore the context and return the same error *) 
	    raise (PoussinException err)
	  | Some te' ->
	    (* we have a term, we return it *)
	    te'
      )    


and typeinfer 
    (defs: defs)
    (ctxt: context ref)
    ?(polarity: bool = true)
    ?(in_app: bool = false)
    (te: term) : term =
  match get_term_typeannotation te with
    | Typed ty -> 
      (* we catch any use of cste *)
      let app_head_ = app_head te in
      let app_args_ = app_args te in
      (* is the head is reducible def -> we register it as a call *)
      if (not in_app) && is_reducible_def defs app_head_ then (
	let {ast = Cste c; _} = app_head_ in
	registered_calls := (!ctxt, c, app_args_)::!registered_calls;
	if print_registered_calls then printf "warning: registered call to reducible def (might require terminaison proof): %s\n" (term2string ctxt (app_ app_head_ app_args_))
      );      
      te
    | Annotation ty -> 
      let ty = typeinfer defs ctxt ~polarity:polarity ty in
      typecheck defs ctxt ~polarity:polarity (set_term_typedannotation te ty) ty		       
    | ty ->
      let mty = match ty with | NoAnnotation -> None | TypedAnnotation ty -> Some ty in
      let te' = (
	match te.ast with
	  | Universe _ -> te
	  | Cste n -> (
	    (* we register the call is needed *)
	    if (not in_app) && is_reducible_def defs te then (
	      registered_calls := (!ctxt, n, [])::!registered_calls;
	      if print_registered_calls then printf "warning: registered call to reducible def (might require terminaison proof): %s\n" (term2string ctxt te)
	    );      
	    match get_cste defs n with
	      | Inductive (_, ty) | Axiom ty | Constructor (_, ty) -> 
		{ te with annot = Typed ty }
	      | Definition te' -> 
		{ te with annot = Typed (get_type te') }
	  )

	  | Var i when i < 0 -> (
	    match fvar_subst ctxt i with
	      | None -> { te with annot = Typed (fvar_type ctxt i) }
	      | Some te -> te
	  )
	  | Var i when i >= 0 ->
	    { te with annot = Typed (bvar_type ctxt i) }

	  | AVar ->
	    add_fvar ~pos:te.tpos ctxt

	  | TName n -> (
	    let res = 
	    (* we first look for a variable *)
	    match var_lookup ctxt n with
	      | Some i -> 
		{ te with ast = Var i; annot = Typed (bvar_type ctxt i) }
	      | None -> 
		match get_cste defs n with
		  | Inductive (_, ty) | Axiom ty | Constructor (_, ty) -> 
		    { te with ast = Cste n; annot = Typed ty }
		  | Definition te -> 
		    { te with ast = Cste n; annot = Typed (get_type te) }
	    in
	    (* we register the call is needed *)
	    if (not in_app) && is_reducible_def defs res then (
	      let {ast = Cste n; _} = res in
	      registered_calls := (!ctxt, n, [])::!registered_calls;
	      if print_registered_calls then printf "warning: registered call to reducible def (might require terminaison proof): %s\n" (term2string ctxt te)
	    ); res

	  )

	  | Forall ((s, ty, n), body) ->
	    (* first let's be sure that ty :: Type *)
	    let ty = typecheck defs ctxt ~polarity:polarity ty (type_ (UName "")) in
	    (* we push the quantification *)
	    push_quantification (s, ty, n) ctxt;
	    (* we typecheck te :: Type *)
	    let body = typecheck defs ctxt ~polarity:polarity body (type_ (UName "")) in
	    (* we pop quantification *)
	    let q1, [body] = pop_quantification defs ctxt [body] in
	    (* and we returns the term with type Type *)
	    let res = { te with ast = Forall (q1, body); annot = Typed (type_ (UName "")) } in
	    res

	  | Lambda ((s, ty, n), body) ->
	    (* first let's be sure that ty :: Type *)
	    let ty = typecheck defs ctxt ~polarity:polarity ty (type_ (UName "")) in
	    (* if we have some type we use it *)
	    let ty = 
	      (* we typecheck te :: Type *)
	      match te.annot with
		| TypedAnnotation ({ ast = Forall ((_, ty', _), te'); _ }) -> unification defs ctxt ~polarity:polarity ty ty'
		| _ -> ty
	    in
	    (* we push the quantification *)
	    push_quantification (s, ty, n) ctxt;
	    (* and we typecheck te *)
	    let body = 
	      (* we typecheck te :: Type *)
	      match te.annot with
		| TypedAnnotation ({ ast = Forall ((_, ty', _), te'); _ }) -> typecheck defs ctxt ~polarity:polarity body te'
		| _ -> typeinfer defs ctxt ~polarity:polarity body
	    in    	    
	    (* we pop quantification *)
	    let (s, ty, n), [body] = pop_quantification defs ctxt [body] in
	    (* and we returns the term with type Type *)
	    let res = forall_ ~annot:(Typed (type_ (UName ""))) s ~nature:n ~ty:ty (get_type body) in
	    { te with ast = Lambda ((s, ty, n), body); annot = Typed res }

	  | Let ((n, value), body) ->
	    (* first we infer the value *)
	    let value = typeinfer defs ctxt ~polarity:polarity value in
	    (* we create a type for the return value *)
	    let ret_ty = 
	      match te.annot with
		| TypedAnnotation ty -> ty
		| _ -> add_fvar ctxt
	    in
	    (* then we push the quantification *)
	    push_quantification (n, get_type value, Explicit) ctxt;
	    (* here we add a conversion rule between the variable and the value *)
	    context_add_conversion defs ctxt (var_ ~annot:(Typed (bvar_type ctxt 0)) 0) value;
	    (* we infer the body *)
	    let body = typecheck defs ctxt ~polarity:polarity body (shift_term ret_ty 1) in
	    (* we pop the quantification *)
	    let (n, ty, _), [body] = pop_quantification defs ctxt [body] in
	    (* we returns the the let with the type of te2 shifted (god help us all ...) *)
	    { te with ast = Let ((n, value), body); annot = Typed (shift_term (get_type body) (-1)) }

	      
	  (* Normalizing app: only if we are not in_app *)
	  | App ({ast = App(f, args1); _}, args2) when not in_app ->
	    let te' = { te with ast = App (f, args1 @ args2) } in
	    typeinfer defs ctxt ~polarity:polarity te'
	      

	  (* this act as some kind of normalization *)
	  | App (hd, []) -> (
	    (* typecheck the head *)
	    let hd = typeinfer defs ctxt ~polarity:polarity hd in
	    (* split between a head and args *)
	    let app_head_ = app_head hd in
	    let app_args_ = app_args hd in
	    match app_args_ with
	      | [] -> app_head_
	      | _ ->
		{ te with ast = App (app_head_, app_args_); annot = Typed (get_type hd) }
	  )

	  | App (hd, (arg, n)::args) ->	  
	    (* we infer hd *)
	    let hd = typeinfer defs ctxt ~polarity:polarity ~in_app:true hd in
	    (* we unify the type of hd with a forall *)
	    let fty = add_fvar ctxt in
	    (*let ftyte = add_fvar ctxt in*)
	    let hd_ty = unification defs ctxt ~polarity:polarity (get_type hd) (forall_ ~annot:(Typed (type_ (UName ""))) "@typeinfer_App" ~nature:NJoker ~ty:fty (avar_ ())) in
	    let { ast = Forall ((_, _, n'), _); _ } = hd_ty in
	    (* if n' is Implicit and n is Explicit, it means we need to insert a free variable *)
	    if n' = Implicit && n = Explicit then (
	      let new_arg = add_fvar ctxt in
	      (* and retypeinfer the whole *)
	      typeinfer defs ctxt ~polarity:polarity ~in_app:true {te with ast = App (hd, (new_arg, n')::(arg, n)::args) }
	    ) else (
	      (* needs to unify the type properly *)
	      let { ast = Forall ((q, arg_ty, n'), body); annot = Typed fty; _ } = hd_ty in
	      let arg = typecheck defs ctxt ~polarity:polarity arg arg_ty in
	      (* we build a new head, as the reduction of hd and arg, with the proper type *)
	      let new_hd_ty = shift_term (term_substitution (IndexMap.singleton 0 (shift_term arg 1)) body) (-1) in
	      let new_hd = app_ ~annot:(Typed (new_hd_ty)) hd ((arg, n)::[]) in
	      let new_hd = reduction_term defs ctxt simplification_strat new_hd in 
	      typeinfer defs ctxt ~polarity:polarity ~in_app:true (app_ ~annot:te.annot ~pos:te.tpos new_hd args)
	    )

	  | Match (m, des) ->
	    (* first we typecheck the destructed term *)
	    let m = typeinfer defs ctxt m in
	    (* then we assure ourselves that it is an inductive *)
	    let mty = (get_type m) in
	    let indname = match (app_head (reduction_term defs ctxt typeinfer_strat mty)).ast with 
	      | Cste n -> (match get_cste defs n with | Inductive _ -> n | _ -> raise (PoussinException (NotInductiveDestruction (!ctxt, m))))
	      | _ -> raise (PoussinException (NotInductiveDestruction (!ctxt, m)))
	    in
	    (* we create a type for the return value *)
	    let ret_ty = 
	      match te.annot with
		| TypedAnnotation ty -> ty
		| _ -> add_fvar ctxt
	    in
	    (* we create a list of exhaustive pattern *)
	    let patlst = ref (build_inductive_pattern defs indname) in
	    (* then we traverse the destructors *)
	    let des = List.map (fun (ps, des) ->
	      (* saves the conversion *)
	      let convs = !ctxt.conversion_hyps in
	      (* first grab the vars of the patterns *)
	      let vars = patterns_vars ps in
	      (* we traverse the patterns *)
	      List.map (fun p ->
		(* we verify that the pattern is well formed *)
		if not (pattern_wf defs p) then raise (PoussinException (FreeError (String.concat " " ["pattern"; (pattern2string ctxt p); "is not well-formed"])));
		(* we push quantification corresponding to the pattern vars *)		
		List.iter (fun v -> 
		  let ty = add_fvar ctxt in
		  push_quantification (v, ty, Explicit (*dummy*)) ctxt
		) vars;
		(* we need to shift ret_ty, te, and tety to be at the same level *)
		let ret_ty = shift_term ret_ty (List.length vars) in
		let mty = shift_term mty (List.length vars) in
		let m = shift_term m (List.length vars) in
		(* we create the term corresponding to the pattern *)
		let p_te = pattern_to_term defs p in
		(* we update the list of visited pattern with p *)
		patlst := update_pattern_list defs !patlst p;
		(* we typecheck the termed pattern against the type of the destructed term *)
		let p_te = typecheck defs ctxt ~polarity:false ~coercion:false p_te mty in
		(* we unify it with the destructed term *)
		let _ = unification defs ctxt ~polarity:false p_te m in
		(* we typecheck the destructor body against the returned_type *)
		let des = typecheck defs ctxt des ret_ty in
		(* we pop_quantifications *)
		let _, [des] = pop_quantifications defs ctxt [des] (List.length vars) in
		(* restore old conversions (current ones are only valid for this pattern) *)
		ctxt := { !ctxt with conversion_hyps = convs };
		[p], des
	      ) ps
	    ) des in
	    (* for each unmatch pattern we try to find if it is compatible with the type of m, if not we discard it, else we register it as unmatched *)
	    List.iter (fun p -> 
	      (* first we make a copy of the context *)
	      let ctxt' = ref !ctxt in
	      (* we grab the vars of the patterns *)
	      let vars = pattern_vars p in
	      (* we push quantification corresponding to the pattern vars *)		
	      List.iter (fun v -> 
		let ty = add_fvar ctxt in
		push_quantification (v, ty, Explicit (*dummy*)) ctxt'
	      ) vars;
	      (* we need to shift the destructed term type *)
	      let mty' = shift_term mty (List.length vars) in
	      (* we create the term corresponding to the pattern *)
	      let p_te = pattern_to_term defs p in	      
	      (* we try to typecheck the termed pattern against the type of the destructed term *)
	      try
		let p_te = typecheck defs ctxt' ~polarity:false ~coercion:false p_te mty' in
		(* it typecheck -> the pattern is valid: we record it as unmatched *)
		unmatched_pattern := (!ctxt, p, mty', ret_ty)::!unmatched_pattern;
		if print_unmatched_pattern then (
		  
		  let _, frames = List.fold_right (fun ({name = n; ty = ty } as frame) (ln, acc)  ->
		    let n' = fresh_name_list ~basename:(if String.compare n "_" == 0 then "H" else n) ln in
		    (n'::ln), {frame with name = n'}::acc
		  ) !ctxt'.bvs ([], []) in
		  
		  let ctxt'' = ref { !ctxt' with bvs = frames } in

		  let s, f = conversion_hyps2subst ~dec_order:true !ctxt''.conversion_hyps in
		  let s = append_substitution s (context2subst ctxt'') in
		  (* we show the goal *)
		  printf "------------------------------------------\n";
		  ignore(map_nth (fun i -> 
		    let i' = i - 1 in
		    printf "%s: %s\n" (bvar_name ctxt'' i') (term2string ctxt'' (term_substitution s (bvar_type ctxt' i')))
		  ) (List.length !ctxt''.bvs));
		  printf "------------------------------------------\n";
		  printf "facts: %s\n" (conversion_hyps2string ctxt'' (!ctxt''.conversion_hyps));
		  printf "==========================================\n";

		  printf "warning: unmatched pattern: %s : %s (== %s)\n\n" (pattern2string ctxt p) (term2string ctxt'' (get_type p_te)) (term2string ctxt'' mty')
		)
	      with
		| PoussinException (NoUnification _) ->
		  (* the term mismatch the type -> this is not a possible pattern, thus we skip it*)
		  ()
	    ) !patlst;
	    let ret_ty = typecheck defs ctxt ~polarity:polarity ret_ty (type_ (UName "")) in
	    { te with ast = Match (m, List.concat des); annot = Typed ret_ty }
	  | _ -> raise (Failure (String.concat "" ["typeinfer: NYI for " ; term2string ctxt te]))
      ) in 
      match mty with
	| Some ty -> (
	  match compute_nature_prefix (args_nature (get_type te')) (args_nature ty) with
	    | [] -> te'
	    | l -> 
	      let new_args = List.fold_right ( fun n acc ->
		(add_fvar ctxt, n)::acc
	      ) l [] in
	      let te = { ast = App (te', new_args); annot = TypedAnnotation ty; tpos = NoPosition; reduced = false } in
	      typeinfer defs ctxt ~polarity:polarity te
	)

	| _ -> 
	  te'

and unification 
    (defs: defs)
    (ctxt: context ref)
    ?(polarity : bool = true)
    (te1: term) (te2: term) : term =
  try (
    match te1.ast, te2.ast with
	
	(* AVar is just a wildcard for unification *)
      | AVar _, _ -> te2
      | _, AVar _ -> te1

	(* the error case for AVar *)
      | TName _, _ | _, TName _ -> raise (PoussinException (FreeError "unification_term_term catastrophic: TName in te1 "))
	
	(* Prop and Set are imcompatible *)
      | Universe (Set, _) , Universe (Prop, _)  ->
	raise (PoussinException (NoUnification (!ctxt, te1, te2)))
      | Universe (Prop, _), Universe (Set, u2) ->
	raise (PoussinException (NoUnification (!ctxt, te1, te2)))
	(* equality over universe is pending equality of level *)
      | Universe (t1, u1), Universe (t2, u2) when t1 = Set or t2 = Set ->
	context_add_lvl_contraint ctxt (UEq (u1, u2));
	set_ ~pos:(pos_to_position (best_pos (pos_from_position te1.tpos) (pos_from_position te2.tpos))) u1

      | Universe (t1, u1), Universe (t2, u2) when t1 = Prop or t2 = Prop ->
	context_add_lvl_contraint ctxt (UEq (u1, u2));
	prop_ ~pos:(pos_to_position (best_pos (pos_from_position te1.tpos) (pos_from_position te2.tpos))) u1

      | Universe (Type, u1), Universe (Type, u2) ->
	context_add_lvl_contraint ctxt (UEq (u1, u2));
	type_ ~pos:(pos_to_position (best_pos (pos_from_position te1.tpos) (pos_from_position te2.tpos))) u1

	(* equality on cste *)
      | Cste c1, Cste c2 when c1 = c2 ->
	let ty = unification defs ctxt ~polarity:polarity (get_type te1) (get_type te2) in
	cste_ ~annot:(Typed ty) ~pos:(pos_to_position (best_pos (pos_from_position te1.tpos) (pos_from_position te2.tpos))) c1
	  
	(* a bit better *)
      | _ when (is_irreducible defs (app_head te1) && is_irreducible defs (app_head te2) && not (term_equal (app_head te1) (app_head te2))) ->
	raise (PoussinException (NoUnification (!ctxt, te1, te2)))
	(* a few other NoUnification Cases *)
      | Lambda _, _ | Forall _, _ | Universe _, _ when is_irreducible defs te2 -> raise (PoussinException (NoUnification (!ctxt, te1, te2)))
      | _, Lambda _ | _, Forall _ | _, Universe _ when is_irreducible defs te1 -> raise (PoussinException (NoUnification (!ctxt, te1, te2)))

	(* equality over variables *)
	(* two bounded variables case *)
      | Var i1, Var i2 when i1 = i2 -> 
	let ty = unification defs ctxt ~polarity:polarity (get_type te1) (get_type te2) in
	var_ ~annot:(Typed ty) ~pos:(pos_to_position (best_pos (pos_from_position te1.tpos) (pos_from_position te2.tpos))) i1

	(* if one of terms is a free variable which which there is a substitution, we redo unification on the term*)
      | Var i1, _ when i1 < 0 && fvar_subst ctxt i1 != None -> 
	unification defs ctxt ~polarity:polarity (match fvar_subst ctxt i1 with Some te1 -> te1) te2

      | _, Var i2 when i2 < 0 && fvar_subst ctxt i2 != None -> 
	unification defs ctxt ~polarity:polarity te1 (match fvar_subst ctxt i2 with Some te2 -> te2)
	  
	(* two free variables case *)
      | Var i1, Var i2 when i1 < 0 && i2 < 0 -> 
	let ty = unification defs ctxt ~polarity:polarity (get_type te1) (get_type te2) in
	let imin = min i1 i2 in
	let imax = max i1 i2 in
	let vmax = var_ ~annot:(Typed ty) ~pos:(pos_to_position (best_pos (pos_from_position te1.tpos) (pos_from_position te2.tpos))) imax in
	let s = IndexMap.singleton imin vmax in
	context_add_substitution defs ctxt s;
	vmax

	(* one free variable and one bounded *)
      | Var i1, _ when i1 < 0 && not (IndexSet.mem i1 (fv_term te2)) -> (
	let ty = unification defs ctxt ~polarity:polarity (get_type te1) (get_type te2) in
	let s = IndexMap.singleton i1 (set_term_typed te2 ty) in
	context_add_substitution defs ctxt s;
	te2
      )
      | Var i1, _ when i1 < 0 && (IndexSet.mem i1 (fv_term te2)) -> (
	raise (PoussinException (NoUnification (!ctxt, te1, te2)))
      )
      | _, Var i2 when i2 < 0 && not (IndexSet.mem i2 (fv_term te1)) -> (
	let ty = unification defs ctxt ~polarity:polarity (get_type te1) (get_type te2)  in
	let s = IndexMap.singleton i2 (set_term_typed te1 ty) in
	context_add_substitution defs ctxt s;
	te1
      )
      | _, Var i2 when i2 < 0 && (IndexSet.mem i2 (fv_term te1)) -> (
	raise (PoussinException (NoUnification (!ctxt, te1, te2)))
      )

	(* the Lambda case: only works if both are Lambda *)
      | Lambda ((s1, ty1, n1), body1), Lambda ((s2, ty2, n2), body2) ->
	if n1 <> n2 then raise (PoussinException (NoUnification (!ctxt, te1, te2)));
	  (* we unify the types *)
	let lty = unification defs ctxt ~polarity:polarity (get_type te1) (get_type te2) in
	let ty = unification defs ctxt ~polarity:polarity ty1 ty2 in
	  (* we push the quantification *)
	push_quantification (s1, ty, n1) ctxt;
	  (* we unify the body *)
	let body = unification defs ctxt ~polarity:polarity body1 body2 in
	  (* we pop quantification (possibly modifying te) *)
	let q1, [body] = pop_quantification defs ctxt [body] in
	  (* and we return the term *)
	{ ast = Lambda (q1, body); annot = Typed lty; tpos = te1.tpos; reduced = false }

      | Forall ((s1, ty1, n1), fte1), Forall ((s2, ty2, n2), fte2) ->
	let n = nature_unify n1 n2 in
	if n = None then raise (PoussinException (NoUnification (!ctxt, te1, te2)));
	let Some n = n in
	  (* we unify the types *)
	let lty = unification defs ctxt ~polarity:polarity (get_type te1) (get_type te2) in
	let ty = unification defs ctxt ~polarity:polarity ty1 ty2 in
	  (* we push the quantification *)
	push_quantification (s1, ty, n1) ctxt;
	  (* we unify the body *)
	let fte = unification defs ctxt ~polarity:polarity fte1 fte2 in
	  (* we pop quantification (possibly modifying te) *)
	let (s, ty, _), [fte] = pop_quantification defs ctxt [fte] in
	  (* and we return the term *)
	{ ast = Forall ((s, ty, n), fte); annot = Typed lty; tpos = te1.tpos; reduced = false }

      | Let ((s1, value1), body1), Let ((s2, value2), body2) ->
	  (* we unify the types *)
	let lty = unification defs ctxt ~polarity:polarity (get_type te1) (get_type te2) in
	let value = unification defs ctxt ~polarity:polarity value1 value2 in
	  (* we push the quantification *)
	push_quantification (s1, value, Explicit) ctxt;
	  (* we unify the body *)
	let body = unification defs ctxt ~polarity:polarity body1 body2 in
	  (* we pop quantification (possibly modifying te) *)
	let (s, value, _), [body] = pop_quantification defs ctxt [body] in
	  (* and we return the term *)
	{ ast = Let ((s, value), body); annot = Typed lty; tpos = te1.tpos; reduced = false }

	(* Normalizing App *)
      | App ({ ast = App(hd, args1); _}, args2), _ -> 
	let te1' = { te1 with ast = App(hd, args1 @ args2) } in
	unification defs ctxt ~polarity:polarity te1' te2
	  
      | _, App ({ ast = App(hd, args1); _}, args2) -> 
	let te2' = { te2 with ast = App(hd, args1 @ args2) } in
	unification defs ctxt ~polarity:polarity te1 te2'

      | App(f, []), _ ->
	unification defs ctxt ~polarity:polarity f te2  

      | _, App(f, []) ->
	unification defs ctxt ~polarity:polarity te1 f
	  
	(* some higher order unification: NOT YET FULLY TESTED !!! *)
      | App ({ ast = Var i; _}, (arg, n)::args), _ when i < 0 ->
	higher_order_unification defs ctxt ~polarity:polarity i arg n args te2 te1 te2
      | _, App ({ ast = Var i; _}, (arg, n)::args) when i < 0 ->
	higher_order_unification defs ctxt ~polarity:polarity i arg n args te1 te1 te2

	(* this is really conservatives ... *)
      | Match (t1, des1), Match (t2, des2) when List.length des1 = List.length des2 ->
	  (* unify the destructed term and the returned type *)
	let t = unification defs ctxt ~polarity:polarity t1 t2 in
	let ty = unification defs ctxt ~polarity:polarity (get_type te1) (get_type te2) in
	  (* then proceeds with the destructor *)
	let des = List.map2 (fun (ps1, t1) (ps2, t2) ->
	  if ps1 <> ps2 then raise (PoussinException (UnknownUnification (!ctxt, te1, te2)));
	    (* first grab the vars of the patterns *)
	  let vars = patterns_vars ps1 in	      
	    (* we push quantification corresponding to the pattern vars *)
	  List.iter (fun v -> 
	    let ty = add_fvar ctxt in
	    push_quantification (v, ty, Explicit (*dummy*)) ctxt
	  ) vars;
	  let t = unification defs ctxt ~polarity:polarity t1 t2 in
	  let _, [t] = pop_quantifications defs ctxt [t] (List.length vars) in
	  ps1, t	  
	) des1 des2 in
	{ ast = Match (t, des); annot = Typed ty; tpos = te1.tpos; reduced = false }

	(* the case of two application: with the same arity (and only positive polarity ) *)
      | App (hd1, args1), App (hd2, args2) when List.length args1 = List.length args2 && 
					     (polarity or (is_irreducible defs hd1 && is_irreducible defs hd2 && term_equal hd1 hd2))
					   ->
	let ty = unification defs ctxt ~polarity:polarity (get_type te1) (get_type te2) in
	let hd = unification defs ctxt ~polarity:polarity hd1 hd2 in
	let args = List.map (fun (n, hd1, hd2) -> unification defs ctxt ~polarity:polarity hd1 hd2, n) 
	  (List.map2 (fun (hd1, n1) (hd2, n2) -> 
	    if n1 <> n2 then 
	      raise (PoussinException (NoNatureUnification (!ctxt, hd1, hd2)))
	    else
	      n1, hd1, hd2
	   ) args1 args2) in
	{ ast = App (hd, args); annot = Typed ty; tpos = te1.tpos; reduced = false }

	(* maybe we can reduce the term *)
      | _ when not (get_term_reduced te1) ->
	let te1' = set_term_reduced true (reduction_term defs ctxt unification_strat te1) in
	let res = unification defs ctxt ~polarity:polarity te1' te2 in
	res
      | _ when not (get_term_reduced te2) ->
	let te2' = set_term_reduced true (reduction_term defs ctxt unification_strat te2) in
	let res = unification defs ctxt ~polarity:polarity te1 te2' in
	res

	(* nothing so far, if the polarity is negative, we add the unification as a converion hypothesis *)
      | _ when not polarity ->
	context_add_conversion defs ctxt te1 te2;
	te1

      (* we look if we have one of the term which is a free var applied to a reducible term
	 we call the oracles to find a proper instance (this is how to implement canonical structure)
      *)
      | _, App (f, ({ast = Var i; annot = Typed ty; _}, n)::[])
      | App (f, ({ast = Var i; annot = Typed ty; _}, n)::[]), _ when i < 0 && is_reducible_def defs f
	->
	(* we build a context with the conv as hypothesis *)
	let ctxt' = ref {!ctxt with conversion_hyps = (te1, te2)::!ctxt.conversion_hyps} in (
	match oracles_call defs ctxt' ~var:(Some i) ty with
	  | None -> (* nothing there, we just raise an error *)
	    raise (PoussinException (FreeError "the oracles failed to infer a free variable (2)"))
	  | Some te -> (* we just return the answer of the oracles as the free variable value *)
	    (* we update the context *)
	    ctxt := { !ctxt' with conversion_hyps = List.tl !ctxt'.conversion_hyps };
	    (* we add the subtitution *)
	    let s = (IndexMap.singleton i te) in
	    context_add_substitution defs ctxt s;
	    (* and we retry the unification *)
	    unification defs ctxt (term_substitution s te1) (term_substitution s te2)
	)
	(* we do not know *)
      | _ -> raise (PoussinException (UnknownUnification (!ctxt, te1, te2)));
	
  ) with
    | (PoussinException (UnknownUnification (ctxt', te1', te2'))) when not (get_term_reduced te1) or not (get_term_reduced te2) ->
      let te1' = if not (get_term_reduced te1) then set_term_reduced true (reduction_term defs ctxt unification_strat te1) else te1 in
      let te2' = if not (get_term_reduced te2) then set_term_reduced true (reduction_term defs ctxt unification_strat te2) else te2 in
      let res = unification defs ctxt ~polarity:polarity te1' te2' in
      res

    | (PoussinException (UnknownUnification (ctxt', te1', te2'))) when polarity ->
      let s, l = conversion_hyps2subst !ctxt.conversion_hyps in
      let s_in_te1 = not (IndexSet.is_empty (IndexSet.inter (substitution_vars s) (bv_term te1))) in
      let s_in_te2 = not (IndexSet.is_empty (IndexSet.inter (substitution_vars s) (bv_term te2))) in
      if s_in_te1 || s_in_te2 then (
	let te1' = if s_in_te1 then {(term_substitution s te1) with reduced = false} else te1 in
	let te2' = if s_in_te2 then {(term_substitution s te2) with reduced = false} else te2 in
	let ctxt' = ref !ctxt in (*{ !ctxt with conversion_hyps = l } in*)
	let res = unification defs ctxt' ~polarity:polarity te1' te2' in
	ctxt := { !ctxt' with conversion_hyps = !ctxt.conversion_hyps };
	res
      ) else (
	match l with
	  | [] -> raise (PoussinException (UnknownUnification (!ctxt, te1, te2)))
	  | (hd1, hd2)::tl -> 
	    let te1' = rewrite_term defs ctxt hd1 hd2 te1 in
	    let te2' = rewrite_term defs ctxt hd1 hd2 te2 in
	    let tl' = List.map (fun (te1, te2) -> rewrite_term defs ctxt hd1 hd2 te1, rewrite_term defs ctxt hd1 hd2 te2) tl in
	    let ctxt' = ref { !ctxt with conversion_hyps = tl' } in
	    let res = unification defs ctxt' ~polarity:polarity te1' te2' in
	    ctxt := { !ctxt' with conversion_hyps = !ctxt.conversion_hyps };
	    res	      
      )	

and higher_order_unification (defs: defs) (ctxt: context ref) ?(polarity : bool = true) (i: index) (arg: term) (n: nature) (args: (term* nature) list) (te: term) te1 te2 =
  (* here the principle is to "extract" the arg from the other term, transforming it into a Lambda and retry the unification *)
  (* shift te 1 : now there is no TVar 0 in te *)
  let te' = shift_term te 1 in
  (* thus we can rewrite (shift arg 1) by TVar 0 *)
  let te' = rewrite_term defs ctxt (shift_term arg 1) (var_ ~annot:(Typed (shift_term (get_type arg) 1)) 0) te' in
  (* we just verify that we have some instance of TVar 0 *)
  (*if not (IndexSet.mem 0 (bv_term te')) then raise (PoussinException (UnknownUnification (!ctxt, te1, te2)));*)
  (* we push a variable in the environment *)
  push_quantification ("", get_type arg, n) ctxt;
  (* we shift all args *)
  let args = List.map (fun (te, n) -> shift_term te 1, n) args in
  (* we create a new free variable and an application *)
  let j = add_fvar ctxt in
  let te_j = app_ j args in
  let te_j = typeinfer defs ctxt ~polarity:polarity te_j in
  (* we unify the application to the remaining args, with the body of the lambda (=t) *)
  let body = unification defs ctxt ~polarity:polarity te_j te' in
  (* we pop the quantifiers *)
  let (_, ty, _), [body] = pop_quantification defs ctxt [body] in
  (* we build the lambda, and add the substitution to i *)
  let res = lambda_ "X" ~nature:n ~ty:ty body in
  let res = typeinfer defs ctxt ~polarity:polarity res in
  context_add_substitution defs ctxt (IndexMap.singleton i res);
  te

(* some basic rewriting *)
(* two mode: structural equality or unification *)
and rewrite_term defs ctxt ?(struct_eq: bool = true) (lhs: term) (rhs: term) (te: term) : term =
  if (
    if struct_eq then 
      term_equal lhs te
    else (
      let ctxt' = !ctxt in
      try
	let _ = unification defs ctxt lhs te in
	true
      with
	| PoussinException _ -> ctxt := ctxt'; false
    )
  ) then
    rhs
  else
    let ast =
      match te.ast with
	| Lambda ((n, ty, nat), body) ->
	  Lambda ((n, rewrite_term defs ctxt ~struct_eq:struct_eq lhs rhs ty, nat),
		  rewrite_term defs ctxt ~struct_eq:struct_eq (shift_term lhs 1) (shift_term rhs 1) body)
	| Forall ((n, ty, nat), body) ->
	  Forall ((n, rewrite_term defs ctxt lhs rhs ty, nat),
		  rewrite_term defs ctxt ~struct_eq:struct_eq (shift_term lhs 1) (shift_term rhs 1) body)
	| Let ((n, value), body) ->
	  Let ((n, rewrite_term defs ctxt ~struct_eq:struct_eq lhs rhs value),
	       rewrite_term defs ctxt ~struct_eq:struct_eq (shift_term lhs 1) (shift_term rhs 1) body)
	| App (f, args) ->
	  App (rewrite_term defs ctxt ~struct_eq:struct_eq lhs rhs f,
	       List.map (fun (arg, n) -> rewrite_term defs ctxt ~struct_eq:struct_eq lhs rhs arg, n) args)
	| Match (te, des) ->
	  Match (rewrite_term defs ctxt ~struct_eq:struct_eq lhs rhs te,
		 List.map (fun (ps, te) -> 
		   let i = patterns_size ps in
		   ps, rewrite_term defs ctxt ~struct_eq:struct_eq (shift_term lhs i) (shift_term rhs i) te) des)
	| _ -> te.ast
    in
    match get_type te with
      | {ast = Universe _; _} -> { te with ast = ast }
      | ty -> { te with ast = ast; annot = Typed (rewrite_term defs ctxt lhs rhs ty); reduced = false }

(* reduction *)

and reduction_term (defs: defs) (ctxt: context ref) (strat: reduction_strategy) (te: term) : term = 
  let te' = reduction_term_loop defs ctxt strat (set_term_reduced ~recursive:true false te) in
  (set_term_reduced ~recursive:true false te')
and reduction_term_loop (defs: defs) (ctxt: context ref) (strat: reduction_strategy) (te: term) : term = 
  let te' = (
    match te.ast with
      | Universe _ | AVar _ | TName _ -> te
	
      | Var i when i < 0 -> (
	match fvar_subst ctxt i with
	  | None -> te
	  | Some te -> reduction_term_loop defs ctxt strat te
      )

      | _ when get_term_reduced te -> te

      | Cste n -> (
	  match get_cste defs n with
	    | Definition te -> (
	      match strat.delta with
		| Some _ -> 
		  let te' = reduction_term_loop defs ctxt strat te in
		  te'
		| None -> set_term_reduced true te
	    )
	    | _ -> set_term_reduced true te
	    
      )

      | Lambda ((n, ty, nature), body) when strat.beta = Some BetaStrong ->
	(
	  push_quantification (n, ty, nature) ctxt;
	  let body = reduction_term_loop defs ctxt strat body in
	  let _ = pop_quantification defs ctxt [] in
	  { te with ast = Lambda ((n, ty, nature), body); reduced = true }
	)

      | Forall ((n, ty, nature), body) when strat.beta = Some BetaStrong ->
	(
	  push_quantification (n, ty, nature) ctxt;
	  let body = reduction_term_loop defs ctxt strat body in
	  let _ = pop_quantification defs ctxt [] in
	  { te with ast = Forall ((n, ty, nature), body); reduced = true }
	)

      | Let _ when strat.zeta = false && strat.beta != Some BetaStrong -> set_term_reduced true te
      | Let ((n, value), body) when strat.zeta = false && strat.beta = Some BetaStrong ->
	push_quantification (n, (get_type value), Explicit) ctxt;
	let body = reduction_term_loop defs ctxt strat body in
	let _ = pop_quantification defs ctxt [] in
	{ te with ast = Let ((n, value), body); reduced = true }

      | Let ((n, value), body) when strat.zeta = true ->
	(* here we compute the reduction of te and shift it such that it is at the same level as te2 *)
	let value = shift_term (reduction_term_loop defs ctxt strat value) 1 in
	(* we substitute all occurence of n by te *)
	let body = term_substitution (IndexMap.singleton 0 value) body in
	(* and we shift back to the proper level *)
	let body = shift_term body (-1) in
	reduction_term_loop defs ctxt strat body

      | Match _ when strat.iota = false -> set_term_reduced true te
      | Match (dte, des) -> (
	let dte = reduction_term_loop defs ctxt strat dte in
	let res = fold_stop (fun () (ps, body) ->
	  fold_stop (fun () p ->
	    match pattern_match defs p dte with
	      | PNoMatch -> Left ()
	      | PUnknownMatch -> Right None
	      | PMatch l ->
		(* we will do the same thing as in let, but on the reversed order of the matching list *)
		let te = List.fold_left (fun acc te -> 
		  (* rewrite the var 0 *)
		  let acc = term_substitution (IndexMap.singleton 0 te) acc in
		  (* shift the term by -1 *)
		  let acc = shift_term acc (-1) in
		  acc
		) 
		  body 
		  (List.rev (List.fold_left (fun acc te -> acc @ [shift_term te (List.length acc + 1)]) [] l)) in
		Right (Some te)
	  ) () ps
	) () des in
	match res with
	  | Left () | Right None -> set_term_reduced true te
	  | Right (Some te) -> reduction_term_loop defs ctxt strat te
      )

      | App ({ ast = Lambda ((n, ty, nature), body); _}, (hd1, hd2)::tl) when strat.beta != None ->
	let hd1 = shift_term (reduction_term_loop defs ctxt strat hd1) 1 in
	let f = set_term_reduced ~recursive:true false (term_substitution (IndexMap.singleton 0 hd1) body) in
	reduction_term_loop defs ctxt strat {te with ast = App (shift_term f (-1), tl); reduced = false }

      | App (f, []) ->
	set_term_reduced true (reduction_term_loop defs ctxt strat f)

      | App ({ast = App(f1, args1)}, args2) ->
	set_term_reduced true (reduction_term_loop defs ctxt strat {te with ast = App (f1, args1 @ args2); reduced = false})

      | App (f, args) when not (get_term_reduced f) -> (
	let f = reduction_term_loop defs ctxt { strat with delta = match strat.delta with | Some DeltaWeak -> Some DeltaStrong | _ -> strat.delta } f in
	set_term_reduced true (reduction_term_loop defs ctxt strat {te with ast = App (f, args); reduced = false})
      )

      | App (f, args) when get_term_reduced f ->
	let args = List.map (fun (te, n) -> reduction_term_loop defs ctxt strat te, n) args in
	{ te with ast = App (f, args); reduced = true }

      | _ -> 
	te

  ) in
  let te' = 
    match strat.delta with
      | Some DeltaWeak when is_clean_term defs te' -> te'
      | Some DeltaUWeak when is_clean_term defs ~strong:true te' -> te'
      | Some DeltaStrong -> set_term_reduced true te'
      | _ -> set_term_reduced true te      
  in
  te'

and reduction_typeannotation (defs: defs) (ctxt: context ref) (strat: reduction_strategy) (ty: typeannotation) : typeannotation =
  match ty with
    | NoAnnotation -> NoAnnotation
    | Annotation te -> Annotation (reduction_term_loop defs ctxt strat te)
    | Typed te -> Typed (reduction_term_loop defs ctxt strat te)

