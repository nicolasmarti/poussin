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


let push_quantification (q: (name * term * nature)) (ctxt: context ref) : unit =
  let s, ty, n = q in
  ctxt := { !ctxt with
    bvs = {name = s; ty = shift_term ty 1; nature = n}::!ctxt.bvs;
    fvs = List.map (fun (i, ty, te, n) -> (i, shift_term ty 1, (match te with | None -> None | Some te -> Some (shift_term te 1)), n)) !ctxt.fvs;
    conversion_hyps = List.map (fun (hd1, hd2) -> (shift_term hd1 1, shift_term hd2 1)) !ctxt.conversion_hyps
  }

let rec flush_fvars (defs: defs) (ctxt: context ref) (tes: term list) : term list =
  (* we rewrite the conversion hypothesis in increasing order in the free vars *)
  let s, _ = conversion_hyps2subst ~dec_order:true !ctxt.conversion_hyps in
  let fvs = List.map (fun (i, ty, te, n) ->
    (i,
     term_substitution s ty,
     (match te with | None -> None | Some te -> Some (term_substitution s te)),
     n)
  ) !ctxt.fvs in  
  (* we rewrite all the terms *)
  let tes = List.fold_left (fun acc (i, ty, te, n) ->
    match te with
      | None -> acc
      | Some te -> List.map (fun te' -> term_substitution (IndexMap.singleton i te) te') acc
  ) tes fvs in
  (* we compute the fvars of the terms *)
  let lfvs = List.fold_left (fun acc te -> IndexSet.union acc (fv_term te)) IndexSet.empty tes in  
  (* we shift the freevars, and allow removing does who does not appears *)
  let fvs = List.fold_left (fun acc (i, ty, te, n) ->
    try 
      acc @ [i, shift_term ty (-1), 
	     (match te with
	       | None -> None
	       | Some te -> Some (shift_term te (-1))), 
	     n]
    with
      | PoussinException (Unshiftable_term _) ->
	(* if the free variable does not appears in the terms we can remove it *)
	if not (IndexSet.mem i lfvs) then (
	  (*printf "remove %s\n" (string_of_int i);*)
	  acc
	) else
	  (* TODO: add oracle call for instantiating the free variable *)
	  (* otherwise there is something wrong here, for now we make it an error *)
	  raise (PoussinException (FreeError "we failed to infer a free variable that cannot be out-scoped"))
  ) [] fvs in
	(* we replace the new free var set *)
	(if List.length !ctxt.bvs != 0 then
	    ctxt := { !ctxt with
	      fvs = fvs
	    } else 
	    List.iter (fun te -> 
	      if not (IndexSet.is_empty (fv_term te)) then (
		let msg = String.concat "" ["there are free variables in the remaining term: \n"; term2string ctxt te; "\n :: \n"; term2string ctxt (get_type te) ] in
		raise (PoussinException (FreeError msg)))
	    ) tes
	);
  tes


let pop_quantification (defs: defs) (ctxt: context ref) (tes: term list) : (name * term * nature) * term list =
  (* we flush the vars *)
  let tes = flush_fvars defs ctxt tes in
  (* we grab the remaining context and the popped frame *)
  let frame = List.hd (!ctxt.bvs) in
  (* we set the context *)
  ctxt := { !ctxt with 
    bvs = List.tl !ctxt.bvs;
    (* we shift the update version of the conversion_hyps *)
    conversion_hyps = 
      List.fold_left (fun acc (hd1, hd2) ->
	try 
	  acc @ (shift_term hd1 (-1), shift_term hd2 (-1))::[]
	with
	  | PoussinException (Unshiftable_term _) ->
	    (*printf "removing from conversion: %s === %s\n" (term2string ctxt hd1) (term2string ctxt hd2);*)
	    acc
	      
      ) [] !ctxt.conversion_hyps;    
  };
  (* and returns the quantifier *)
  (frame.name, shift_term frame.ty (-1), frame.nature), tes  

let rec pop_quantifications (defs: defs) (ctxt: context ref) (tes: term list) (n: int) : (name * term * nature) list * term list =
  match n with
    | _ when n < 0 -> raise (PoussinException (FreeError "Catastrophic: negative n in pop_quantifications"))
    | 0 -> [], tes
    | _ ->
      let hd, tes = pop_quantification defs ctxt tes in
      let tl, tes = pop_quantifications defs ctxt tes (n-1) in
      hd::tl, tes

(**)
let context_add_conversion (ctxt: context ref) (te1: term) (te2: term) : unit =
  printf "added conversion: %s == %s\n" (term2string ctxt te1) (term2string ctxt te2);
  ctxt := { !ctxt with conversion_hyps = ((te1, te2)::(!ctxt.conversion_hyps)) }
  (*printf "%s\n"(conversion_hyps2string ctxt (!ctxt.conversion_hyps))*)



(* typechecking, inference and reduction *)

let rec typecheck 
    (defs: defs)
    (ctxt: context ref)
    ?(polarity: bool = true)
    (te: term)
    (ty: term) : term =
  if !mk_trace then trace := (TC (!ctxt, te, ty))::!trace;
  let res = 
  (* TODO: add oracle calls on error
     te:ty' --> f: ty' -> ty, returns f te
  *)
  match get_term_typeannotation te with
    | Typed ty' ->
      ignore(unification defs ctxt ~polarity:polarity ty' ty);
      te
    | Annotation ty' ->
      let ty' = typeinfer defs ctxt ~polarity:polarity ty' in
      let te = typeinfer defs ctxt ~polarity:polarity (set_term_typedannotation te ty') in
      ignore(unification defs ctxt ~polarity:polarity (get_type te) ty);
      te 
    | TypedAnnotation ty' ->
      let te = typeinfer defs ctxt ~polarity:polarity (set_term_typedannotation te ty') in
      ignore(unification defs ctxt ~polarity:polarity (get_type te) ty);
      te 
    | NoAnnotation ->
      let te = typeinfer defs ctxt ~polarity:polarity (set_term_typedannotation te ty) in
      ignore(unification defs ctxt ~polarity:polarity (get_type te) ty);
      te
  in
  if !mk_trace then trace := List.tl !trace;
  res


and typeinfer 
    (defs: defs)
    (ctxt: context ref)
    ?(polarity: bool = true)
    (te: term) : term =
  if !mk_trace then trace := (TI (!ctxt, te))::!trace;
  (*printf "%s :? \n" (term2string ctxt te);*)
  let res = 
  match get_term_typeannotation te with
    | Typed ty -> te
    | Annotation ty ->
      (*let ty = typecheck defs ctxt ty (type_ (UName "")) in*)
      let ty = typeinfer defs ctxt ~polarity:polarity ty in
      typeinfer defs ctxt ~polarity:polarity (set_term_typedannotation te ty)
    | ty ->
      let mty = match ty with | NoAnnotation -> None | TypedAnnotation ty -> Some ty in
      let te' = (
	match te.ast with
	  | Universe _ -> te
	  | Cste n -> (
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

	  | AVar  ->
	    add_fvar ~pos:te.tpos ctxt

	  | Interactive -> 
	    add_fvar ~pos:te.tpos ~interactive:true ctxt

	  | TName n -> (
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
	    let res = { te with ast = Forall ((s, ty, n), body); annot = Typed (type_ (UName "")) } in
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
	    let q1, [body] = pop_quantification defs ctxt [body] in
	    (* and we returns the term with type Type *)
	    let res = forall_ ~annot:(Typed (type_ (UName ""))) s ~nature:n ~ty:ty (get_type body) in
	    { te with ast = Lambda ((s, ty, n), body); annot = Typed res }

	  | Let ((n, value), body) ->
	    (* first we infer the value *)
	    let value = typeinfer defs ctxt ~polarity:polarity value in
	    (* then we push the quantification *)
	    push_quantification (n, get_type value, Explicit) ctxt;
	    (* here we add a conversion rule between the variable and the value *)
	    context_add_conversion ctxt (var_ ~annot:(Typed (bvar_type ctxt 0)) 0) value;
	    (* we infer the body *)
	    let body = typeinfer defs ctxt ~polarity:polarity body in
	    (* we pop the quantification *)
	    let (n, ty, _), [body] = pop_quantification defs ctxt [body] in
	    (* we returns the the let with the type of te2 shifted (god help us all ...) *)
	    { te with ast = Let ((n, value), body); annot = Typed (shift_term (get_type body) (-1)) }

	  | App (hd, []) -> (
	    let hd = typeinfer defs ctxt ~polarity:polarity hd in
	    match app_args hd with
	      | [] -> hd
	      | args ->
		{ te with ast = App (app_head hd, args); annot = Typed (get_type hd) }
	  )

	  | App (hd, (arg, n)::args) ->	  
	    (* we infer hd *)
	    let hd = typeinfer defs ctxt ~polarity:polarity hd in
	    (* we unify the type of hd with a forall *)
	    let fty = add_fvar ctxt in
	    let hd_ty = unification defs ctxt ~polarity:polarity (get_type hd) (forall_ ~annot:(Typed (type_ (UName ""))) "@typeinfer_App" ~nature:NJoker ~ty:fty (avar_ ())) in
	    let { ast = Forall ((_, _, n'), _); _ } = hd_ty in
	    (* if n' is Implicit and n is Explicit, it means we need to insert a free variable *)
	    if n' = Implicit && n = Explicit then (
	      let new_arg = add_fvar ctxt in
	      (* and retypeinfer the whole *)
	      typeinfer defs ctxt ~polarity:polarity {te with ast = App (hd, (new_arg, n')::(arg, n)::args) }
	    ) else (
	      (* needs to unify the type properly *)
	      let { ast = Forall ((q, arg_ty, n'), body); annot = Typed fty; _ } = hd_ty in
	      let arg = typecheck defs ctxt ~polarity:polarity arg arg_ty in
	      (* we build a new head, as the reduction of hd and arg, with the proper type *)
	      (*(App (Lambda ((q, ty, n, pq), te, Typed fty, p, reduced), (arg,n)::[], Typed fty, pos, false))*)
	      let new_hd_ty = shift_term (term_substitution (IndexMap.singleton 0 (shift_term arg 1)) body) (-1) in
	      let new_hd = app_ ~annot:(Typed (new_hd_ty)) (*~pos:pos*) hd ((arg, n)::[]) in
	      (*printf "Unification, App new_hd:\n%s\n\n" (term2string ctxt new_hd);*)
	      let new_hd = reduction_term defs ctxt simplification_strat new_hd in 
	      typeinfer defs ctxt ~polarity:polarity (app_ ~pos:te.tpos new_hd args)
	    )

	  | Match (m, des) ->
	    (* first we typecheck the destructed term *)
	    let m = typeinfer defs ctxt m in
	    (* then we assure ourselves that it is an inductive *)
	    let mty = (get_type m) in
	    (*
	    let _ = 
	      match (app_head (reduction_term defs ctxt typeinfer_strat mty)).ast with
		| Cste n -> (
		  match get_cste defs n with
		    | Inductive _ as ty -> ty
		    | _ -> raise (PoussinException (NotInductiveDestruction (!ctxt, m)))
		)
		| _ -> raise (PoussinException (NotInductiveDestruction (!ctxt, m)))
	    in
	    *) 
	    (* we create a type for the return value *)
	    let ret_ty = 
	      match te.annot with
		| TypedAnnotation ty -> ty
		| _ -> add_fvar ctxt
	    in
	    (* then we traverse the destructors *)
	    let des = List.map (fun (ps, des) ->
	      (*printf "********************************************************************\n";*)
	      (* saves the conversion *)
	      let convs = !ctxt.conversion_hyps in
	      (* first grab the vars of the patterns *)
	      let vars = patterns_vars ps in
	      (* we push quantification corresponding to the pattern vars *)
	      List.iter (fun v -> 
		let ty = add_fvar ctxt in
		push_quantification (v, ty, Explicit (*dummy*)) ctxt
	      ) vars;
	      (* we need to shift ret_ty, te, and tety to be at the same level *)
	      let ret_ty = shift_term ret_ty (List.length vars) in
	      let mty = shift_term mty (List.length vars) in
	      let m = shift_term m (List.length vars) in
	      (* then we create the terms corresponding to the patterns *)
	      let tes = List.map (fun p -> pattern_to_term defs p) ps in
	      (* then, for each patterns, we typecheck against tety *)
	      (* for each pattern that do not unify we remove it *)
	      let tes = List.fold_right (fun te acc -> 
		(*printf "%s :?\n" (term2string ctxt te); flush stdout;*)
		let te = typeinfer defs ctxt ~polarity:false te in
		try 
		  (*printf "%s =?= %s\n" (term2string ctxt (get_type te)) (term2string ctxt mty); flush stdout;*)
		  let _ = unification defs ctxt ~polarity:false (get_type te) mty in
		  (*printf "%s : %s == %s\n" (term2string ctxt m) (term2string ctxt mty) (term2string ctxt te);*)
		  te::acc
		with
		  | PoussinException _ -> 
		    (*printf "%s <!> %s\n" (term2string ctxt (get_type te)) (term2string ctxt mty); flush stdout;*)
		    acc
	      ) tes [] in
	      (* then, for each pattern *)
	      let des = List.map (fun hd ->
		(* we unify it (with negative polarity) with te *)
		let _ = unification defs ctxt ~polarity:false hd m in
		(* and typecheck des against ret_ty *)
		let s = context2subst ctxt in
		(*printf "s := %s\n" (substitution2string ctxt s);*)
		let ret_ty = term_substitution s ret_ty in
		(*printf ":= %s : %s\n" (term2string ctxt des) (term2string ctxt ret_ty);*)
		typecheck defs ctxt des ret_ty
	      ) tes in
	      (* we pop all quantifiers *)
	      let _, des = pop_quantifications defs ctxt des (List.length vars) in
	      (* restore old conversions *)
	      ctxt := { !ctxt with conversion_hyps = convs };
	      (* and finally returns all the constructors *)
	      List.map2 (fun hd1 hd2 -> [hd1], hd2) ps des
	    ) des in
	    (*printf "********************************************************************\n";*)
	    let ret_ty = typecheck defs ctxt ~polarity:polarity ret_ty (type_ (UName "")) in
	    { te with ast = Match (m, List.concat des); annot = Typed ret_ty }
	  | _ -> raise (Failure (String.concat "" ["typeinfer: NYI for " ; term2string ctxt te]))
      ) in 
      (*
      if not (NameSet.is_empty (name_term te')) then (
	printf "catastrophic contains names !!:\n%s\n" (term2string ctxt te');
	raise Pervasives.Exit
      );
      *)
      match mty with
	| Some ty -> (
	  (*
	  printf "%s ~~> %s:\n%s(%s)\n Vs \n%s(%s)\n\n" 
	    (term2string ctxt te) 
	    (term2string ctxt te') 
	    (term2string ctxt (get_type te')) 
	    (match nb_first_implicits (get_type te') with | None -> "None" | Some i -> string_of_int i) 
	    (term2string ctxt ty)
	    (match nb_first_implicits ty with | None -> "None" | Some i -> string_of_int i) 
	  ;
	  *)
	  (* we can check if we need to add Implicit arguments *)
	  match nb_first_implicits (get_type te'),  nb_first_implicits ty with
	    | Some i, Some j when i > j ->
	      let new_args = foldi (fun l -> (add_fvar ctxt, Implicit)::l) [] (i - j) in
	      let te = { ast = App (te', new_args); annot = TypedAnnotation ty; tpos = NoPosition; reduced = false } in
	      (*printf "%s ~~> %s\n" (term2string ctxt te') (term2string ctxt te);*)
	      typeinfer defs ctxt ~polarity:polarity te
	    | Some i, None when i > 0 ->
	      let new_args = foldi (fun l -> (add_fvar ctxt, Implicit)::l) [] i in
	      let te = { ast = App (te', new_args); annot = TypedAnnotation ty; tpos = NoPosition; reduced = false } in
	      (*printf "%s ~~> %s\n" (term2string ctxt te') (term2string ctxt te);*)
	      typeinfer defs ctxt ~polarity:polarity te
	    | _ -> te'

	)

	| _ -> te'
  in
  if !mk_trace then trace := List.tl !trace;
  res

and unification 
    (defs: defs)
    (ctxt: context ref)
    ?(polarity : bool = true)
    (te1: term) (te2: term) : term =
  if !mk_trace then trace := (if polarity then (U (!ctxt, te1, te2)) else (UNeg (!ctxt, te1, te2)))::!trace;
  let res = 
    (*printf "%s Vs %s\n" (term2string ctxt te1) (term2string ctxt te2); flush stdout;*)
    try (
      match te1.ast, te2.ast with
	  
	(* AVar is just a wildcard for unification *)
	| AVar, _ -> te2
	| _, AVar -> te1

	(* the error case for AVar *)
	| TName _, _ -> raise (PoussinException (FreeError "unification_term_term catastrophic: TName in te1 "))
	| _, TName _ -> raise (PoussinException (FreeError "unification_term_term catastrophic: TName in te2 "))
	  
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
	| _ when (is_irreducible defs te1 && is_irreducible defs te2 && not (term_equal te1 te2)) ->
	  raise (PoussinException (NoUnification (!ctxt, te1, te2)))

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
	  context_add_substitution ctxt s;
	  vmax

	(* one free variable and one bounded *)
	| Var i1, _ when i1 < 0 && not (IndexSet.mem i1 (fv_term te2)) -> (
	  let ty = unification defs ctxt ~polarity:polarity (get_type te1) (get_type te2) in
	  let s = IndexMap.singleton i1 (set_term_typed te2 ty) in
	  context_add_substitution ctxt s;
	  te2
	)
	| Var i1, _ when i1 < 0 && (IndexSet.mem i1 (fv_term te2)) -> (
	  (*printf "%s \\in %s\n" (string_of_int i1) (term2string ctxt te2); flush stdout;*)
	  raise (PoussinException (NoUnification (!ctxt, te1, te2)))
	)
	| _, Var i2 when i2 < 0 && not (IndexSet.mem i2 (fv_term te1)) -> (
	  let ty = unification defs ctxt ~polarity:polarity (get_type te1) (get_type te2)  in
	  let s = IndexMap.singleton i2 (set_term_typed te1 ty) in
	  context_add_substitution ctxt s;
	  te1
	)
	| _, Var i2 when i2 < 0 && (IndexSet.mem i2 (fv_term te1)) -> (
	  (*printf "%s \\in %s\n" (string_of_int i2) (term2string ctxt te1); flush stdout;*)
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
	  if !mk_trace then trace := (Reduction (!ctxt, te1, te1'))::!trace;
	  let res = unification defs ctxt ~polarity:polarity te1' te2 in
	  if !mk_trace then trace := List.tl !trace;
	  res
	| _ when not (get_term_reduced te2) ->
	  let te2' = set_term_reduced true (reduction_term defs ctxt unification_strat te2) in
	  if !mk_trace then trace := (Reduction (!ctxt, te2, te2'))::!trace;
	  let res = unification defs ctxt ~polarity:polarity te1 te2' in
	  if !mk_trace then trace := List.tl !trace;
	  res

	(* nothing so far, if the polarity is negative, we add the unification as a converion hypothesis *)
	| _ when not polarity ->
	  context_add_conversion ctxt te1 te2;
	  te1

	(* we do not know *)
	| _ -> raise (PoussinException (UnknownUnification (!ctxt, te1, te2)));
	    
    ) with
      | (PoussinException (UnknownUnification (ctxt', te1', te2'))) when not (get_term_reduced te1) or not (get_term_reduced te2) ->
	let te1' = if not (get_term_reduced te1) then set_term_reduced true (reduction_term defs ctxt unification_strat te1) else te1 in
	if !mk_trace then trace := (Reduction (!ctxt, te1, te1'))::!trace;
	let te2' = if not (get_term_reduced te2) then set_term_reduced true (reduction_term defs ctxt unification_strat te2) else te2 in
	if !mk_trace then trace := (Reduction (!ctxt, te2, te2'))::!trace;
	let res = unification defs ctxt ~polarity:polarity te1' te2' in
	if !mk_trace then trace := List.tl (List.tl !trace);
	res

      | (PoussinException (UnknownUnification (ctxt', te1', te2'))) when polarity ->
	let s, l = conversion_hyps2subst !ctxt.conversion_hyps in
	(*printf "(1)\n%s Vs %s\nl := %s \n==========> \ns := %s, \nl:= %s\n\n" (term2string ctxt te1) (term2string ctxt te2) (conversion_hyps2string ctxt (!ctxt.conversion_hyps)) (substitution2string ctxt s) (conversion_hyps2string ctxt l); flush stdout;*)
	if not (IndexSet.is_empty (IndexSet.inter (substitution_vars s) (IndexSet.union (bv_term te1) (bv_term te2)))) then ( 
	  (*if !mk_trace then trace := (Free (String.concat "" [substitution2string ctxt s'; " /\ "; substitution2string ctxt s])):: !trace;*)
          if !mk_trace then trace := (Free (conversion_hyps2string ctxt !ctxt.conversion_hyps)) :: !trace;
	  let te1' = term_substitution s te1 in
	  let te2' = term_substitution s te2 in
	    (*printf "(%s, %s) --> (%s, %s)\n" (term2string ctxt te1) (term2string ctxt te2) (term2string ctxt te1') (term2string ctxt te2');*)
	  try 
	    let res = unification defs ctxt ~polarity:polarity te1' te2' in
	    if !mk_trace then trace := List.tl !trace;
	    res
	  with
	    | _ -> 
	      if !mk_trace then trace := List.tl !trace;
	      if are_convertible defs ctxt te1' te2' or are_convertible defs ctxt te2' te1' then te1' else
		raise (PoussinException (UnknownUnification (!ctxt, te1', te2')));
	) else (
	  (*printf "\n%s Vs %s WTF\n" (term2string ctxt te1) (term2string ctxt te2); flush stdout;*)
	  if are_convertible defs ctxt te1 te2 or are_convertible defs ctxt te2 te1 then te1 else
	  raise (PoussinException (UnknownUnification (!ctxt, te1, te2)));
	)	
	  
  in
  if !mk_trace then trace := List.tl !trace;
  res

(* these stuffs are quite ... *)
and are_convertible 
    (defs: defs)
    (ctxt: context ref)
    (te1: term) (te2: term) : bool =
  match 
    let s, l = conversion_hyps2subst !ctxt.conversion_hyps in
    (*printf "(2)\n%s Vs %s\nl := %s \n==========> \ns := %s, \nl:= %s\n\n" (term2string ctxt te1) (term2string ctxt te2) (conversion_hyps2string ctxt (!ctxt.conversion_hyps)) (substitution2string ctxt s) (conversion_hyps2string ctxt l); flush stdout;*)
    fold_stop (fun i (hd1, hd2) ->
      (*printf "(%s, %s) <--> (%s, %s)\n" (term2string ctxt te1) (term2string ctxt te2) (term2string ctxt hd1) (term2string ctxt hd2);*)
      try 
	if !mk_trace then trace := (Free (String.concat "" ["try conversion: "; (term2string ctxt hd1); " <-> "; (term2string ctxt hd2)])):: !trace;
	let ctxt' = ref {!ctxt with conversion_hyps = delete i l } in
	let _ = unification defs ctxt' (get_type te1) (get_type hd1) in
	let _ = unification defs ctxt' te1 hd1 in
	let _ = unification defs ctxt' te2 hd2 in
	ctxt := { !ctxt' with conversion_hyps = !ctxt.conversion_hyps };
	if !mk_trace then trace := List.tl !trace;
	Right ()
      with
	| _ -> 	if !mk_trace then trace := List.tl !trace; Left (i + 1)
    ) 0 l with
      | Left _ -> false
      | Right () -> true

and higher_order_unification (defs: defs) (ctxt: context ref) ?(polarity : bool = true) (i: index) (arg: term) (n: nature) (args: (term* nature) list) (te: term) te1 te2 =
  (* here the principle is to "extract" the arg from the other term, transforming it into a Lambda and retry the unification *)
  (* shift te 1 : now there is no TVar 0 in te *)
  let te' = shift_term te 1 in
  (* thus we can rewrite (shift arg 1) by TVar 0 *)
  let te' = rewrite_term ctxt (shift_term arg 1) (var_ 0) te' in
  (* we just verify that we have some instance of TVar 0 *)
  if not (IndexSet.mem 0 (bv_term te')) then raise (PoussinException (UnknownUnification (!ctxt, te1, te2)));
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
  context_add_substitution ctxt (IndexMap.singleton i res);
  printf "(%s Vs %s) -> %s\n" (term2string ctxt te1) (term2string ctxt te2) (term2string ctxt (app_ res ((arg, n)::[])));
  te


(* some basic rewriting *)
and rewrite_term ctxt (lhs: term) (rhs: term) (te: term) : term =
  (*printf "rewrite [%s => %s] in %s\n" (term2string ctxt lhs) (term2string ctxt rhs) (term2string ctxt te);*)
  if term_equal lhs te then
    rhs
  else
    let ast =
      match te.ast with
	| Lambda ((n, ty, nat), body) ->
	  Lambda ((n, rewrite_term ctxt lhs rhs ty, nat),
		  rewrite_term ctxt (shift_term lhs 1) (shift_term rhs 1) body)
	| Forall ((n, ty, nat), body) ->
	  Forall ((n, rewrite_term ctxt lhs rhs ty, nat),
		  rewrite_term ctxt (shift_term lhs 1) (shift_term rhs 1) body)
	| Let ((n, value), body) ->
	  Let ((n, rewrite_term ctxt lhs rhs value),
	       rewrite_term ctxt (shift_term lhs 1) (shift_term rhs 1) body)
	| App (f, args) ->
	  App (rewrite_term ctxt lhs rhs f,
	       List.map (fun (arg, n) -> rewrite_term ctxt lhs rhs arg, n) args)
	| Match (te, des) ->
	  Match (rewrite_term ctxt lhs rhs te,
		 List.map (fun (ps, te) -> 
		   let i = patterns_size ps in
		   ps, rewrite_term ctxt (shift_term lhs i) (shift_term rhs i) te) des)
	| _ -> te.ast
    in
    match get_type te with
      | {ast = Universe _; _} -> { te with ast = ast }
      | ty -> { te with ast = ast; annot = Typed (rewrite_term ctxt lhs rhs ty) }


(* reduction *)
(* NB: in order to enhanced reduction, it might be proper have a marker on terms 
   stating the term is reduced
*)


and reduction_term (defs: defs) (ctxt: context ref) (strat: reduction_strategy) (te: term) : term = 
  if !debug_reduction then printf "reduction: "; flush stdout;
  let te' = reduction_term_loop defs ctxt strat (set_term_reduced ~recursive:true false te) in
  if !debug_reduction then  printf "\n"; flush stdout;
  (set_term_reduced ~recursive:true false te')
and reduction_term_loop (defs: defs) (ctxt: context ref) (strat: reduction_strategy) (te: term) : term = 
  if !debug_reduction then (printf "{ %s }\n" (term2string ctxt te); flush stdout);
  (*if !mk_trace then trace := (Reduction (!ctxt, te)) :: !trace;*)
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
		(* delta strong -> we return it 
		   delta_weak -> we make sure the resulting term is 'clean'
		*)
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
	    match pattern_match ctxt p dte with
	      | None -> Left ()
	      | Some l ->
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
		Right te
	  ) () ps
	) () des in
	match res with
	  | Left () -> set_term_reduced true te
	  | Right te -> reduction_term_loop defs ctxt strat te
      )

	(*
      | App (App (f, args1, ty1, pos1, _), args2, ty2, pos2, _) ->
	reduction_term_loop defs ctxt strat (App (f, args1 @ args2, ty2, pos2, false))
	*)

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

      (* using conversion (adhoc) *)
      | _ -> 
	(* create the substitution *)
	let s, l = conversion_hyps2subst !ctxt.conversion_hyps in
	(*  if its not empty and the bv_term + fv_term has an intersection with the domain of the substitution -> apply *)
	if not (IndexMap.is_empty s) then (
	  (*
	  printf "reduction of %s\n" (term2string ctxt te);
	  printf "rewriting s for reduction := %s\n" (substitution2string ctxt s);
	  *)
	  let vars = IndexSet.union (bv_term te) (fv_term te) in
	  let intersect = 
	    match fold_stop (fun () i -> 
	      if IndexMap.mem i s then Right () else Left ()
	    ) () (IndexSet.elements vars) with 
	      | Left () -> false
	      | Right () -> true
	  in
	  if intersect then
	    let te = term_substitution s te in
	    te
	  else
	    te
	) else te	  

  ) in
  let te' = 
    match strat.delta with
      | Some DeltaWeak when is_clean_term te' -> te'
      | Some DeltaStrong -> set_term_reduced true te'
      | _ -> set_term_reduced true te      
  in
  if !debug_reduction then (printf "{ %s }\n" (term2string ctxt te'); flush stdout);
  (*if !mk_trace then trace := List.tl !trace;*)
  te'

and reduction_typeannotation (defs: defs) (ctxt: context ref) (strat: reduction_strategy) (ty: typeannotation) : typeannotation =
  match ty with
    | NoAnnotation -> NoAnnotation
    | Annotation te -> Annotation (reduction_term_loop defs ctxt strat te)
    | Typed te -> Typed (reduction_term_loop defs ctxt strat te)

