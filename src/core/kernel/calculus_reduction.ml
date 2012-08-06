open Calculus_def
open Calculus_misc
open Calculus_substitution
open Extlist

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

(* is clean term:
   no lambda, no match, ....
 *)
let rec is_clean_term (te: term) : bool =
  match te with
    | Universe _ | Cste _ | Var _ | AVar _ | TName _ -> true
    | Let _ | Lambda _ | Match _ -> false
    | Forall (_, te, _, _, _) -> is_clean_term te
    | App (f, args, _, _, _) ->
      List.fold_left (fun acc (hd, _) -> acc && is_clean_term hd) (is_clean_term f) args

(* simpl pattern match *)
let rec pattern_match (p: pattern) (te: term) : (term list) option =
  match p with
    | PAvar -> Some []
    | PName s -> Some [te]
    | PCstor (c, args) ->
      match te with
	| Cste (c2, _, _, _) when c = c2 && List.length args = 0 -> Some []
	| App (Cste (c2, _, _, _), args2, _, _, _) when c = c2 && List.length args = List.length args2 ->
	  List.fold_left (fun acc (hd1, hd2) -> 
	    match acc with
	      | None -> None
	      | Some l ->
		match pattern_match hd1 hd2 with
		  | None -> None
		  | Some l' -> Some (l @ l')
	  ) (Some []) (List.map2 (fun hd1 hd2 -> (fst hd1, fst hd2)) args args2)
	| _ -> None
	  


(* reduction *)
(* NB: in order to enhanced reduction, it might be proper have a marker on terms 
   stating the term is reduced
*)

let rec reduction_term (defs: defs) (strat: reduction_strategy) (te: term) : term = 
  match te with
    | Universe _ | Var _ | AVar _ | TName _ -> te

    | _ when is_reduced te -> te

    | Cste (n, ty, position, _) -> (
      match strat.delta with
	(* no unfolding *)
	| None -> te

	| Some delta -> (
	  try 
	    match Hashtbl.find defs n with
	      (* delta strong -> we return it 
		 delta_weak -> we make sure the resulting term is 'clean'
	      *)
	      | Definition te ->
		let te' = reduction_term defs strat te in
		set_reduced (
		  match delta with
		    | DeltaStrong -> te'
		    | DeltaWeak when is_clean_term te' -> te'
		    | _ -> te
		)
	      | _ -> set_reduced te
	  with
	    | Not_found -> raise (PoussinException (UnknownCste n))
	      
	)
	  
    )

    | Lambda _ | Forall _ when strat.beta != Some BetaStrong -> set_reduced te

    | Lambda ((n, ty, nature, pos), te, ty2, pos2, _) ->
      (
	let te = reduction_term defs strat te in
	Lambda ((n, ty, nature, pos), te, ty2, pos2, true)
      )

    | Forall ((n, ty, nature, pos), te, ty2, pos2, _) ->
      (
	let te = reduction_term defs strat te in
	Forall ((n, ty, nature, pos), te, ty2, pos2, true)
      )

    | Let _ when strat.zeta = false && strat.beta != Some BetaStrong -> set_reduced te
    | Let ((n, te, pos), te2, ty, pos2, _) when strat.zeta = false && strat.beta = Some BetaStrong ->
      Let ((n, te, pos), reduction_term defs strat te2, ty, pos2, true)

    | Let ((n, te, pos), te2, ty, pos2, _) when strat.zeta = true ->
      (* here we compute the reduction of te and shift it such that it is at the same level as te2 *)
      let te = shift_term (reduction_term defs strat te) 1 in
      (* we substitute all occurence of n by te *)
      let te2 = term_substitution (IndexMap.singleton 0 te) te2 in
      (* and we shift back to the proper level *)
      let te2 = shift_term te2 (-1) in
      reduction_term defs strat te2

    | Match _ when strat.iota = false -> set_reduced te
    | Match (dte, des, ty, pos, _) -> (
      let dte = reduction_term defs strat dte in
      let res = fold_stop (fun () (ps, body) ->
	fold_stop (fun () p ->
	  match pattern_match p dte with
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
		(List.map (fun te -> shift_term te (List.length l)) (List.rev l)) in
	      Right te
	) () ps
      ) () des in
      match res with
	| Left () -> set_reduced te
	| Right te -> reduction_term defs strat te
    )

    | App (Lambda ((n, ty, nature, pos), te, ty2, pos2, _), (hd1, hd2)::tl, app_ty, app_pos, _) ->
      let hd1 = shift_term (reduction_term defs strat hd1) 1 in
      let f = term_substitution (IndexMap.singleton 0 hd1) te in
      reduction_term defs strat (App (shift_term f (-1), tl, app_ty, app_pos, false))

    | App (f, [], _, _, _) ->
      set_reduced (reduction_term defs strat f)

    | App (f, args, ty, pos, _) -> (
      let f = reduction_term defs strat f in
      (* here we are doing eager by default *)
      let args = List.map (fun (te, n) -> reduction_term defs strat te, n) args in
      set_reduced (reduction_term defs strat (App (f, args, ty, pos, false)))
    )


and reduction_typeannotation (defs: defs) (strat: reduction_strategy) (ty: typeannotation) : typeannotation =
  match ty with
    | NoAnnotation -> NoAnnotation
    | Annotation te -> Annotation (reduction_term defs strat te)
    | Typed te -> Typed (reduction_term defs strat te)
