(******************)
(*      misc      *)
(******************)

(* the last element of the list *)
let rec last (l: 'a list) : 'a =
  match l with 
    | [] -> raise (Failure "last: empty list")
    | hd::[] -> hd
    | hd :: tl -> last tl

(* take and drop as in haskell *)
let rec take (n: int) (l: 'a list) :'a list =
  match n with
    | 0 -> []
    | i when i < 0 -> raise (Failure "take")
    | _ -> 
      match l with
	| [] -> []
	| hd::tl -> hd::take (n-1) tl

let rec drop (n: int) (l: 'a list) :'a list =
  match n with
    | 0 -> l
    | i when i < 0 -> raise (Failure "drop")
    | _ -> 
      match l with
	| [] -> []
	| hd::tl -> drop (n-1) tl

(* build a list of the same element of size n *)
let rec replicate (e: 'a) (n: int) : 'a list =
  match n with
    | _ when n < 0 -> raise (Failure "replicate")
    | 0 -> []
    | _ -> e :: replicate e (n-1)

(* some traverse fold without the reverse *)
let mapacc (f: 'b -> 'a -> ('c * 'b)) (acc: 'b) (l: 'a list) : 'c list * 'b =
  let acc = ref acc in
  (List.map (fun hd -> let (hd, acc') = f !acc hd in
		       acc := acc';
		       hd) l, !acc)

(* some map which also gives the remaining list *)
let rec map_remain (f: 'a -> 'a list -> 'b) (l: 'a list) : 'b list =
  match l with
    | [] -> []
    | hd::tl ->
      let hd = f hd tl in
      hd :: map_remain f tl


type ('a, 'b) either = Left of 'a
		       | Right of 'b
;;

(* a fold that might stop before the whole traversal *)
let rec fold_stop (f: 'b -> 'a -> ('b, 'c) either) (acc: 'b) (l: 'a list) : ('b, 'c) either =
  match l with
    | [] -> Left acc
    | hd::tl ->
      match f acc hd with
	| Left acc -> fold_stop f acc tl
	| Right res -> Right res

(* a fold that returns an update of the traversed list *)
let rec fold_cont (f: 'b -> 'a list -> 'a list * 'b) (acc: 'b) (l: 'a list): 'b =
  match l with
    | [] -> acc
    | _ -> 
      let l', acc = f acc l in
      fold_cont f acc l'

(* a function called n times with arguments pushed in a list *)
let rec map_nth (f: int -> 'a) (n: int) : 'a list =
  match n with
    | i when i < 0 -> []
    | 0 -> []
    | _ ->
      let res = f n in
      res::map_nth f (n - 1)

(* function like map, but that can skip elements *)
let rec skipmap (f: 'a -> 'b option) (l: 'a list) : 'b list =
  match l with
    | [] -> []
    | hd::tl -> 
      match f hd with
	| None -> skipmap f tl
	| Some hd -> hd::(skipmap f tl)

(*
  helper functions
*)
let rec intercalate (inter: 'a) (l: 'a list) : 'a list =
  match l with
    | hd1::hd2::tl ->
      hd1::inter::(intercalate inter (hd2::tl))
    | _ -> l

let rec intercalates (inter: 'a list) (l: 'a list) : 'a list =
  match l with
    | hd1::hd2::tl ->
      hd1::inter @ intercalates inter (hd2::tl)
    | _ -> l

(* delete an index *)
let rec delete (i: int) (l: 'a list) : 'a list =
  match l with
    | [] -> []
    | hd :: tl ->
      match i with
	| 0 -> tl
	| _ -> hd :: delete (i-1) tl
