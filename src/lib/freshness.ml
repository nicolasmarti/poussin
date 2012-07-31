(*
 This file is part of Mymms.

 Mymms is free software: you can redistribute it and/or modify
 it under the terms of the GNU General Public License as published by
 the Free Software Foundation, either version 3 of the License, or
 (at your option) any later version.

 Mymms is distributed in the hope that it will be useful,
 but WITHOUT ANY WARRANTY; without even the implied warranty of
 MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 GNU General Public License for more details.

 You should have received a copy of the GNU General Public License
 along with Mymms.  If not, see <http://www.gnu.org/licenses/>.

 Copyright (C) 2008 Nicolas Marti
*)


open List;;
open String;;
open Printf;;
open Varset;;

(* is n fresh in l ?*)
let is_fresh_name l n =
  not (VarSet.subset (VarSet.singleton n) l);;

(* generation of a fresh name *)

let rec add_string_index (y: string) index =
  let len = (length y - index) in
  match (String.get y ) len with
    | '0' -> (set y len '1'); y
    | '1' -> (set y len '2'); y
    | '2' -> (set y len '3'); y
    | '3' -> (set y len '4'); y
    | '4' -> (set y len '5'); y
    | '5' -> (set y len '6'); y
    | '6' -> (set y len '7'); y
    | '7' -> (set y len '8'); y
    | '8' -> (set y len '9'); y
    | '9' -> (set y len '0'); (add_string_index (y: string) (index + 1));
    | c -> (concat "" (y :: "0" :: [])) ;;


let add_index_string y = add_string_index y 1;;

(* returns a derivatives of x fresh in l *)

let rec fresh_name_list_name' l x =
  (*printf "%s fresh in {" x ; print_list_string l; printf "}? %b\n" (is_fresh_name l x);*)
  if (is_fresh_name l x) then x else (
    (fresh_name_list_name' l (add_index_string x))
  );;

let fresh_name_list_name l x = fresh_name_list_name' l (copy x)


let rec fresh_names l n = 
  match n with
    | 0 -> []
    | _ ->
        let x = fresh_name_list_name l "H" in
        let tl = fresh_names (x ++ l) (n-1) in
          x::tl
;;

let rec fresh_names2 l n c = 
  match n with
    | 0 -> []
    | _ ->
        let x = fresh_name_list_name l c in
        let tl = fresh_names (x ++ l) (n-1) in
          x::tl
;;
