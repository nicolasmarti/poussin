(*

  This file is free software: you can redistribute it and/or modify
  it under the terms of the GNU General Public License as published by
  the Free Software Foundation, either version 3 of the License, or
  (at your option) any later version.

  This file is distributed in the hope that it will be useful,
  but WITHOUT ANY WARRANTY; without even the implied warranty of
  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
  GNU General Public License for more details.

  You should have received a copy of the GNU General Public License
  along with this file.  If not, see <http://www.gnu.org/licenses/>.

  Copyright (C) Nicolas Marti
*)

open Printf;;
(*open Listext;;*)

let rec repeat (e: 'a) (n: int) : 'a list =
  match n with
    | 0 -> []
    | _ -> e::(repeat e (n-1))
;;

type token = 
  | Verbatim of string
  | Box of token list
  | IBox of token list
  | Newline
  | Space of int
  | ISpace of int
  | Grid of token list list
  | Frac of token * (token list)
  | Bar of bool * token * token (* true = horizontal, false vertical *)
  
;;

type box = {
  data : string list;
  height : int;
  width: int;
};;

type concatType =
  | Bottom 
  | Top
  | Left
  | Right
  | Center
;;

exception IncompatibleConcatType;;

let addleftspace (n: int) (b: box) : box =
  {
    data = List.map (fun hd -> String.concat "" 
		       ((repeat " " n) @ hd :: [])
		    ) b.data;
    width = b.width + n;
    height = b.height;
  }
;;

let addrightspace (n: int) (b: box) : box =
  {
    data = List.map (fun hd -> String.concat "" 
		       (hd :: (repeat " " n))
		    ) b.data;
    width = b.width + n;
    height = b.height;
  }
;;

let addtopspace (n: int) (b: box) : box =
    {
      data = (repeat (String.concat "" (repeat " " b.width)) n) @ b.data;
      height = b.height + n;
      width = b.width;
    }
;;

let addbottomspace (n: int) (b: box) : box =
    {
      data = b.data @ (repeat (String.concat "" (repeat " " b.width)) n);
      height = b.height + n;
      width = b.width;
    }
;;


let vertical_concat (t: concatType) (b1: box) (b2: box) : box =
  if (b1.width == 0) then b2 else
    if (b2.width == 0) then b1 else
      match t with
	| Left -> 
	    if (b1.width < b2.width) then (
	      
	      let b1 = addrightspace (b2.width - b1.width) b1 in
		{ data = b1.data @ b2.data; height = b1.height + b2.height;  width = b2.width}
		  
	    ) else (
	      
	      let b2 = addrightspace (b1.width - b2.width) b2 in
		{ data = b1.data @ b2.data; height = b1.height + b2.height;  width = b1.width}
		  
	    )
	| Right -> 
	    if (b1.width < b2.width) then (
	      
	  let b1 = addleftspace (b2.width - b1.width) b1 in
	    { data = b1.data @ b2.data; height = b1.height + b2.height;  width = b2.width}
	      
	    ) else (
	      
	      let b2 = addleftspace (b1.width - b2.width) b2 in 
		{ data = b1.data @ b2.data; height = b1.height + b2.height;  width = b1.width}
		  
	    )
	| Center -> 
	    if (b1.width < b2.width) then (
	      
	      let n1 = ((b2.width - b1.width) / 2) in
	      let n2 = (b2.width - b1.width) - ((b2.width - b1.width) / 2) in
	      let b1 = addleftspace n1 b1 in
	      let b1 = addrightspace n2 b1 in
		{ data = b1.data @ b2.data; height = b1.height + b2.height;  width = b2.width}
		  
	    ) else (
	      
	      let n1 = ((b1.width - b2.width) / 2) in
	      let n2 = (b1.width - b2.width) - ((b1.width - b2.width) / 2) in
	      let b2 = addleftspace n1 b2 in
	      let b2 = addrightspace n2 b2 in
		{ data = b1.data @ b2.data; height = b1.height + b2.height;  width = b1.width}
		  
	    )
	| _ -> raise IncompatibleConcatType
;;

let horizontal_concat (t: concatType) (b1: box) (b2: box) : box =
  if (b1.height == 0) then b2 else
    if (b2.height == 0) then b1 else
      match t with
	| Top -> 
	    if (b1.height < b2.height) then (
	      
	      let b1 = addbottomspace (b2.height - b1.height) b1 in
		{ data = List.map (fun (hd1, hd2) -> String.concat "" (hd1 :: hd2 :: [])) (List.combine b1.data b2.data); 
		  height = b2.height;  
		  width = b1.width + b2.width
		}
		  
	    ) else (
	      
	      let b2 = addbottomspace (b1.height - b2.height) b2 in
		{ data = List.map (fun (hd1, hd2) -> String.concat "" (hd1 :: hd2 :: [])) (List.combine b1.data b2.data); 
		  height = b2.height;  
		  width = b1.width + b2.width
		}
		  
	    )
	| Bottom -> 
	    if (b1.height < b2.height) then (
	  
	      let b1 = addtopspace (b2.height - b1.height) b1 in
		{ data = List.map (fun (hd1, hd2) -> String.concat "" (hd1 :: hd2 :: [])) (List.combine b1.data b2.data); 
		  height = b2.height;  
		  width = b1.width + b2.width
		}
		  
	    ) else (
	      
	      let b2 = addtopspace (b1.height - b2.height) b2 in
		{ data = List.map (fun (hd1, hd2) -> String.concat "" (hd1 :: hd2 :: [])) (List.combine b1.data b2.data); 
		  height = b2.height;  
		  width = b1.width + b2.width
		}
		  
	    )
	| Center -> 

	    if (b1.height = b2.height) then (
	      { data = List.map (fun (hd1, hd2) -> String.concat "" (hd1 :: hd2 :: [])) (List.combine b1.data b2.data); 
		height = b1.height;  
		width = b1.width + b2.width;
	      }
	    ) else
	      if (b1.height < b2.height) then (
		
		let n1 = ((b2.height - b1.height) / 2) in
		let n2 = b2.height - b1.height - n1 in
		let b1 = addtopspace n1 b1 in
		let b1 = addbottomspace n2 b1 in
		  { data = List.map (fun (hd1, hd2) -> String.concat "" (hd1 :: hd2 :: [])) (List.combine b1.data b2.data); 
		    height = b1.height;  
		    width = b1.width + b2.width;
		  }
		    
	      ) else (
		
		let n1 = ((b1.height - b2.height) / 2) in
		let n2 = b1.height - b2.height - n1 in
		let b2 = addtopspace n1 b2 in
		let b2 = addbottomspace n2 b2 in
		  { data = List.map (fun (hd1, hd2) -> String.concat "" (hd1 :: hd2 :: [])) (List.combine b1.data b2.data); 
		    height = b1.height;  
		    width = b1.width + b2.width;
		  }
		    
	      )
	| _ -> raise IncompatibleConcatType
;;
  
let printbox (b: box) : unit =
  List.fold_left (
    fun acc hd ->
      printf "%s\n" hd;
  ) () b.data
;;

let box2string (b: box) : string =
  String.concat "\n" b.data
;;

let rec break_string (s: string) : string list =  
  if (String.length s = 0) then [] else
    try 
      let i = String.index s '\n' in
      let s1 = String.sub s 0 i in
      let s2 = break_string (String.sub s (i + 1) (String.length s - i - 1)) in
	s1::s2	
    with
      | _ -> s :: []
;;

let string_to_box s = 
  let l = break_string s in
  let lmax = List.fold_left (fun acc hd -> max acc (String.length hd)) 0 l in
  let l' = List.map (fun hd -> if (String.length hd < lmax) then String.concat "" (hd :: (repeat " " (lmax - String.length hd ))) else hd) l in
    { data = l';
      height = List.length l;
      width = lmax
    }
;;

let fill_box s height width =
  { data = repeat (String.concat "" (repeat s width )) height;
    height = height;
    width = width;
  };;

exception PprintFailure;;

let rec token2box (t: token) (w: int) (indent: int) : box =
  match t with
    | Verbatim s ->
	string_to_box s
    | IBox l -> (

	let spacebox n = { data = (String.concat "" (repeat " " n))::[];
			   height = 1;
			   width = n;
			 } in

	let indentbox = spacebox indent in

	let emptybox = spacebox 0 in

	let (_, lineboxes, totalboxes) = List.fold_left (

	  fun (remainingwidth, lineboxes, totalboxes) hd ->
	    
	    match hd with

	      | Newline ->
		  (w - indent, [], totalboxes @ lineboxes::[])

	      | Space n ->
		  if (remainingwidth < n) then
		    (w - indent, indentbox :: [], totalboxes @ lineboxes::[])
		  else
		    if remainingwidth = w - indent && List.length lineboxes = 0 then (
		      (*printf "%d = %d - %d && [linesbox] == %d && [totalboxes] == %d \n" remainingwidth w indent (List.length lineboxes) (List.length totalboxes);*)
		      (w - indent, lineboxes, totalboxes)
		      (*(remainingwidth - n, lineboxes @ (spacebox n) :: [], totalboxes)*)
		    )
		    else
		      (remainingwidth - n, lineboxes @ (spacebox n) :: [], totalboxes)

	      | ISpace n ->
		  if (remainingwidth < n) then
		    (w - indent, indentbox :: [], totalboxes @ lineboxes::[])
		  else
		    (remainingwidth - n, lineboxes @ (spacebox n) :: [], totalboxes)

	      | t ->
		  let b = token2box t remainingwidth indent in
		    if (b.width > remainingwidth || b.height > 1) then (

		      let b = token2box t (w - indent) indent in
			if (b.height > 1) then 
			  (w - indent, indentbox::[], totalboxes @ lineboxes::(indentbox :: b :: [])::[])
			else
			  (w - indent - b.width, indentbox :: b :: [], totalboxes @ lineboxes::[])

		    ) else (

		      (remainingwidth - b.width, lineboxes @ b :: [], totalboxes)

		    )	    

	) (w, [], []) l in

	let l = totalboxes @ lineboxes::[] in

	  List.fold_left (
	    
	    fun acc hd ->

	      vertical_concat Left acc (
		
		List.fold_left (

		  fun acc hd ->
		    
		    horizontal_concat Center acc hd

		) emptybox hd

	      )

	  ) emptybox l

      )
    | Box l -> (

	let spacebox n = { data = (String.concat "" (repeat " " n))::[];
			   height = 1;
			   width = n;
			 } in

	let indentbox = spacebox indent in

	let emptybox = spacebox 0 in

	let (_, lineboxes, totalboxes) = List.fold_left (

	  fun (remainingwidth, lineboxes, totalboxes) hd ->
	    
	    match hd with

	      | Newline ->
		  (w - indent, [], totalboxes @ lineboxes::[])

	      | Space n ->
		  if (remainingwidth < n) then
		    (w - indent, indentbox :: [], totalboxes @ lineboxes::[])
		  else
		    if remainingwidth = w - indent && List.length lineboxes = 0 then (
		      (*printf "%d = %d - %d && [linesbox] == %d && [totalboxes] == %d \n" remainingwidth w indent (List.length lineboxes) (List.length totalboxes);*)
		      (w - indent, lineboxes, totalboxes)
		      (*(remainingwidth - n, lineboxes @ (spacebox n) :: [], totalboxes)*)
		    )
		    else
		      (remainingwidth - n, lineboxes @ (spacebox n) :: [], totalboxes)

	      | ISpace n ->
		  if (remainingwidth < n) then
		    (w - indent, indentbox :: [], totalboxes @ lineboxes::[])
		  else
		    (remainingwidth - n, lineboxes @ (spacebox n) :: [], totalboxes)

	      | t ->
		  let b = token2box t remainingwidth indent in
		    if (b.width > remainingwidth || b.height > 1) then (

		      let b = token2box t (w - indent) indent in
			if (b.height > 1) then 
			  (w, [], totalboxes @ lineboxes::(indentbox :: b :: [])::[])
			else
			  (w - b.width, b :: [], totalboxes @ lineboxes::[])

		    ) else (

		      (remainingwidth - b.width, lineboxes @ b :: [], totalboxes)

		    )	    

	) (w, [], []) l in

	let l = totalboxes @ lineboxes::[] in

	  List.fold_left (
	    
	    fun acc hd ->

	      vertical_concat Left acc (
		
		List.fold_left (

		  fun acc hd ->
		    
		    horizontal_concat Center acc hd

		) emptybox hd

	      )

	  ) emptybox l

      )
    | Frac (hd, tl) -> (

	let spacebox n = { data = (String.concat "" (repeat " " n))::[];
			   height = 1;
			   width = n;
			 } in
	let emptybox = spacebox 0 in
	
	(* Generate the tokens *)
	let hd = token2box hd w 0 in
	let tl = List.map (fun t -> token2box t w 0) tl in
	  
	(* we merge all the tl, inserting a space *)
	let mspace = string_to_box "   " in
	let bottom = List.fold_left (
	  fun acc hd ->
	    let i = horizontal_concat Top acc hd in
	      horizontal_concat Top i mspace
	) emptybox tl in
	let middle_bar = (string_to_box (String.make bottom.width '-'))
	  (*
	  vertical_concat 
	    Center 
	    (string_to_box (String.make bottom.width ' ')) (
	      vertical_concat Center (string_to_box (String.make bottom.width '-')) (string_to_box (String.make bottom.width ' '))
	    )
	  *)
	in
	  vertical_concat Center (vertical_concat Center hd middle_bar) bottom
      )
    | Bar (false, t1, t2) ->
      let b1 = token2box t1 w indent in
      let b2 = token2box t2 w indent in
      let height = max b1.height b2.height in
      horizontal_concat Top (horizontal_concat Top b1 (fill_box "|" height 1)) b2
    | Bar (true, t1, t2) ->
      let b1 = token2box t1 w indent in
      let b2 = token2box t2 w indent in
      let width = max b1.width b2.width in
      vertical_concat Left (vertical_concat Left b1 (fill_box "-" 1 width)) b2
    | _ -> raise PprintFailure
;;
