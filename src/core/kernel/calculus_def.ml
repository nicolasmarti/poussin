open Libpprinter
open Libparser

(*********************************)
(* Definitions of data structure *)
(*********************************)

type name = string

module NameMap = Map.Make(
  struct
    type t = string
    let compare x y = compare x y
  end
);;

module NameSet = Set.Make(
  struct
    type t = string
    let compare x y = compare x y
  end
);;

type index = int

module IndexSet = Set.Make(
  struct
    type t = int
    let compare x y = compare x y
  end
);;

module IndexMap = Map.Make(
  struct
    type t = int
    let compare x y = compare x y
  end
);;

type nature = Explicit
	      | Implicit

(* but in our case we only use 
   'a = term
   'b = context
   'c = defs
*)
class virtual ['a, 'b, 'c] tObj =
object 
  method uuid: int = 0
  method virtual get_name: string
  method virtual get_type: 'a
  method virtual get_trigger: int
  method virtual pprint: unit -> token
  method virtual equal: ('a, 'b, 'c) tObj -> bool
  method virtual apply: 'c -> 'b -> ('a * nature) list -> 'a
end

type uType = Type | Set | Prop 

type uLevel = UName of name | USucc of uLevel | UMax of uLevel list

type path = name list

type position = NoPosition
		| Position of ((int * int) * (int * int)) * name list

type term = Universe of uType * uLevel * position 

            (* constante *)
	    | Cste of path * name * typeannotation * position

	    (* Free Var (index < 0) and Bounded Var (index > 0) *)
	    | Var of index * typeannotation * position 
		
	    (* these constructors are only valide after parsing, and removed by typechecking *)
	    | AVar of typeannotation * position (* _ *)
	    | TName of name * typeannotation * position

	    (* quantifiers *)
	    | Lambda of (name * term * nature * position) * term * typeannotation * position
	    | Forall of (name * term * nature * position) * term * typeannotation * position
	    | Let of (name * term * position) * term * typeannotation * position

	    (* application *)
	    | App of term * (term * nature) list * typeannotation * position

	    (* destruction *)
	    | Match of term * (pattern list * term) list * typeannotation * position

and pattern = PAvar | PName of string
	      | PCstor of (path * name) * (pattern * nature) list

and conversion_formula = 
  Conv_Lit of bool * term * term
  | Conv_And of conversion_formula list
  | Conv_Or of conversion_formula list

and typeannotation = NoAnnotation
		     | Annotation of term
		     | Typed of term

and var_frame = {

  name: name;
  ty: term;
  nature: nature;
  pos: position;
  
  fvs: (index * term * position) list;

  termstack: term list;
  naturestack: nature list;
  conversions_hyp: conversion_formula

}

(* context *)
and context = var_frame list

(* for notation *)
type op = Nofix
	  | Prefix of int
	  | Infix of int * associativity
	  | Postfix of int


(* values contains in module *)
type value = Inductive of (name * term) list
	    | Axiom
	    | Definition of term
	    | Constructor of name
	    | Primitive of (term, context, module_) tObj
	    | Import of module_

and defs = (name, (term * value * (string * op) option (* parsing *) * (string * op) option (* pprinting *))) Hashtbl.t

and module_ = {
  name: name;
  path: path;
  defs: defs;
  univ_eqs: unit;
  exports: unit
}

type doudou_error = NegativeIndexBVar of index
		    | Unshiftable_term of term * int * int

		    | UnknownCste of path * name
		    | UnknownBVar of index * context
		    | UnknownFVar of index * context

		    | UnknownUnification of context * term * term
		    | NoUnification of context * term * term

		    | NoMatchingPattern of context * term * term

		    | PoppingNonEmptyFrame of var_frame

		    | CannotInfer of context * term * doudou_error
		    | CannotTypeCheck of context * term * term * term * doudou_error

		    | FreeError of string

exception DoudouException of doudou_error

let oracles_list : ((module_ * context * term) -> term option) list ref = ref []

type debug_flags = {
  (* pretty printer flags *)
  mutable show_universe: bool;
  mutable show_implicit: bool;
  mutable show_varindices: bool;
  mutable show_position: bool;
  mutable show_proofs: bool;
}

let flags : debug_flags = {
  show_universe = true;
  show_implicit = true;
  show_varindices = true;
  show_position = true;
  show_proofs = true;
}
