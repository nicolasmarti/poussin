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

and defs = (name, value) Hashtbl.t;;

type doudou_error = FreeError of string
		    | Unshiftable_term of term * int * int

exception DoudouException of doudou_error
