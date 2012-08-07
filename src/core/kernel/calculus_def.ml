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

type uLevel_constraints = UEq of uLevel * uLevel
			  | ULt of uLevel * uLevel

type position = NoPosition
		| Position of ((int * int) * (int * int)) * name list

type reduced = bool

type term = Universe of uType * uLevel * position 

            (* constante *)
	    | Cste of name * typeannotation * position * reduced

	    (* Free Var (index < 0) and Bounded Var (index > 0) *)
	    | Var of index * typeannotation * position
		
	    (* these constructors are only valide after parsing, and removed by typechecking *)
	    | AVar of typeannotation * position (* _ *)
	    | TName of name * typeannotation * position

	    (* quantifiers *)
	    | Lambda of (name * term * nature * position) * term * typeannotation * position * reduced
	    | Forall of (name * term * nature * position) * term * typeannotation * position * reduced
	    | Let of (name * term * position) * term * typeannotation * position * reduced

	    (* application *)
	    | App of term * (term * nature) list * typeannotation * position * reduced

	    (* destruction *)
	    | Match of term * (pattern list * term) list * typeannotation * position * reduced

and pattern = PAvar | PName of string
	      | PCstor of name * (pattern * nature) list

and typeannotation = NoAnnotation
		     | Annotation of term
		     | Typed of term


and substitution = term IndexMap.t

and var_frame = {

  name: name;
  ty: term;
  nature: nature;
  pos: position;
    
}

(* context *)
and context = {
  bvs: var_frame list; (* size = n *)
  fvs: (index * term * term option * name option) list list; (* size = n+1 *)
  conversion_hyps: (term * term) list list; (* size = n *)
  lvl_cste: uLevel_constraints list; (* size = ??? *)
}
  
  

(* for notation *)
type op = Nofix
	  | Prefix of int
	  | Infix of int * associativity
	  | Postfix of int


(* values contains in module *)
type value = Inductive of name list * term
	    | Axiom of term
	    | Definition of term
	    | Constructor of term

and defs = (name, value) Hashtbl.t;;

type poussin_error = FreeError of string
		    | Unshiftable_term of term * int * int
		    | UnknownCste of name
		    | NoUnification of context * term * term
		    | NoNatureUnification of context * term * term
		    | UnknownUnification of context * term * term
		    | NegativeIndexBVar of int
		    | UnknownBVar of context * int
		    | UnknownFVar of context * int


exception PoussinException of poussin_error
