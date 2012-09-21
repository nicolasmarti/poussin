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
	      | Implicit (* arguments which value can be inferred by unification *)
	      | NJoker (* used for unification *)

type uType = Type | Set | Prop 

type uLevel = UName of name | USucc of uLevel | UMax of uLevel list

type uLevel_constraints = UEq of uLevel * uLevel
			  | ULt of uLevel * uLevel

type position = NoPosition
		| Position of ((int * int) * (int * int)) * name list

type reduced = bool

type pattern = PAvar | PName of string | PCste of name
	       | PApp of name * (pattern * nature) list


type term_ast = Universe of uType * uLevel 

            (* constante *)
	    | Cste of name

	    (* Free Var (index < 0) and Bounded Var (index > 0) *)
	    | Var of index
		
	    (* these constructors are only valide after parsing, and removed by typechecking *)
	    | AVar (* _ *)
	    | TName of name

	    (* quantifiers *)
	    | Lambda of (name * term * nature) * term
	    | Forall of (name * term * nature) * term
	    | Let of (name * term) * term

	    (* application *)
	    | App of term * (term * nature) list

	    (* destruction *)
	    | Match of term * (pattern list * term) list

and term = 
{ ast: term_ast;
  annot: typeannotation;
  tpos: position;
  reduced: bool;
}

and typeannotation = NoAnnotation
		     | Annotation of term
		     | TypedAnnotation of term
		     | Typed of term


and substitution = term IndexMap.t

and var_frame = {

  name: name;
  ty: term;
  nature: nature;
    
}

(* context *)
and context = {
  bvs: var_frame list; (* size = n *)
  fvs: (index * term * term option) list; (*  *)
  conversion_hyps: (term * term) list; (* *)
  lvl_cste: uLevel_constraints list; (* *)
}

(* for notation *)
type op = Nofix
	  | Prefix of int
	  | Infix of int * associativity
	  | Postfix of int


(* values for constante *)
type value = Inductive of name list * term
	    | Axiom of term
	    | Definition of term
	    | Constructor of name * term

and defs = (name, value) Hashtbl.t;;


type env = {
  defs: defs;
  (* dependencies *)
  deps: (name, NameSet.t) Hashtbl.t;
}

type poussin_error = FreeError of string
		    | Unshiftable_term of term * int * int
		    | UnknownCste of name
		    | NoUnification of context * term * term
		    | NoNatureUnification of context * term * term
		    | UnknownUnification of context * term * term
		    | CsteNotConstructor of name
		    | CsteNotInductive of name
		    | NegativeIndexBVar of int
		    | UnknownBVar of context * int
		    | UnknownFVar of context * int
		    | NotInductiveDestruction of context * term
		    | InteractiveFailure
		    (*| ConstructorCclHeadNotInductive of term*)

exception PoussinException of poussin_error

type ty_action =
  | TC of context * term * term
  | TI of context * term
  | U of context * term * term
  | UNeg of context * term * term
  | Free of string
  | Reduction of context * term * term

let trace : ty_action list ref = ref []

let mk_trace : bool ref = ref true

let debug_reduction = ref false

(* the global parserbuffer *)
let global_parserbuffer : parserbuffer ref = ref (build_parserbuffer (Stream.of_list []))

(* interactive routine *)
let oracles : (defs -> context -> index option -> term -> term option) list ref = ref []

