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
  fvs: (index * term * term option * name option) list; (*  *)
  conversion_hyps: (term * term) list; (* *)
  lvl_cste: uLevel_constraints list; (* *)
}

(* values for constante *)
type value = Inductive of name list * term
	    | Axiom of term
	    | Definition of term
	    | Constructor of name * term

and defs = (name, value) Hashtbl.t;;

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
		    | CannotTypeCheck of context * term * term * poussin_error
		    | MissingMatchCase of (context * pattern * term * term)
		    | NoDecreasingArguments of (context * name * (term * nature) list)

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

type oracle = 
    defs -> context -> (* definitions + context *)
    index option -> (* the free var we are trying to solve *)
    term -> (* the desired type *)
    term option (* the result term *)

(* registered oracles *)
let registered_oracles : oracle list ref = ref []

(* this is a list of contexted unmatch patterns (with the destructed term type, and the desired return type) *)
let unmatched_pattern : (context * pattern * term * term) list ref = ref []

(* this is the list of all non irreducible name called *)
let registered_calls : (context * name * (term * nature) list) list ref = ref []
