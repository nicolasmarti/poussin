open Calculus_def

type definition = DefSignature of name * term
		  | DefDefinition of name * term
		  | DefInductive of name * term * (name * term) list
		  | DefCompute of term

