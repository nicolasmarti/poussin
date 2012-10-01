open Calculus_kernel

type definition = DefSignature of name * term
		  | DefDefinition of name * term
		  | DefInductive of name * term
		  | DefConstructor of name * term
		  | DefCompute of term

