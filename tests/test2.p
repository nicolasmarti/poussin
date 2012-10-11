Inductive List: Type -> Set :=
| nil {A}: List A 
| cons {A}: A -> List A -> List A

Inductive Tuple: List Set -> Set :=
| tnil: Tuple nil
| tcons {hd} {tl}: hd -> Tuple tl -> Tuple (cons hd tl)

Inductive Function: List Set -> Set -> Set :=
| fun {argtys} {retty}: (Tuple argtys -> retty) -> Function argtys retty

Signature Apply {argtys} {retty} (f: Function argtys retty) (args: Tuple argtys): retty 
Definition Apply {argtys} {retty} (f: Function argtys retty) (args: Tuple argtys): retty :=
  match f with
    | fun {_} {_} fct := fct args
  end

Signature UncurryingType (argtys: List Set) (retty: Set) : Set
Definition UncurryingType (argtys: List Set) (retty: Set) : Set :=
   match argtys with
     | nil {_} := retty
     | cons {_} hd tl := hd -> UncurryingType tl retty
   end

Signature UncurryingFunction {argtys} {retty} (f: Function argtys retty): UncurryingType argtys retty

Signature A: Set
Signature B: Set
Signature C: Set

Definition caca :=  UncurryingType (cons A (cons B (cons C))) C