Inductive List: Type -> Set 
Constructor nil {A}: List A 
Constructor cons {A}: A -> List A -> List A

Inductive Tuple: List Set -> Set
Constructor tnil: Tuple nil
Constructor tcons {hd} {tl}: hd -> Tuple tl -> Tuple (cons hd tl)

Inductive Function: List Set -> Set -> Set
Constructor fun {argtys} {retty}: (Tuple argtys -> retty) -> Function argtys retty

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

Inductive A: Set
Inductive B: Set
Inductive C: Set

Definition caca :=  UncurryingType (cons A (cons B (cons C))) C