Signature P: Set
Signature N: Set
Signature Z: Set
Signature Q: Set
Signature R: Set

Signature prodSet: Set -> Set -> Set

Signature PlusType {A: Set} {B: Set}: Set
Definition PlusType {A} {B} : Set :=
  match prodSet A B with
     | prodSet P P := P
     | prodSet N N := N
  end

Signature Plus {A: Set} {B: Set}: (a: A) -> (b: B) -> PlusType {A} {B}

Signature test : N -> N -> N

Definition test :=  \ (p1 p2: N) -> Plus p1 p2