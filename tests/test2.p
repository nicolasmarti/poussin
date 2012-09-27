Signature P: Set
Signature N: Set
Signature Z: Set
Signature Q: Set
Signature R: Set

Signature plusCase: Set -> Set -> Set

Signature PlusType {A: Set} {B: Set}: Set
Definition PlusType {A} {B} : Set :=
  match plusCase A B with
     | plusCase P P := P
     | plusCase N N := N
  end

Signature Plus {A: Set} {B: Set}: (a: A) -> (b: B) -> PlusType {A} {B}

Signature p1: N
Signature p2: N

Definition test := Plus p1 p2