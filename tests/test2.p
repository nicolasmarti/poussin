Inductive P: Set
Inductive N: Set
Inductive Z: Set
Inductive Q: Set
Inductive R: Set

Inductive plusCase: Set
Constructor plusCaseC: Set -> Set -> plusCase

Signature PlusType {A: Set} {B: Set}: Set
Definition PlusType {A} {B} : Set :=
  match plusCaseC A B with
     | plusCaseC P P := P
     | plusCaseC N N := N
     | plusCaseC P N := N
     | plusCaseC N P := N
  end

Signature Plus {A: Set} {B: Set}: (a: A) -> (b: B) -> PlusType {A} {B}

Signature p1: N
Signature p2: P

Compute PlusType {P} {N} 

Definition test : N := Plus p1 p2
