Inductive True : Prop :=
| I: True

Inductive False : Prop :=

Inductive Not (P: Prop) : Prop :=
| Contradiction  {P}: (P -> False) -> Not P

Inductive And (A B: Prop) : Prop :=
| conj {A} {B}: A -> B -> And A B

Inductive Or (A B: Prop) : Prop :=
| left {A} {B}: A -> Or A B
| right {A} {B}: B -> Or A B

Inductive eq {A: Type} (a: A): A -> Prop :=
| eq_refl {A} (a: A): eq a a

Inductive Peano: Set :=
| O: Peano
| S: Peano -> Peano

Signature peano_plus: Peano -> Peano -> Peano
Decreasing peano_plus [0]

Definition peano_plus (n m: Peano) : Peano :=
  match n with
     | O := m
     | S n := S (peano_plus n m) 
  end
