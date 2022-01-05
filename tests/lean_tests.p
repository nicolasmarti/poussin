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

Definition AndComm {p q: Type} (H: And p q): And q p :=
match H with
| conj {_} {_} Hp Hq := conj Hq Hp
end