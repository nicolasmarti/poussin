Inductive True : Prop :=
| I: True.

Inductive False : Prop := .

Inductive Not (P: Prop) : Prop :=
| Contradiction {P}: (P -> False) -> Not P.

Inductive And (A B: Prop) : Prop :=
| conj {A} {B}: A -> B -> And A B.

Inductive Or (A B: Prop) : Prop :=
| left {A} {B}: A -> Or A B
| right {A} {B}: B -> Or A B.

Inductive eq {A: Set} (a: A): A -> Prop :=
| eq_refl: eq a a.

Definition Relation (A: Set) : Type := A -> A -> Prop.

Inductive ReflexiveRel : Set :=
   | build_ReflexiveRel: (A: Set) -> (rel: Relation A) -> (refl: (x: A) -> rel x x) -> ReflexiveRel.

Definition ReflexiveRel_t {rel: ReflexiveRel} : Set :=
   match rel with
      | build_ReflexiveRel A _ _ := A
   end.

Definition ReflexiveRel_rel {rel: ReflexiveRel} : ReflexiveRel_t {rel} -> ReflexiveRel_t {rel} -> Prop:=
   match rel with
      | build_ReflexiveRel _ rel _ := rel      
   end.

Definition ReflexiveRel_refl {rel: ReflexiveRel} : (x: ReflexiveRel_t {rel}) -> ReflexiveRel_rel x x :=
   match rel with
      | build_ReflexiveRel _ _ refl := refl      
   end.

				 

