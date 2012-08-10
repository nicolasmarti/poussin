Inductive True : Prop
Constructor I: True

Inductive False : Prop

Inductive Not (P: Prop) : Prop
Constructor Contradiction  {P}: (P -> False) -> Not P

Inductive And (A B: Prop) : Prop
Constructor conj {A} {B}: A -> B -> And A B

Inductive Or (A B: Prop) : Prop
Constructor left {A} {B}: A -> Or A B
Constructor right {A} {B}: B -> Or A B

Inductive eq {A: Set} (a: A): A -> Prop
Constructor eq_refl {A} (a: A): eq a a

Definition Relation (A: Set) : Type := A -> A -> Prop

Inductive ReflexiveRel : Set
Constructor build_ReflexiveRel: (A: Set) -> (rel: Relation A) -> (refl: (x: A) -> rel x x) -> ReflexiveRel

Definition ReflexiveRel_t {rel: ReflexiveRel} : Set :=
   match rel with | build_ReflexiveRel A _ _ := A end

Definition ReflexiveRel_rel {rel: ReflexiveRel} : ReflexiveRel_t {rel} -> ReflexiveRel_t {rel} -> Prop:=
   match rel with
      | build_ReflexiveRel _ rel _ := rel      
   end

Definition ReflexiveRel_refl {rel: ReflexiveRel} : (x: ReflexiveRel_t {rel}) -> ReflexiveRel_rel {rel} x x :=
   match rel with
      | build_ReflexiveRel _ _ refl := refl      
   end

Inductive Nat: Set
Constructor O: Nat
Constructor S: Nat -> Nat

Inductive Vector (A: Set): Nat -> Set
Constructor nil {A: Set}: Vector A O
Constructor cons {A: Set} {n}: A -> Vector A n -> Vector A (S n)

Signature map {A B: Set} {n}: (f: A -> B) -> Vector A n -> Vector B n

Definition map {A B: Set} {n} (f: A -> B) (v: Vector A n) : Vector B n :=
  match v with
     | nil {A} := nil {B}
     | cons {A} {n} hd tl := cons (f hd) (map f tl)
end

Signature plus: Nat -> Nat -> Nat

Definition plus (n m: Nat) : Nat :=
  match n with
     | O := m
     | S n := S (plus n m) 
  end

Signature append {A} {n1 n2} (v1: Vector A n1) (v2: Vector A n2): Vector A (plus n1 n2)

Definition append {A} {n1 n2} (v1: Vector A n1) (v2: Vector A n2): Vector A (plus n1 n2) :=
  match v1 with
     | nil {A} := v2
     | cons {A} {n1} hd tl := cons hd (append tl v2)
  end