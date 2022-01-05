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

Definition eq_symm {A} (x y: A) (Hxy: eq x y) : eq y x :=
   match Hxy with
      | eq_refl {A} x := eq_refl x
   end

Definition eq_trans {A} (x y z: A) (Hxy: eq x y) (Hyz: eq y z) : eq x z :=
   match Hxy with
      | eq_refl {A} xy :=
          match Hyz with
           | eq_refl {A} yz := eq_refl _
          end      
   end


Definition Relation (A: Set) : Type := A -> A -> Prop

Inductive ReflexiveRel : Set :=
| build_ReflexiveRel: (A: Set) -> (rel: Relation A) -> (refl: (x: A) -> rel x x) -> ReflexiveRel

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

Inductive Nat: Set :=
| O: Nat
| S: Nat -> Nat

Inductive Vector (A: Set): Nat -> Set :=
| vnil {A: Set}: Vector A O
| vcons {A: Set} {n}: A -> Vector A n -> Vector A (S n)

Recursive vmap {A B: Set} {n} (f: A -> B) (v: Vector A n) [4] : Vector B n :=
  match v with
     | vnil {A} := vnil
     | vcons {A} {n} hd tl := vcons (f hd) (vmap f tl)
end

Recursive plus (n m: Nat) [0]: Nat :=
  match n with
     | O := m
     | S n := S (plus n m) 
  end

Recursive vappend {A} {n} (v1: Vector A n) {m} (v2: Vector A m) [2]: Vector A (plus n m) :=
  match v1 with
     | vnil {A} := v2
     | vcons {A} {n1} hd tl := vcons hd (vappend tl v2)
  end

Inductive list: Type -> Type :=
| lnil: {A: Type} -> list A
| lcons: {A: Type} -> A -> list A -> list A

Inductive tuple: list Type -> Type :=
| tnil: tuple lnil
| tcons: {hd: Type} -> hd -> {tl: list Type} -> tuple tl -> tuple (lcons hd tl)

Check tcons O (tcons (S O) tnil)

Recursive mult (n m: Nat) [0] : Nat :=
  match n with
     | O := O
     | S n := plus m (mult n m)
  end

Recursive exp (n m: Nat) [1] : Nat :=
  match m with
     | O := S O
     | S m := mult n (exp n m)
  end

Definition two : Nat := S (S O)
Definition three : Nat := S two
Definition four := plus two two
Definition five := plus two three

Check exp two three
Compute exp two three

