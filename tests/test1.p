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

Definition eq_symm {A} (x y: A) (Hxy: eq x y) : eq y x :=
   match Hxy with
      | eq_refl {A} x := eq_refl {A} x
   end

Definition eq_trans {A} (x y z: A) (Hxy: eq x y) (Hyz: eq y z) : eq x z :=
   match Hxy with
      | eq_refl {A} xy :=
          match Hyz with
           | eq_refl {A} yz := eq_refl {A} z
          end      
   end


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

Inductive bool: Set
Constructor true: bool
Constructor false: bool

Inductive Eq: Set -> Set
Constructor build_eq {A}: (eqb: A -> A -> bool) -> Eq A

Definition eqb {A: Set} {eqA: Eq A}: A -> A -> bool :=
  match eqA with
     | build_eq {A} eqb := eqb
  end


Inductive pair: Set -> Set -> Set
Constructor prod {A B: Set} (a: A) (b: B): pair A B

Definition eqb_bool (b1 b2: bool) : bool :=
  match prod b1 b2 with
     | prod {_} {_} true true := true
     | prod {_} {_} false false := true
     | prod {_} {_} true false := false
     | prod {_} {_} false true := false
  end

Compute eqb_bool true true
Compute eqb_bool true false
Compute eqb_bool false true
Compute eqb_bool false false

Signature iota : Nat -> (size: Nat) -> Vector Nat size
Definition iota (start size: Nat) :=
  match size with
     | O := nil {Nat}
     | S size := cons start (iota (S start) size)
  end

Signature mult : Nat -> Nat -> Nat
Definition mult (n m: Nat) :=
  match n with
     | O := O
     | S n := plus m (mult n m)
  end

Signature exp : Nat -> Nat -> Nat
Definition exp (n m: Nat) :=
  match n with
     | O := S O
     | S n := mult m (exp n m)
  end

Definition three : Nat := S (S (S O))
Definition two : Nat := S (S O)

Signature min: Nat -> Nat -> Nat
Definition min (x y: Nat) :=
  match x with
     | O := O
     | S n := match y with
          	| O := x
        	| S m := min n m 
              end
  end

Compute mult three three
Compute min (S (exp two three)) (exp two three)

Compute let x := exp two three in min (S x) x

Definition and_comm {P Q} (H: And P Q) :=
  match H with
     | conj {P} {Q} p q := conj q p
end

Inductive expr: Set -> Set
Constructor Cste {A: Set}: A -> expr A
Constructor App {A B: Set}: expr (A -> B) -> expr A -> expr B
Constructor Ifte {A: Set}: expr bool -> expr A -> expr A -> expr A

Signature expr_sem {A: Set}: expr A -> A
Definition expr_sem {A: Set} (e: expr A) :=
  match e with
     | Cste {A} c := c
     | App {A} {B} f a := (expr_sem f) (expr_sem a)
     | Ifte {A} b e1 e2 := 
        match expr_sem b with
          | true := expr_sem e1
          | false := expr_sem e2
        end
  end


