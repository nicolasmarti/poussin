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
     | nil {A} := nil
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
     | O := nil
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

Inductive formula: Set
Constructor f_forall: {A: Set} -> (A -> formula) -> formula
Constructor f_exists: {A: Set} -> (A -> formula) -> formula
Constructor f_neg: formula -> formula
Constructor f_and: formula -> formula -> formula
Constructor f_or: formula -> formula -> formula
Constructor f_impl: formula -> formula -> formula
Constructor f_iff: formula -> formula -> formula
Constructor f_pred: bool -> formula

Inductive exists {A: Set} (P: A -> Prop): Prop
Constructor witness {A: Set} (a: A) P: P a -> exists P

Inductive Iff: Prop -> Prop -> Prop
Constructor iff {P Q}: (P -> Q) -> (Q -> P) -> Iff P Q

Signature formula_sem: formula -> Prop
Definition formula_sem (f: formula) :=
   match f with
      | f_forall {A} f := (x: A) -> formula_sem (f x)
      | f_exists {A} f := exists (\ x -> formula_sem (f x))
      | f_neg f := Not (formula_sem f)
      | f_and f1 f2 := And (formula_sem f1) (formula_sem f2)
      | f_or f1 f2 := Or (formula_sem f1) (formula_sem f2)
      | f_impl f1 f2 := (formula_sem f1) -> (formula_sem f2)
      | f_iff f1 f2 := Iff (formula_sem f1) (formula_sem f2)
      | f_pred b := eq b true
   end

Signature andb (b1 b2: bool): bool
Definition andb (b1 b2: bool) :=
   match b1 with
      | false := false
      | true := b2
   end

Signature orb (b1 b2: bool): bool
Definition orb (b1 b2: bool) :=
   match b1 with
      | true := true
      | false := b2
   end

Signature notb (b: bool): bool
Definition notb (b: bool) :=
   match b with
      | true := false
      | false := true
   end

Signature implb (b1 b2: bool): bool
Definition implb (b1 b2: bool) :=
   match b1 with
      | false := true
      | true := b2
   end

Signature eq_implb_orb_notb (b1 b2: bool): eq (implb b1 b2) (orb (notb b1) b2)
Definition eq_implb_orb_notb (b1 b2: bool) :=
  match b1 with
     | true := eq_refl b2
     | false := eq_refl true
  end

Signature eq_implb_orb_notb2 (b1 b2: bool): eq (implb b1 b2) (orb (notb b1) b2)
Definition eq_implb_orb_notb2 (b1 b2: bool) :=
  match prod b1 b2 with
     | prod true true := eq_refl true 
     | prod true false := eq_refl false
     | prod false _ := eq_refl true
  end

Definition eq_trans2 {A} (x y z: A) (Hxy: eq x y) (Hyz: eq y z) : eq x z :=
  match Hyz with
     | eq_refl {_} _ := Hxy
  end

Signature congr: {A: Type} -> (x y: A) -> (P: A -> Type) -> (Hxy: eq x y) -> (H: P x) -> P y
Definition congr {A: Type} (x y: A) (P: A -> Type) (Hxy: eq x y) (H: P x) :=
  match Hxy with
     | eq_refl {_} _ := H
  end

Signature leibniz: {A: Type} -> (x y: A) -> ((P: A -> Prop) -> P x -> P y) -> eq x y
Definition leibniz {A: Type} (x y: A) (H: (P: A -> Prop) -> P x -> P y) :=
  H (eq {A} x) (eq_refl _)

Signature nat_ind (P: Nat -> Prop) (H0: P O) (H1: (n: Nat) -> P n -> P (S n)): (n: Nat) -> P n
Definition nat_ind (P: Nat -> Prop) (H0: P O) (H1: (n: Nat) -> P n -> P (S n)) (n: Nat) :=
  match n with
     | O := H0
     | S n := H1 n (nat_ind P H0 H1 n)
  end

Definition eqS (x y: Nat) (Hxy: eq x y) : eq (S x) (S y) :=
  match Hxy with
    | eq_refl {_} _ := eq_refl (S x)
  end

Signature plusxO: (n: Nat) -> eq (plus n O) n
Definition plusx0 (n: Nat) :=
  nat_ind (\ x -> eq (plus x O) x)
          (eq_refl O)
          (\ n (Pn: eq (plus n O) n) -> eqS _ _ Pn) n

Definition plusxS (x y: Nat) : eq (plus x (S y)) (S (plus x y)) :=
  nat_ind (\ x -> eq (plus x (S y)) (S (plus x y)))
          (eq_refl (S y))
          (\n (Pn: eq (plus n (S y)) (S (plus n y))) -> eqS _ _ Pn) x

Definition plus_comm (x y: Nat) : eq (plus x y) (plus y x) :=
  nat_ind (\ x -> eq (plus x y) (plus y x))
          (eq_symm _ _ (plusxO y))
          (\ n (Pn: eq (plus n y) (plus y n)) -> 
	    match (plusxS y n) with
              | eq_refl {_} v :=  match Pn with
	      		            | eq_refl {_} m := eq_refl (S (plus y n))
				      	      	  
                   end
	     end
	  ) x

Definition plus_assoc (x y z: Nat) : eq (plus x (plus y z)) (plus (plus x y) z) := ?







