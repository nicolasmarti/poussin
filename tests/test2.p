Inductive eq {A: Set} : A -> A -> Prop
Constructor eq_refl {A: Set} (a: A): eq a a

Inductive Peano : Set
Constructor O: Peano
Constructor S: Peano -> Peano

Signature Peano_inversion (n: Peano) (P: Prop) (H1: eq n O -> P) (H2: (x: Peano) -> eq n (S x) -> P): P
Definition Peano_inversion (n: Peano) (P: Prop) (H1: eq n O -> P) (H2: (x: Peano) -> eq n (S x) -> P) : P :=
   match n with
      | O := H1 (eq_refl O)
      | S x := H2 x (eq_refl (S x))      
   end

Inductive True: Prop
Constructor I: True

Inductive False: Prop

Inductive Bool: Set
Constructor true : Bool
Constructor false : Bool

Definition caca: Peano := S (S O)

Signature even: Peano -> Bool
Definition even (n: Peano) :=
  match n with
     | O := true
     | S O := false
     | S (S O) := even n
end

Inductive Vector (A: Set): Peano -> Set
Constructor nil {A: Set}: Vector A O
Constructor cons {A: Set} {n}: A -> Vector A n -> Vector A (S n)

Definition head {A: Set} {n} (v: Vector A (S n)) : A :=
  match v with
     | cons {_} {_} hd _ := hd
  end

Inductive evenPeano : Set
Constructor evP: (x: Peano) -> [H: eq (even x) true] -> evenPeano

Definition evenPeano_num (x: evenPeano) : Peano :=
  match x with
     | evP x [_] := x
  end

Definition evenPeano_iseven (x: evenPeano) : eq (even (evenPeano_num x)) true :=
  match x with
     | evP _ [P] := P
  end

Signature debile: Peano -> Peano
Definition debile (a: Peano) :=
let f := debile in
let g := f a in
  match f a with
     | O := O
     | S x := x
end

Inductive Fin: Peano -> Set
Constructor f0 {n}: Fin (S n)
Constructor fS {n}: Fin n -> Fin (S n)

Signature index {A} {n} (i: Fin n) (v: Vector A n) : A
Definition index {A} {n} (i: Fin n) (v: Vector A n) :=
  match i with
     | f0 {_} := match v with | cons {_} {_} hd _ := hd end
     | fS {_} i := match v with | cons {_} {_} _ tl := index i tl end
  end