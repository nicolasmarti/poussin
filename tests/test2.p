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
     | S (S n) := even n
     | O := true
     | S O := false
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
