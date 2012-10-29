<:def< 

Inductive eq {A: Set} (x: A): A -> Prop :=
  | eq_refl {A: Set} (x: A): eq x x

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

Definition eq_trans2 {A} (x y z: A) (Hxy: eq x y) (Hyz: eq y z) : eq x z :=
  match Hyz with
     | eq_refl {_} _ := Hxy
  end

Definition congr {A: Type} (x y: A) (P: A -> Type) (Hxy: eq x y) (H: P x) : P y :=
  match Hxy with
     | eq_refl {_} _ := H
  end

Definition leibniz {A: Type} (x y: A) (H: (P: A -> Prop) -> P x -> P y) : eq x y :=
     H (eq {A} x) (eq_refl _)

>>;; 
