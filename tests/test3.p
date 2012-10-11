Inductive List: Type -> Set :=
| nil {A}: List A 
| cons {A}: A -> List A -> List A

Definition hd {A} (l: List A) :=
  match l with
     | cons {_} x _  := x
  end
