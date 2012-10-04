Inductive List: Type -> Set 
Constructor nil {A}: List A 
Constructor cons {A}: A -> List A -> List A

Definition hd {A} (l: List A) :=
  match l with
     | cons {_} x _  := x
  end
