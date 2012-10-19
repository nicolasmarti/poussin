<<| Inductive Peano : Set := | O : Peano | S: Peano -> Peano |>>;;
<<| Signature plus_Peano: Peano -> Peano -> Peano |>>;;
<<| Decreasing plus_Peano [0] |>>;;
<<| 
  Definition plus_Peano (x y: Peano) :=
    match x with
      | O := y
      | S x := S (plus_Peano x y)
    end
  |>>;;

