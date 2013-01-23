<:def< Inductive Peano : Set := | O : Peano | S: Peano -> Peano >>;;
<:def< 
  Recursive plus_Peano (x y: Peano) [0] : Peano :=
    match x with
      | O := y
      | S x := S (plus_Peano x y)
    end
  >>;;

