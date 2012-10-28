<:def< Inductive Peano : Set := | O : Peano | S: Peano -> Peano >>;;
<:def< Signature plus_Peano: Peano -> Peano -> Peano >>;;
<:def< Decreasing plus_Peano [0] >>;;
<:def< 
  Definition plus_Peano (x y: Peano) :=
    match x with
      | O := y
      | S x := S (plus_Peano x y)
    end
  >>;;

