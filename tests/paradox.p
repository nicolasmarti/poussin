Inductive False : Prop :=

Inductive I : Set :=
| C: (I -> False) -> I

Definition ICase (Q: Prop) (i: I) (g: (I -> False) -> Q) : Q :=
  match i with
     | C x := g x
  end

Definition doudou : I -> I -> False :=
   \ (f x: I) -> ICase False f (\ (h: I -> False) -> h x)

Definition doudou2 : I :=
	   C (\ (x: I) -> doudou x x)

Definition doudou3 : False := doudou doudou2 doudou2

Compute doudou3
