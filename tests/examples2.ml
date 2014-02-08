let zero = <:term< O >>;;

let caca = match to_ground_term <:term< O >> with 
  | { ast = Cste "O"; _} -> true 
  | { ast = Lambda ((x, _,Explicit), { ast = TName x0; _}); _} when String.compare x x0 = 0 -> false ;;


let prout = match to_ground_term <:term< \\ {A: Set} (y: A) -> y >> with 
  | <:pat< O >> -> true 
  | <:pat< \\ {x} -> y >> -> false
;;

let popo = match get_type (to_ground_term <:term< \\ {A: Set} (y: A) -> y >>) with 
  | <:pat< O >> -> true 
  | <:pat<  {x} -> y >> -> false
;;

