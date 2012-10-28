let zero = <:term< O >>;;

let caca = match <:term< O >> with 
  | { ast = Cste "O"; _} -> true 
  | { ast = Lambda ((x, _,Explicit), { ast = TName x0; _}); _} when String.compare x x0 = 0 -> false ;;


let prout = match <:term< \\ {A: Set} (y: A) -> y >> with | <:term< O >> -> true | <:term< \\ {x} -> y >> -> false ;;

