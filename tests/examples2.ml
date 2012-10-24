let zero = << O >>;;

let caca = match << O >> with 
  | { ast = Cste "O"; _} -> true 
  | { ast = Lambda ((x, _,Explicit), { ast = TName x0; _}); _} when String.compare x x0 = 0 -> false ;;


let prout = match << O >> with | << O >> -> true | << \\ x -> x >> -> false ;;

