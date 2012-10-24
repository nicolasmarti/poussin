let quotexpander s =
  if String.sub s 0 1 = "|" & String.sub s (String.length s - 1) 1 = "|" then
    "parse_process_definition \""^
    (String.escaped (String.sub s 1 (String.length s - 2)))^"\""
  else
    "parse_type_term \""^(String.escaped s)^"\"";;

Quotation.add "" (Quotation.ExStr (fun x -> 
  if x then
    quotexpander
  else 
    term2pattern
))
;;

