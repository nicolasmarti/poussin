let quotexpander_def s =
  "parse_process_definition \""^(String.escaped s)^"\""

let quotexpander_term s =
  "parse_type_term \""^(String.escaped s)^"\"";;

Quotation.add "term" (Quotation.ExStr (fun x -> 
  if x then
    quotexpander_term
  else 
    term2pattern
))
;;

Quotation.add "def" (Quotation.ExStr (fun x -> 
  if x then
    quotexpander_def
  else 
    raise (failwith "no pattern mode for defs")
))
;;


