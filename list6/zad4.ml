let parens_ok (str : string) : bool = 
  let rec checker (chars : char list) (open_count : int) = 
    match chars with 
    | [] -> open_count = 0
    | '(' :: rest -> checker rest (open_count + 1)
    | ')' :: rest -> open_count > 0 && checker rest (open_count - 1)
    | _ :: rest -> false 
  in checker (List.of_seq (String.to_seq str)) 0