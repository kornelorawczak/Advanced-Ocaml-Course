(* count1 - (); count2 - {}; count3 - [] *)
let parens_ok2 (str : string) : bool = 
  let rec checker (chars : char list) (count1 : int) (count2 : int) (count3 : int) = 
    match chars with 
    | [] -> count1 = 0 && count2 = 0 && count3 = 0 
    | '(' :: rest -> checker rest (count1 + 1) count2 count3
    | ')' :: rest -> count1 > 0 && checker rest (count1 - 1) count2 count3
    | '{' :: rest -> checker rest count1 (count2+ 1) count3
    | '}' :: rest -> count2 > 0 && checker rest count1 (count2 - 1) count3
    | '[' :: rest -> checker rest count1 count2 (count3 + 1)
    | ']' :: rest -> count3 > 0 && checker rest count1 count2 (count3 - 1)
    | _ :: rest -> false 
  in checker (List.of_seq (String.to_seq str)) 0 0 0