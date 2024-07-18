(*Kornel Orawczak 346010*)
type nonogram_spec = {rows: int list list ; cols: int list list}

let ( let* ) xs ys = List.concat_map ys xs

let list_sum xs = 
  let rec iter xs acc = 
    match xs with 
    | [] -> acc
    | x :: xs' -> iter xs' acc + x
  in iter xs 0 

let bools b n = 
  let rec iter b n acc = 
    match n with 
    | 0 -> acc
    | m -> iter b (m-1) (b :: acc)
  in iter b n [] 

(*let seq x l = (* creates all possible sequences of x times true in l spaces with false in the begginning *)
  let rec help x l acc ret = 
    if ((List.length ret) + x > l) then ret else 
      help x l (acc @ [false]) ((acc @ ((bools true x) @ (bools false (l - x - (List.length acc))))) :: ret)
    in List.tl (List.rev (help x l [false] [[]])) *)

let seq2 x l = (* creates all possible sequences of x times true in l spaces with false in the begginning *)
let rec help x l acc ret = 
  if ((List.length acc) + x > l) then ret else 
    help x l (acc @ [false]) (ret @ [acc @ ((bools true x) @ (bools false (l - x - (List.length acc))))])
  in List.tl (help x l [false] [[]])

let seq3 x l = (* creates all possible sequences of x times true in l spaces *)
  let rec help x l acc ret = 
    if ((List.length acc) + x > l) then ret else 
      help x l (acc @ [false]) (ret @ [acc @ ((bools true x) @ (bools false (l - x - (List.length acc))))])
    in List.tl (help x l [] [[]])

let concatenate_each xs ys = (* creates all possible concatenations between two lists *)
  let rec help xs ys acc = 
    match xs with 
    | [] -> acc 
    | x :: xs' -> help xs' ys (acc @ (List.map (fun y -> x @ y) ys)) 
  in List.tl (help xs ys [[]])

let build_row (rs : int list) (len : int) = 
  let rec help rs len acc = 
    match rs with 
    | [] -> acc 
    | x :: xs -> 
      match acc with 
      | [] -> help xs ((list_sum xs) + 1) ((seq3 x (len - (list_sum xs) )))
      | _ -> help xs ((list_sum xs) + 1) (concatenate_each acc (seq2 x (len - (list_sum xs) )))
    in help rs len [[]]

let build_candidate (rss : int list list) (len : int) = 
  List.map (fun xs -> build_row xs len) rss 




let trues (xs : bool list) : int list = (* returns number of trues that are in sequences together *)
  let rec iter xs acc ret =
    match xs with 
    | [] -> if acc = 0 then ret else (acc :: ret)
    | true :: xs' -> iter xs' (acc + 1) ret
    | false :: xs' -> if acc = 0 then iter xs' 0 ret else iter xs' 0 (acc :: ret)
  in List.rev (iter xs 0 [])

let verify_row (rs : int list) (bs : bool list) : bool = 
  if rs = (trues bs) then true else false

let verify_row2 (rs : int list) (bs : bool list) : bool = 
  let rec iter rs bs curr acc = 
    match bs with 
    | [] -> 
      if curr = 0 then if acc = rs then true else false 
      else if acc @ [curr] = rs then true else false  
    | true :: bs' -> iter rs bs' (curr + 1) acc 
    | false :: bs' -> 
      if curr = 0 then iter rs bs' 0 acc 
      else iter rs bs' 0 (acc @ [curr])
    in iter rs bs 0 []

let transpose (rss : 'a list list) : 'a list list = 
  let max_len = List.length (List.hd rss) in 
  let rec help (rss : 'a list list) (acc : int) (ret : 'a list list) = 
    if acc = max_len then ret else 
      help (List.map List.tl rss) (acc + 1) (ret @ [List.concat_map (fun xs -> [List.hd xs]) rss])
    in help rss 0 []

let rec build_candidate (pss : int list list) (n : int) : bool list list list = 
  match pss with 
  | [] -> [[]]
  | ps :: pss' -> 
    let* built = build_row ps n in 
    let* rest = build_candidate pss' n in 
    [built :: rest] 


let premature_col_verification (pss : int list list) (xss : bool list list) (len : int) : bool = 
  let rec check_column ps xs true_count curr remaining_len = 
    match xs with 
    | [] -> if remaining_len + true_count >= curr + (list_sum ps) then true else false 
    | true :: xs' -> 
      if (true_count + 1) > curr then false 
      else check_column ps xs' (true_count + 1) curr (remaining_len - 1)
    | false :: xs' -> 
      if true_count = 0 then check_column ps xs' 0 curr (remaining_len - 1) 
      else if true_count != curr then false 
      else if ps = [] then List.for_all ((=) false) xs' 
      else check_column (List.tl ps) xs' 0 (List.hd ps) (remaining_len - 1)
  in let rec check_columns pss xss = 
    match pss, xss with 
    | [], _ | _, [] -> true 
    | ps :: pss', xs :: xss' -> 
      if check_column (List.tl ps) xs 0 (List.hd ps) len then check_columns pss' xss'
      else false 
    in check_columns pss xss
let rec is_positive (xs : int list) = 
  match xs with 
  | [] -> true 
  | x :: xs' -> 
    if x < 0 then false 
    else is_positive xs'

let solve_nonogram (nono : nonogram_spec) = 
  if List.length (nono.rows) = 0 
  || List.length (nono.cols) = 0 
  || not (List.for_all ((!=) []) nono.cols) 
  || not (List.for_all ((!=) []) nono.rows)
  || List.for_all (is_positive) nono.cols
  || List.for_all (is_positive) nono.rows
      then [] else
let backtrack (pss : int list list) (n : int) (xss : int list list): bool list list list = 
  let col_len = List.length pss in 
  let rec help (pss : int list list) (xss : int list list) (current_rows : bool list list list) = 
  match pss with 
  | []  -> current_rows
  | [0] :: pss' -> 
    let new_row = bools false n in 
    if current_rows = [] then help pss' xss [[new_row]] else 
    let new_rows = List.map (fun rows -> rows @ [new_row]) current_rows in 
    help pss' xss new_rows
  | ps  :: pss' -> 
    if current_rows = [] then help pss' xss (List.map (fun xs -> [xs]) (build_row ps n)) else 
    let new_rows = build_row ps n in 
    let filtered_rows = 
      List.concat_map 
        (fun verified_row -> 
          List.filter_map 
            (fun new_row -> 
              if premature_col_verification xss (transpose (verified_row @ [new_row])) (col_len) then 
                Some (verified_row @ [new_row]) else None)
        new_rows) 
      current_rows
    in help pss' xss filtered_rows 
  in help pss xss [] 
in backtrack nono.rows (List.length (nono.cols)) nono.cols
  


let example_1 = {
  rows = [[2];[1];[1]];
  cols = [[1;1];[2]]
}

let example_2 = {
  rows = [[2];[2;1];[1;1];[2]];
  cols = [[2];[2;1];[1;1];[2]]
}

let big_example = {
  rows = [[1;2];[2];[1];[1];[2];[2;4];[2;6];[8];[1;1];[2;2]];
  cols = [[2];[3];[1];[2;1];[5];[4];[1;4;1];[1;5];[2;2];[2;1]]
}

let example_3 = {
  rows = [[2;3];[1;1;1];[3];[2;2];[5]];
  cols = [[2;2];[1;3];[3;1];[1;3];[2;2]]
}

let example_4 = {
  rows = [[1]];
  cols = [[1]]
}

let example_5 = {
  rows = [[1];[1]];
  cols = [[1];[1]];
}

let example_6 = {
  rows = [[1];[1];[1]];
  cols = [[1];[1];[1]];
}

let example_7 = {
  rows = [[1];[];[1]];
  cols = [[1];[];[1]]
}

let example_8 = {
  rows = [[];[]];
  cols = [[];[]]
}

let example_9 = {
  rows = [[-1];[1]];
  cols = [[1];[0]]
}

let example_10 = {
  rows = [[0;1];[1]];
  cols = [[2];[0]]
}

let example_11 = {
  rows = [[0;1];[1]];
  cols = [[1];[1]]
}
let example_12 = {
  rows = [[];[]];
  cols = [[1]]
}


let solve_nonogram (nono : nonogram_spec) = 

  if List.length (nono.rows) = 0 
  || List.length (nono.cols) = 0 
  || not (List.for_all (is_positive) nono.cols)
  || not (List.for_all (is_positive) nono.rows)
  then [] else

let backtrack (pss : int list list) (n : int) (xss : int list list): bool list list list = 
  let col_len = List.length pss in 
  let rec help (pss : int list list) (xss : int list list) (current_rows : bool list list list) = 
  match pss with 
  | []  -> current_rows

  | [] :: pss' -> 
    let new_row = bools false n in 
    if current_rows = [] 
      then if premature_col_verification xss (transpose [new_row]) col_len 
        then help pss' xss [[new_row]] 
        else help pss' xss []
    else
    let filtered_rows = List.concat_map 
    (fun verified_row -> 
      List.filter_map 
        (fun new_row -> 
          if premature_col_verification xss (transpose (verified_row @ [new_row])) (col_len) then 
            Some (verified_row @ [new_row]) else None)
      [new_row]) 
    current_rows 
  in help pss' xss filtered_rows

  | ps  :: pss' -> 
    if current_rows = [] 
      then if premature_col_verification xss (transpose (build_row ps n)) col_len 
        then help pss' xss (List.map (fun xs -> [xs]) (build_row ps n)) 
        else help pss' xss []
    else 
    let new_rows = build_row ps n in 
    let filtered_rows = 
      List.concat_map 
        (fun verified_row -> 
          List.filter_map 
            (fun new_row -> 
              if premature_col_verification xss (transpose (verified_row @ [new_row])) (col_len) then 
                Some (verified_row @ [new_row]) else None)
        new_rows) 
      current_rows
    in help pss' xss filtered_rows 

  in help pss xss [] 
in backtrack nono.rows (List.length (nono.cols)) nono.cols