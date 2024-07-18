(* Kornel Orawczak 346010 Projekt 1 MP 2024 *)
type nonogram_spec = {rows: int list list ; cols: int list list}

let ( let* ) xs ys = List.concat_map ys xs

let list_sum (xs : int list) : int = 
  let rec iter xs acc = 
    match xs with 
    | [] -> acc
    | x :: xs' -> iter xs' acc + x
  in iter xs 0 

(* simple function that returns a sequence of n times either true or false *)
let bools (b : bool) (n : int) : bool list = 
  let rec iter b n acc = 
    match n with 
    | 0 -> acc
    | m -> iter b (m-1) (b :: acc)
  in iter b n [] 

(* this is a build_row function in case there is only one trues segment in a row *)
let simple_build_row (r : int) (len : int) : bool list list = 
  let true_segment = bools true r in 
  let rec iter r len acc ret = 
    if acc > (len - r) then ret else 
    iter r len (acc + 1) ((bools false acc @ true_segment @ bools false (len - acc - r)) :: ret)
    in iter r len 0 []

(* max_index = amount of falses in the beginning, equals len - all the trues and necessary spaces between them*)
(* index = number of falses in the beginning on this stage of creating bool list *)
(* next_len = len after pasting index*false + x*true + false (len of the next element in a row) *)
(* next_elements recurrently eventually catches case [x] and returns simple elements, then this function inserts necessary segments that were calculated before to create all good rows *)
let rec build_row (ps : int list) (n : int) : bool list list=
  match ps with 
  | [] -> [bools false n]
  | [p] -> simple_build_row p n 
  | p :: ps' -> 
    let row_insert = (bools true p) @ [false] in 
    let max_index = n - (list_sum ps') - (List.length ps') + 1 in 
    let rec insert_row index ret = 
      if index > max_index then ret else
        let false_segment = bools false index in 
        let next_len = n - index - p - 1 in 
        let next_elements = build_row ps' next_len in 
        let element = List.map (fun row -> false_segment @ row_insert @ row) next_elements in 
        insert_row (index + 1) (ret @ element)
      in insert_row 0 []
  
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

let rec transpose (xss : 'a list list) : 'a list list = 
  match xss with 
  | [] :: _ -> []
  | _ -> List.map List.hd xss :: transpose (List.map List.tl xss)
  
(* for every possible row built it builts all the others and groups them *)     
let build_candidate (pss : int list list) (n : int) (xss : int list list): bool list list list = 
  let col_len = List.length pss in 
  let rec help (pss : int list list) (xss : int list list) (current_rows : bool list list list) = 
  match pss with 
  | [] -> current_rows
  | ps :: pss' -> 
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
              


let verify_row (ps : int list) (xs : bool list) : bool = 
  let rec iter ps xs count curr =
    match xs with
    | [] -> 
      if count != 0 then if count = curr && ps = [] then true else false
      else if ps = [] then true else false 
    | true :: xs' -> iter ps xs' (count + 1) curr 
    | false :: xs' -> 
      if count = 0 then iter ps xs' 0 curr else 
      if count != curr then false else 
      if ps = [] then iter [] xs' 0 0 else 
      iter (List.tl ps) xs' 0 (List.hd ps)
  in iter (List.tl ps) xs 0 (List.hd ps)


(* at this point its safe to say that the data inputted into functions are correct, in this function meaning that len(rss) == len(bss) *)
let rec verify_rows (pss : int list list) (xss : bool list list) : bool = 
  match pss, xss with
  | [], _ -> true
  | _, [] -> true
  | ps :: pss', xs :: xss' ->  
    verify_row ps xs && verify_rows pss' xss' 


(* Transpose function needs data to make sense, meaning that every list inside rss has to have the same amount of elements *)
let rec transpose (xss : 'a list list) : 'a list list = 
  match xss with 
  | [] :: _ -> []
  | _ -> List.map List.hd xss :: transpose (List.map List.tl xss)



let solve_nonogram (nono : nonogram_spec) = 
  build_candidate (nono.rows) (List.length (nono.cols)) nono.cols

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


