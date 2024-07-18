(*zadanie 1*)
let rec fib n =
  if n = 0 then 0 else
  if n = 1 then 1 else
  fib (n-1) + fib (n-2);;

let fib_iter n = 
  let rec it n a b =
    if n = 0 then a else
      it (n-1) (b) (a+b) in 
      it n 0 1;;

(*zadanie 2*)
let matrix_mult m n = 
  let f (a,b,c,d) (a',b',c',d') =
    (a*a'+b*c', a*b'+b*d', c*a'+d*c', c*b'+d*d')
  in f m n;;

let matrix_id = (1,0,1,0);;

let matrix_ecpt m k = 
  let rec it m k res = 
    if k = 1 then res else
      it m (k-1) (matrix_mult m res)
    in it m k m;;

let matrix_fib n = 
  if n = 0 then 0 else 
    if n = 1 then 1 else
      let thrd (a,b,c,d) = c 
    in thrd (matrix_ecpt (1,1,1,0) n);;

(*zadanie 3
   Najszybszy był fib_iter, potem matrix_fib_fast a na końcu matrix_fib*)

let rec matrix_expt_fast m k = 
  if k = 1 then m else 
    if k mod 2 = 0 then 
      matrix_expt_fast (matrix_mult m m) (k / 2) else 
        matrix_mult m (matrix_expt_fast m (k - 1));;
      
let matrix_fib_fast n = 
  if n = 0 then 0 else 
    if n = 1 then 1 else
      let thrd (a,b,c,d) = c 
    in thrd (matrix_ecpt (1,1,1,0) n);;

    
(*zadanie 4*)
let rec mem i list = 
  if list = [] then false else
  if (List.hd list) = i then true else
    mem i (List.tl list);;

(*zadanie 5*)
let maximum xs = 
  if xs = [] then neg_infinity else
    let rec max_it xs max = 
      if xs = [] then max else
        if List.hd xs > max then 
          max_it (List.tl xs) (List.hd xs) else
            max_it (List.tl xs) max in max_it xs neg_infinity;;


(*zadanie 6*)
let rec suffixes xs = 
  match xs with 
  | [] -> [[]]
  | _ :: tail -> xs :: suffixes tail;;

(*zadanie 7*)
let is_sorted xs = 
  if xs = [] then true else
  let rec help xs prev = 
    match xs with
    | [] -> true 
    | x::xs' -> 
      if x < prev then 
        false else  
          help xs' x in 
          help (List.tl xs) (List.hd xs);;

(*zadanie 8*)
let rec select xs = 
  match xs with 
  | [] -> failwith "List can't be empty"
  | [x] -> (x, [])
  | x::xs' -> 
    let (min, rest) = select xs' in 
    if x < min then (x, xs') else 
      (min, x::rest);;

let rec selection_sort xs = 
  match xs with 
  | [] -> []
  | _ -> let (min, rest) = select xs in
    min::(selection_sort rest);;


(*zadanie 9*)
let split xs = 
  let rec help xs s1 s2 next = 
    match xs with 
    | [] -> (s1, s2)
    | x::xs' -> if next = 1 then 
      help xs' (x::s1) s2 2 else
        help xs' s1 (x::s2) 1 in 
        help xs [] [] 1;;

let rec merge xs ys = 
  if xs = [] then ys else
    if ys = [] then xs else 
      if (List.hd xs) < (List.hd ys) then 
        (List.hd xs)::(merge (List.tl xs) ys) else
          (List.hd ys )::(merge xs (List.tl ys));;
          
let merge_sort xs = 
  let rec help xs ys = 
    if (List.tl xs) = [] || (List.tl ys) = [] then 
      merge xs ys else
        merge (help (fst (split xs)) (snd (split xs))) (help (fst (split ys)) (snd (split ys))) in 
        help (fst (split xs)) (snd (split xs));;
