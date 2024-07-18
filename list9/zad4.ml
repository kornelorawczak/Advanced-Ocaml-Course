type expr =
  | Int of int
  | Add of expr * expr
  | Mult of expr * expr

let rec eval ( e : expr ) : int =
  match e with
  | Int n -> n
  | Add ( e1 , e2 ) -> eval e1 + eval e2
  | Mult ( e1 , e2 ) -> eval e1 * eval e2

type rpn_cmd =
  | Push of int
  | RAdd
  | RMult

type rpn = rpn_cmd list

let rec to_rpn ( e : expr ) : rpn =
  match e with
  | Int n -> [ Push n ]
  | Add ( e1 , e2 ) -> to_rpn e1 @ to_rpn e2 @ [ RAdd ]
  | Mult ( e1 , e2 ) -> to_rpn e1 @ to_rpn e2 @ [ RMult ]

let rec eval_rpn ( r : rpn ) ( s : int list ) : int =
  match r , s with
  | [] , [ n ] -> n
  | Push n :: r', _ -> eval_rpn r' ( n :: s )
  | RAdd :: r', n1 :: n2 :: s' -> eval_rpn r' ( n2 + n1 :: s')
  | RMult :: r', n1 :: n2 :: s' -> eval_rpn r' ( n2 * n1 :: s')
  | _ , _ -> failwith " error ! "


let expr_ex1 = Mult(Int 2, Add(Int 4, Mult(Int 2, Int 3)))
let expr_ex2 = Mult(Add(Int 2, Int 3), Mult(Int 1, Int 3))


let from_rpn (r : rpn) : expr = 
  let rec help (r : rpn) (intstack : expr list) : expr = 
    match r with  
    | Push n :: r' -> help r' (intstack @ [Int n]) 
    | RMult :: r' -> (
      match intstack with 
      | [Int n1; Int n2] -> Mult(Int n1, Int n2)
      | Int n :: is' -> Mult(Int n, help r' is')
      | _ -> failwith "error 1"
    )
    | RAdd :: r' -> (
      match intstack with 
      | [Int n1; Int n2] -> Add(Int n1, Int n2)
      | Int n :: is' -> Add(Int n, help r' is')
      | _ -> failwith "error 2"
    )
    | _ -> failwith "error 3"
  in help r [] 



let rec random_expr (max_depth : int) : expr = 
  if max_depth = 0 then
    if Random.int(2) = 0 then (* losujemy znak liczby *)
      Int (Random.int(10000)) else Int ((-1) * Random.int(10000))
  else if Random.int(2) = 0 then 
    Mult(random_expr (max_depth - 1), random_expr (max_depth - 1)) else 
    Add(random_expr (max_depth - 1), random_expr (max_depth - 1))

let rec test_ce (max_depth : int) (n : int) : expr option = 
  if n = 0 then None else 
    let rand_expr = random_expr max_depth in 
    if (from_rpn (to_rpn rand_expr) = rand_expr) = false then Some rand_expr else test_ce max_depth (n - 1)
