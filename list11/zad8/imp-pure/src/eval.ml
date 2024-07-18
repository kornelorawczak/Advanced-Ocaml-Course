open Ast

module H = Map.Make(String)

exception Unbound_var of string 
exception MyExn 
exception Type_error 

type heap = int H.t

type ret = 
  | Heap of heap
  | Exn 

let transfer h = Heap h 

let lookup_var heap x =
  match H.find_opt x heap with
  | Some v -> v
  | None   -> raise (Unbound_var x)

let assign_var (heap : heap) x v =
  match H.find_opt x heap with
  | Some _ -> H.add x v heap
  | None   -> raise (Unbound_var x)

let declare_var heap x : heap =
  H.add x 0 heap

let eval_binop op =
  match op with
  | Mul -> ( * )
  | Div -> ( / )
  | Add -> ( + )
  | Sub -> ( - )

let rec eval_aexp heap e =
  match e with
  | Int n -> n
  | Var x -> lookup_var heap x
  | Binop(op, e1, e2) ->
    eval_binop op (eval_aexp heap e1) (eval_aexp heap e2)

let eval_cmpop op =
  match op with
  | Eq  -> ( = )
  | Neq -> ( <> )
  | Lt  -> ( < )
  | Gt  -> ( > )
  | Leq -> ( <= )
  | Geq -> ( >= )

let rec eval_bexp heap e =
  match e with
  | Bool b -> b
  | Cmp(op, e1, e2) ->
    eval_cmpop op (eval_aexp heap e1) (eval_aexp heap e2)
  | And(e1, e2) ->
    eval_bexp heap e1 && eval_bexp heap e2
  | Or(e1, e2) ->
    eval_bexp heap e1 || eval_bexp heap e2
  | Not e -> not (eval_bexp heap e)

let rec eval_stmt heap s : ret =
  match s with
  | Block ss -> List.fold_left (fun acc s ->
      match acc with
      | Heap h -> eval_stmt h s
      | Exn -> Exn
    ) (transfer heap) ss
  | Assgn(x, e) -> 
    let value = eval_aexp heap e in
    transfer (assign_var heap x value)
  | If(e, s1, s2) ->
    if eval_bexp heap e then eval_stmt heap s1
    else eval_stmt heap s2
  | While(e, s) -> eval_while heap e s
  | Read x ->
    let value = read_line () |> int_of_string in
    transfer (assign_var heap x value)
  | Write e ->
    let value = eval_aexp heap e in
    print_endline (string_of_int value);
    transfer heap
  | Raise -> Exn
  | Try(s1, s2) -> (
    match eval_stmt heap s1 with 
    | Exn -> eval_stmt heap s2 
    | Heap h -> Heap h 
  )

and eval_while heap e s =
  if eval_bexp heap e then
    match eval_stmt heap s with
    | Heap h -> eval_while h e s
    | Exn -> Exn
  else
    Heap heap

let run_prog (xs, stmt) =
  let heap = List.fold_left declare_var H.empty xs in
  match eval_stmt heap stmt with
  | Heap _ -> ()
  | Exn -> print_endline "Exception raised during program execution"
