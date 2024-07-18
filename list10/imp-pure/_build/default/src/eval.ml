open Ast

module H = Map.Make(String)

type heap = int list

let rec change_value heap id v=
  match heap, id with
  | _::tl, 0 -> v::tl
  | h::tl, n -> h::(change_value tl (n-1) v)
  | [], _ -> failwith "Unbound variable"
let lookup_var heap env x =
  match H.find_opt x env with
  | Some v -> List.nth  heap v
  | None   -> failwith ("Unbound variable " ^ x)

let assign_var heap env x v =
  match H.find_opt x env with
  | Some n -> change_value heap n v
  | None   -> failwith ("Unbound variable " ^ x)

let rec declare_vars length env xs=
  match xs with 
  | [] -> env
  | x::tl -> declare_vars (length-1) (H.add x length env) tl

(*let declare_var heap x : heap =
  H.add x 0 heap*)

let eval_binop op =
  match op with
  | Mul -> ( * )
  | Div -> ( / )
  | Add -> ( + )
  | Sub -> ( - )

let rec eval_aexp heap env e =
  match e with
  | Int n -> n
  | Var x -> lookup_var heap env x
  | Binop(op, e1, e2) ->
    eval_binop op (eval_aexp heap env e1) (eval_aexp heap env e2)

let eval_cmpop op =
  match op with
  | Eq  -> ( = )
  | Neq -> ( <> )
  | Lt  -> ( < )
  | Gt  -> ( > )
  | Leq -> ( <= )
  | Geq -> ( >= )

let rec eval_bexp heap env e =
  match e with
  | Bool b -> b
  | Cmp(op, e1, e2) ->
    eval_cmpop op (eval_aexp heap env e1) (eval_aexp heap env e2)
  | And(e1, e2) ->
    eval_bexp heap env e1 && eval_bexp heap env e2
  | Or(e1, e2) ->
    eval_bexp heap env e1 || eval_bexp heap env e2
  | Not e -> not (eval_bexp heap env e)

let rec eval_stmt env heap s =
  match s with
  | Block (vs,ss)-> (* ilość wartości w heap odpowiada ilości zmiennych w programie (lokalne + globalne) *)
    let heap' = List.fold_left (fun heap _-> heap@[0]) heap vs in (* Dodaje tyle 0 ile jest nowo zadeklarowanych zmiennych *)
    let env' =  declare_vars ((List.length heap')-1) env vs in (* Przepisuje środowisko, biorąc pod uwagę nowe zmienne i ich indeksy *)
    List.fold_left (eval_stmt env') heap' ss
  | Assgn(x, e) -> assign_var heap env x (eval_aexp heap env e)
  | If(e, s1, s2) ->
    if eval_bexp heap env e then eval_stmt env heap s1
    else eval_stmt env heap s2
  | While(e, s) ->
    eval_while heap env e s
  | Read x ->
    read_line () |> int_of_string |> assign_var heap env x
  | Write e ->
    eval_aexp heap env e |> string_of_int |> print_endline;
    heap

and eval_while heap env e s =
  if eval_bexp heap env e then
    eval_while (eval_stmt env heap s) env e s
  else
    heap

let run_prog (xs, stmt) =
  let heap = List.fold_left (fun heap _-> heap@[0]) [] xs in
  let env= declare_vars ((List.length xs)-1) H.empty xs in
  let _ : heap = eval_stmt env heap  stmt in
  ()
