(* abstract syntax tree *)

type bop = Mult | Div | Add | Sub | Eq | Lt | Gt | Leq | Geq | Neq

type ident = string

type expr =
  | Int of int
  | Bool of bool
  | Binop of bop * expr * expr
  | If of expr * expr * expr
  | Var of ident
  | Let of ident * expr * expr

module M = Map.Make(String)

type env = string M.t

(* funkcja ktora sprawdza czy dwa wyrazenia są alfa-rownowazne *)
let alpha_equiv (e1 : expr) (e2 : expr) : bool = 
  let rec compare (e1 : expr) (e2 : expr) (env1 : env) (env2 : env) : bool =
    match e1, e2 with
    | Int _, Int _ | Bool _, Bool _ -> e1 = e2
    | If (p1, t1, e1), If (p2, t2, e2) -> 
      compare p1 p2 env1 env2 && compare t1 t2 env1 env2 && compare e1 e2 env1 env2 
    | Binop (op, e1, e2), Binop (op2, e3, e4) -> op = op2 && compare e1 e3 env1 env2 && compare e2 e4 env1 env2
    | Let (x1, e1l, e1r), Let (x2, e2l, e2r) -> 
      compare e1l e2l env1 env2 && compare e1r e2r (M.add x1 x2 env1) (M.add x2 x1 env2)
    | Var x, Var y -> (
      match (M.find_opt x env1), (M.find_opt y env2) with 
      | Some x0, Some y0 -> x0 = y && y0 = x
      | None, None -> x = y
      | _ -> false )
    | _ -> false 
  in compare e1 e2 M.empty M.empty 


let all_subexprs expr = 
  let rec helper (expr : expr) (acc : expr list) = 
    match expr with
    | Int _ | Bool _ | Var _ -> acc
    | Binop (_, e1, e2) -> helper e1 (helper e2 (expr :: acc))
    | If (p, t, e) -> helper p (helper t (helper e (expr :: acc)))
    | Let (x, e1, e2) -> expr :: acc
in helper expr [] 


(* Funkcja contains sprawdza czy wyrażenie target znajduje się wewnątrz wyrażenia e *)
let rec contains (e : expr) (target : expr) : bool = 
  match e = target with 
  | true -> true 
  | false -> (
    match e with 
    | Int _ | Bool _ | Var _ -> false 
    | If (p, t, e) -> (contains p target) || (contains t target) || (contains e target)
    | Binop (op, e1, e2) -> (contains e1 target) || (contains e2 target)
    | Let (x, e1, e2) -> (contains e1 target) || (contains e2 target)
  )

let rec contains_any (e : expr) (targets : expr list) : bool = 
  match targets with 
  | [] -> false 
  | t :: ts -> if contains e t then true else contains_any e ts

(* Funkcja replace zamienia wyrażenia a-równoważne old_expr na new_expr w wyrażeniu expr o ile te podwyrażenia znalezion nie mają zmiennej związanej z listy bound *)
let rec replace (expr : expr) (old_expr : expr) (new_expr : expr) (bound : expr list) : expr =
  match (alpha_equiv expr old_expr) && not (contains_any expr bound) with
  | true -> new_expr 
  | _ -> (
    match expr with 
    | Int _ | Bool _ | Var _ -> expr 
    | Binop (op, e1, e2) -> 
      let e1' = replace e1 old_expr new_expr bound in 
      let e2' = replace e2 old_expr new_expr bound in 
      Binop (op, e1', e2')
    | If (p, t, e) -> 
      let p' = replace p old_expr new_expr bound in
      let t' = replace t old_expr new_expr bound in 
      let e' = replace e old_expr new_expr bound in
      If (p', t', e')
    | Let (x, e1, e2) -> expr
  )

(* Funkcja let która nie wchodzi w głąb letów *)
let cse_single (e : expr) : expr option =
  let all = all_subexprs e in
  let rec helper exprs exp =
    match exprs with 
    | e1 :: e' -> if alpha_equiv e1 exp then Some (Let("v0", e1, (replace e e1 (Var "v0") []))) else helper e' exp
    | _ -> None
  in 
  let rec helper2 exprs = 
    match exprs with
    | e1 :: e' -> (match helper e' e1 with
                  | Some exp -> Some exp
                  | None -> helper2 e')
    | _ -> None
  in helper2 all 

let rec find_let (elist: expr list) : expr option = 
  match elist with 
  | [] -> None
  | Let(x, e1, e2) :: elist' -> Some (Let(x, e1, e2))
  | _ :: elist' -> find_let elist'


let rec cse (e : expr) : expr option = 
  let all = all_subexprs e in 
  match cse_single e with 
  | Some expr -> Some expr 
  | None -> (
    match find_let all with 
    | None -> None 
    | Some (Let (x, e1, e2)) -> (
      match cse e2 with 
      | Some expr -> Some (Let (x, e1, expr))
      | None -> None 
    )
    | _ -> failwith "Bug"
  )