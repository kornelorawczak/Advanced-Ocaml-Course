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

(* Funkcja sprawdzająca czy dwa wyrażenia są a-równoważne *)
let alpha_equiv (e1 : expr) (e2 : expr) : bool = 
  let rec compare (e1 : expr) (e2 : expr) (env1 : env) (env2 : env) : bool =
    match e1, e2 with
    | Int _, Int _ | Bool _, Bool _ -> e1 = e2
    | If (p1, t1, e1), If (p2, t2, e2) -> 
      compare p1 p2 env1 env2 && compare t1 t2 env1 env2 && compare e1 e2 env1 env2 
    | Binop (op, e1, e2), Binop (op2, e3, e4) -> 
      op = op2 && compare e1 e3 env1 env2 && compare e2 e4 env1 env2
    | Let (x1, e1l, e1r), Let (x2, e2l, e2r) -> 
      compare e1l e2l env1 env2 && compare e1r e2r (M.add x1 x2 env1) (M.add x2 x1 env2)
    | Var x, Var y -> (
      match (M.find_opt x env1), (M.find_opt y env2) with 
      | Some x0, Some y0 -> x0 = y && y0 = x
      | None, None -> x = y
      | _ -> false )
    | _ -> false 
  in compare e1 e2 M.empty M.empty 

(* Funkcja contains sprawdza czy wyrażenie 'target' znajduje się wewnątrz wyrażenia 'e' *)
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

(* Funkcja sprawdza czy dane wyrażenie (expr) zawiera jakikolwiek z wyrażeń z listy targets *)
let rec contains_any (e : expr) (targets : expr list) : bool = 
  match targets with 
  | [] -> false 
  | t :: ts -> 
    if contains e t then true 
    else contains_any e ts

(* Funkcja sprawdzająca czy pod wyrażenie zawiera jakieś zmienne związane z listy 'vars' *)
let check_expr (e : expr) (vars : expr list) : expr list = 
  match e with
  | Int _ | Bool _ | Var _ -> []
  | _ -> if not (contains_any e vars) then [e] 
         else []
 
(* Funkcja która zwraca wszystkie pod wyrażenia bez zmiennych związanych (takie które przejdą 'check_expr') *)
let all_subexprs (e : expr) : expr list = 
  let rec iter (e : expr) (vars : expr list) (acc : expr list) =
    match e with
    | Int _ | Bool _ | Var _ -> acc
    | Binop (_, e1, e2) ->  
      let new_acc = iter e2 vars (check_expr e1 vars @ check_expr e2 vars @ acc) in 
      iter e1 vars new_acc
    | If (p, t, e) -> 
      let new_acc = iter t vars (iter e vars (check_expr p vars @ check_expr t vars @ check_expr e vars @ acc)) 
      in iter p vars new_acc
    | Let (x, e1, e2) -> 
      let new_vars = (Var x :: vars) in 
      let new_acc = iter e2 new_vars (check_expr e1 new_vars @ check_expr e2 new_vars @ acc) in 
      iter e1 new_vars new_acc  
  in iter e [] [] 

(* Bardzo prosta funkcja która szuka let-wyrażenia *)
let rec find_let (e : expr) : expr option = 
  match e with 
  | Let(x, e1, e2) -> Some e
  | Int _ | Bool _ | Var _ -> None
  | Binop(op, e1, e2) -> (
    match find_let e1 with
    | Some e -> Some e 
    | None -> find_let e2 )
  | If(p, t, e) -> (
    match find_let p with 
    | Some e -> Some e 
    | None -> (
      match find_let t with 
      | Some e -> Some e
      | None -> find_let e
    ))

(* Funkcja replace zamienia wyrażenia a-równoważne old_expr na new_expr w wyrażeniu expr,
   o ile te podwyrażenia znalezion nie mają zmiennej związanej  *)
let replace (expr : expr) (old_expr : expr) (new_expr : expr) : expr = 
  let rec replace_aux (expr : expr) (old_expr : expr) (new_expr : expr) (bound : expr list) : expr =
    match (alpha_equiv expr old_expr) && not (contains_any expr bound) with
    | true -> new_expr 
    | _ -> (
      match expr with 
      | Int _ | Bool _ | Var _ -> expr 
      | Binop (op, e1, e2) -> 
        let e1' = replace_aux e1 old_expr new_expr bound in 
        let e2' = replace_aux e2 old_expr new_expr bound in 
        Binop (op, e1', e2')
      | If (p, t, e) -> 
        let p' = replace_aux p old_expr new_expr bound in
        let t' = replace_aux t old_expr new_expr bound in 
        let e' = replace_aux e old_expr new_expr bound in
        If (p', t', e')
      | Let (x, e1, e2) -> 
        let e1' = replace_aux e1 old_expr new_expr bound in
        let e2' = replace_aux e2 old_expr new_expr (Var x :: bound) in
        Let (x, e1', e2')
    )
  in replace_aux expr old_expr new_expr []


(* Funkcja 'cse unbound' przechodzi kwadratowo przez liste podwyrażeń, nie biorąc pod uwagę tych ze zmiennymi związanymi,
   takie podwyrażenia zostaną rozpatrzone osobno w funkcji 'cse' *)
let cse_unbound (main_expr : expr) : expr option =
  let subexprs = all_subexprs main_expr in
  (* 2. Iter2 odpalone dla poszczególnego pod wyrażenia i listy możliwych wspólnych pod wyrażeń,
        szuka kandydatów na co najmniej pary wyrażeń równoważnych *)
  let rec iter2 expr exprs =
    match exprs with 
    | [] -> None
    | e :: rest -> 
      if alpha_equiv e expr 
      then Some (Let("v0", e, (replace main_expr e (Var "v0")))) 
      else iter2 expr rest
  in 
  (* 1. Zaczyna się od funkcji iter1, która idzie po każdym podwyrażeniu i dla niego odpala iter2 *)
  let rec iter1 exprs = 
    match exprs with
    | [] -> None
    | e :: rest -> (
      match iter2 e rest with
      | Some expr -> Some expr
      | None -> iter1 rest
    )
  in iter1 subexprs

(* Jako że cse_unbound bierzę pod uwagę tylko niezwiązane podwyrażenia to teraz trzeba wziąc pod uwagę jeszcze te związane *)  
let cse (e : expr) : expr option = 
  match cse_unbound e with
  | Some e -> Some e 
  | None -> (
    match find_let e with 
    | None -> None
    | Some Let(x, e1, e2) -> ( 
      match cse_unbound e2 with 
      | None -> None
      | Some cse_let -> Some (replace e (Let(x, e1, e2)) (Let(x, e1, cse_let))) 
    )
    | _ -> assert false
  )