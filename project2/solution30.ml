(* Kornel Orawczak 346010 - Pracownia 2 Metody Programowania *)

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

(* Funkcja pomocnicza ktora sprawdza czy dwa wyrazenia 'e1', 'e2' są alfa-rownowazne *)
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

(* Prosta funkcja pomocnicza która zwraca posortowaną alfabetycznie listę unikalnych wolnych zmiennych w wyrażeniu 'e' *)
let free_variables (e : expr) : ident list =
  let rec iter (e : expr) (bound : ident list) (free : ident list) = 
    match e with 
    | Int _ | Bool _ -> free 
    | Binop (op, e1, e2) -> 
      (iter e1 bound free) @ (iter e2 bound free)
    | If (e1, e2, e3) -> 
      (iter e1 bound free) @ (iter e2 bound free) @ (iter e3 bound free)
    | Var x -> 
      if List.mem x bound then free 
      else x :: free
    | Let (y, e1, e2) -> 
      iter e2 (y :: bound) free 
  
  in List.sort_uniq String.compare (iter e [] [])


(* Funkcja pomocnicza 'contains' sprawdza czy wyrażenie 'target' znajduje się wewnątrz wyrażenia 'e' *)
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

(* Funkcja sprawdzająca czy pod wyrażenie ma sens, 
   dokładniej mówiąc czy wyrażenie 'e' zawiera jakąś ze zmiennych z 'vars' *)
let check_expr (e : expr) (vars : expr list) : expr list = 
  match e with
  | Int _ | Bool _ | Var _ -> []
  | _ -> if not (contains_any e vars) then [e] 
         else []
 

(* Funkcja która zwraca wszystkie pod wyrażenia, które przejdą 'check_expr' *)
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




(* Funkcja replace zamienia pod wyrażenia a-równoważne 'old_expr' na 'new_expr' w wyrażeniu 'expr',
   o ile podwyrażenia znalezione nie mają zmiennej związanej z listy bound *)
let rec replace (expr : expr) (old_expr : expr) (new_expr : expr) (bound : expr list) : expr =
  match (alpha_equiv expr old_expr) && not (contains_any expr bound) with
  | true -> new_expr 
  | false -> (
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
    | Let (x, e1, e2) -> 
      let e1' = replace e1 old_expr new_expr bound in
      let e2' = replace e2 old_expr new_expr (Var x :: bound) in
      Let (x, e1', e2')
  )

let cse (e : expr) : expr option =

  let subexprs = all_subexprs e in

  (* 2. Iter2 odpalone dla poszczególnego pod wyrażenia i listy możliwych wspólnych pod wyrażeń,
        szuka kandydatów na co najmniej pary wyrażeń równoważnych (a-równożanych + takie same zmienne wolne) *)
  let rec iter2 (expr : expr) (exprs : expr list) : expr option =
    match exprs with 
    | [] -> None
    | e' :: es -> 
      if (alpha_equiv e' expr) && (free_variables e' = free_variables expr)
      then Some (Let("v0", e', (replace e e' (Var "v0") []))) 
      else iter2 expr es
  in 

  (* 1. Zaczyna się od funkcji iter1, która idzie po każdym podwyrażeniu i dla niego odpala iter2 *)
  let rec iter1 (exprs : expr list) : expr option = 
    match exprs with
    | [] -> None
    | e' :: es -> (
      match iter2 e' es with
      | Some expr -> Some expr
      | None -> iter1 es
    )
  in iter1 subexprs