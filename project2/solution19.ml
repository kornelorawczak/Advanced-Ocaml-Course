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


(* Funkcja pomocnicza zwracająca wolne zmienne w wyrażeniu *)
let free_variables (e : expr) (bound_initial : ident list)=
  let rec iter (e : expr) (bound : ident list) (free : ident list) = 
    match e with 
    | Int _ | Bool _ -> free 
    | Binop (op, e1, e2) -> (iter e1 bound free) @ (iter e2 bound free)
    | If (e1, e2, e3) -> (iter e1 bound free) @ (iter e2 bound free) @ (iter e3 bound free)
    | Var x -> if List.mem x bound = true then free else x :: free
    | Let (y, e1, e2) -> iter e2 (y :: bound) free 
  in List.sort_uniq String.compare (iter e bound_initial [])


(* Funkcja pomocnicza zastępująca wystąpienia podwyrażeń w wyrażeniu *)
let rec replace expr old_expr new_expr =
  match expr = old_expr with
  | true -> new_expr 
  | _ -> (
    match expr with 
    | Int _ | Bool _ | Var _ -> expr 
    | Binop (op, e1, e2) -> Binop (op, replace e1 old_expr new_expr, replace e2 old_expr new_expr)
    | If (e1, e2, e3) -> If (replace e1 old_expr new_expr, replace e2 old_expr new_expr, replace e3 old_expr new_expr)
    | Let (x, e1, e2) -> Let (x, replace e1 old_expr new_expr, replace e2 old_expr new_expr)
  )

(* Collect all subexpressions within the given expression, considering scope *)
let all_subexprs expr = 
  let rec helper (bound : ident list) (e : expr) (acc) = 
    match e with
    | Int _ | Bool _ | Var _ -> acc
    | Binop (_, e1, e2) -> helper bound e1 (helper bound e2 ((e, bound) :: acc))
    | If (cond, e1, e2) -> helper bound cond (helper bound e1 (helper bound e2 ((e, bound) :: acc)))
    | Let (v, e1, e2) -> helper bound e1 (helper (v :: bound) e2 ((e, bound) :: acc))
in helper [] expr [] 

let find_equivalent_subexprs expr =
  let subexprs = all_subexprs expr in
  let rec find_pairs acc = function
    | [] -> acc
    | (e, bound) :: tl ->
        let pairs_with_e = List.filter (fun (x, _) -> alpha_equiv e x) tl in
        let new_acc = if List.length pairs_with_e > 0 then ((e, bound) :: pairs_with_e) :: acc else acc in
        find_pairs new_acc tl
  in
  let initial = List.sort_uniq compare (List.hd (find_pairs [] subexprs)) in 
  if List.length initial < 2 then (List.map (fun (x,y) -> x) initial) else 
  let rec second_bound_check starter e_list acc = 
    match e_list with 
    | [] -> acc 
    | hd :: tl -> if free_variables (fst starter) (snd starter) = free_variables (fst hd) (snd hd) then 
      second_bound_check starter tl ((fst hd) :: acc) else second_bound_check starter tl acc 
  in let after_second = second_bound_check (List.hd initial) (List.tl initial) [] in 
  if after_second != [] then (fst (List.hd initial)) :: after_second else []


let cse (e : expr) : expr option = 
  let to_change = find_equivalent_subexprs e in 
  if to_change = [] then None else 
    let rec changer e to_change = 
      match to_change with 
      | [] -> Some e 
      | hd :: tl -> changer (replace e hd (Var "v0")) tl 
    in match changer e to_change with 
    | Some e -> Some (Let("v0", List.hd to_change, e))
    | _ -> failwith "Bug"

