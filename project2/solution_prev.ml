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
let free_variables (e : expr) =
  let rec iter (e : expr) (bound : ident list) (free : ident list) = 
    match e with 
    | Int _ | Bool _ -> free 
    | Binop (op, e1, e2) -> (iter e1 bound free) @ (iter e2 bound free)
    | If (e1, e2, e3) -> (iter e1 bound free) @ (iter e2 bound free) @ (iter e3 bound free)
    | Var x -> if List.mem x bound = true then free else x :: free
    | Let (y, e1, e2) -> iter e2 (y :: bound) free 
  in List.sort_uniq String.compare (iter e [] [])


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

let expr_equal (e1 : expr) (e2 : expr) : bool = 
  alpha_equiv e1 e2 && (free_variables e1 = free_variables e2)

(* Collect all subexpressions within the given expression, considering scope *)
(* let all_subexprs expr = 
  let rec helper (scope : (ident * expr) list) (e : expr) (acc) = 
    match e with
    | Int _ | Bool _ | Var _ -> acc
    | Binop (_, e1, e2) -> helper scope e1 (helper scope e2 ((e, scope) :: acc))
    | If (cond, e1, e2) -> helper scope cond (helper scope e1 (helper scope e2 ((e, scope) :: acc)))
    | Let (v, e1, e2) -> helper scope e1 (helper ((v, e1) :: scope) e2 ((e, scope) :: acc))
in helper [] expr [] *)
let rec all_subexprs (e : expr) = 
  let rec helper scope expr acc = match expr with
    | Int _ | Bool _ | Var _ -> acc
    | Binop (_, e1, e2) -> helper scope e1 (helper scope e2 (expr :: acc))
    | If (cond, e1, e2) -> helper scope cond (helper scope e1 (helper scope e2 (expr :: acc)))
    | Let (v, e1, e2) -> helper scope e1 (helper ((v, e1) :: scope) e2 (expr :: acc))
  in helper [] e [] 
let find_equivalent_subexprs expr =
  let subexprs = all_subexprs expr in
  let rec find_pairs acc = function
    | [] -> acc
    | hd :: tl ->
        let pairs_with_hd = List.filter (fun x -> alpha_equiv hd x && (free_variables hd = free_variables x)) tl in
        let new_acc = if List.length pairs_with_hd > 0 then (hd :: pairs_with_hd) :: acc else acc in
        find_pairs new_acc tl
  in
  List.sort_uniq compare (List.hd (find_pairs [] subexprs))

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


let e0 =
  If (Binop (Gt, Binop (Add, Var "x", Var "y"), Int 0),Binop (Add, Var "x", Var "y"),Int 0)

(*(Let ("v1", Binop (Mult, Int 2, Var "x"),
   Binop (Add, Var "v1", Binop (Add, Int 1, Var "v1"))))*)
let e1 =
  Binop(Add, 
    Binop (Mult, Int 2, Var "x"),
    Binop (Add, Int 1, Binop (Mult, Int 2, Var "x")))

(*wyrazenie z let aby nie podstawialo*)
(* DO POPRAWY, ABY BRALO POD UWAGE WIAZANIA LEPIEJ*)
let e2 =
  Binop (Add,
    Binop (Mult, Var "x", Int 10),
    Let ("x", Int 3,
         Binop (Mult, Var "x", Int 10)))

(*(Let ("v2", Binop (Add, Var "x", Var "y"), Binop (Add, Var "v2", Var "v2")))*)
let e3 =
  Binop (Add,
    Binop(Add, Var "x", Var "y"),
    Binop(Add, Var "x", Var "y"))

(*przyklad alfa rownowaznosc
   (Let ("v3", Let ("x", Int 1, Binop (Add, Var "x", Var "z")),
   Binop (Add, Var "v3", Binop (Mult, Int 10, Var "v3"))))*)
let e4 =
  Binop (Add, Let ("x", Int 1, Binop (Add, Var "x", Var "z")),Binop (Mult,Int 10,Let ("y", Int 1, Binop (Add, Var "y", Var "z"))))

(*przyklad koniec zadania*)
(*(Let ("v4", Binop (Mult, Var "z", Int 10),
   If (Var "x", Binop (Add, Var "v4", Var "v4"), Int 0)))*)
let e5 = 
  If (
    Var "x",
    Binop (
      Add,
      Binop (Mult, Var "z", Int 10),
      Binop (Mult, Var "z", Int 10)
    ),
    Int 0
  )

(*przyklad 3 te same wyrazenia
(Let ("v5", Binop (Add, Var "x", Var "y"), If (Var "v5", Var "v5", Var "v5")))*)
let e6 =
  If (
    Binop (Add, Var "x", Var "y"),
    Binop (Add, Var "x", Var "y"),
    Binop (Add, Var "x", Var "y")
  )

let e7 = 
  Let ("x", Binop (Mult, Int 3, Int 10),
  Let ("x", Binop (Mult, Binop (Mult, Int 3, Int 10), Int 2),
    Binop (Add, Var "x", Binop (Mult, Int 3, Int 10))))

let e8 = Let("x", Binop(Add, Var "x", Int 10), Binop(Add, Var "x", Int 10))