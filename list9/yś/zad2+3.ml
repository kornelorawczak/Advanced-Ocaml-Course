type bop = Mult | Div | Add | Sub | Eq | Lt | Gt | Leq | Geq | Neq | And | Or

type ident = string
                                                                         
type expr =
  | Int of int
  | Bool of bool
  | Var of ident
  | Binop of bop * expr * expr
  | If of expr * expr * expr
  | Let of ident * expr * expr

type value =
  | VInt of int
  | VBool of bool

let eval_op (op : bop) (v1 : value) (v2 : value) : value =
  match op, v1, v2 with
  | Add,  VInt i1, VInt i2 -> VInt (i1 + i2)
  | Sub,  VInt i1, VInt i2 -> VInt (i1 - i2)
  | Mult, VInt i1, VInt i2 -> VInt (i1 * i2)
  | Div,  VInt i1, VInt i2 -> VInt (i1 / i2)
  | Eq,   VInt i1, VInt i2 -> VBool (i1 = i2)
  | Lt,   VInt i1, VInt i2 -> VBool (i1 < i2)
  | Gt,   VInt i1, VInt i2 -> VBool (i1 > i2)
  | Leq,  VInt i1, VInt i2 -> VBool (i1 <= i2)
  | Geq,  VInt i1, VInt i2 -> VBool (i1 >= i2)
  | Neq,  VInt i1, VInt i2 -> VBool (i1 <> i2)
  | _ -> failwith "type error"

module M = Map.Make(String)

type env = value M.t

let rec eval_env (env : env) (e : expr) : value =
  match e with
  | Int n -> VInt n
  | Bool b -> VBool b
  | If (p, t, e) ->
      (match eval_env env p with
      | VBool true -> eval_env env t
      | VBool false -> eval_env env e
      | _ -> failwith "type error")
  | Binop (And, e1, e2) ->
      (match eval_env env e1 with
      | VBool true -> eval_env env e2
      | VBool false -> VBool false
      | _ -> failwith "type error")
  | Binop (Or, e1, e2) ->
      (match eval_env env e1 with
      | VBool false -> eval_env env e2
      | VBool true -> VBool true
      | _ -> failwith "type error")
  | Binop (op, e1, e2) -> eval_op op (eval_env env e1) (eval_env env e2)
  | Let (x, e1, e2) ->
      let r = eval_env env e1 in
      let new_env = M.update x (fun _ -> Some r) env in
      eval_env new_env e2
  | Var x ->
      (match M.find_opt x env with
      | Some v -> v
      | None -> failwith ("unbound value" ^ x))

type env2 = string M.t 
let alpha_equiv (e1 : expr) (e2 : expr) : bool = 
  let rec compare (e1 : expr) (e2 : expr) (env1 : env2) (env2 : env2) : bool =
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
(* Let x = 2 in Let y = 3 in Let z = y + x in z *)
(* Let x = 2 in Let x = 3 in Let z = x + x in z *)

let rename_expr (e : expr) : expr = 
  let rec step (e : expr) (env : env2) (next_string : string) : expr =
    match e with 
    | Int _ | Bool _ -> e
    | If (p, t, e) -> 
      If (step p env (next_string ^ "P"), step t env (next_string ^ "T"), step e env (next_string ^ "E"))
    | Binop (b, e1, e2) -> Binop (b, step e1 env (next_string ^ "L"), step e2 env (next_string ^ "R"))
    | Let (x, e1, e2) -> 
      let new_env = M.add x next_string env in 
      Let (next_string, step e1 env (next_string ^ "L"), step e2 new_env (next_string ^ "R"))
    | Var x -> (
      match M.find_opt x env with 
      | Some new_x -> Var new_x
      | None -> Var x )
    in step e M.empty "#"

let test1 = Let("x", Int 1, Binop (Add, Let ("y", Int 2, Binop (Add, Binop (Add, Var "x", Var "y"), Var "z")), Let("x", Var "x", Var "x")))