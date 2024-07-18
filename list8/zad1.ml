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

let rec subst (x : ident) (s : expr) (e : expr) : expr =
  match e with
  | Binop (op, e1, e2) -> Binop (op, subst x s e1, subst x s e2)
  | If (p, t, e) -> If (subst x s p, subst x s t, subst x s e)
  | Var y -> if x = y
                then s
                else e
  | Let (y, e1, e2) -> if x = y
                          then Let (y, subst x s e1, e2)
                          else Let (y, subst x s e1, subst x s e2)
  | _ -> e

let expr_of_value (v : value) : expr =
  match v with
  | VInt a -> Int a
  | VBool a -> Bool a

  let rec cp (e : expr) : expr = 
  match e with 
  | Int v -> Int v
  | Bool v -> e
  | Var x -> e
  | Binop (op, e1, e2) -> (
    match (cp e1), (cp e2) with 
    | Int v1, Int v2 -> expr_of_value (eval_op op (VInt v1) (VInt v2))
    | _ -> Binop (op, (cp e1), (cp e2))
  )
  | If (e1, e2, e3) -> (
    match (cp e1) with 
    | Bool true -> cp e2 
    | Bool false -> cp e3 
    | _ -> If (cp e1, cp e2, cp e3)
  )
  | Let (x, e2, e3) -> (
    match (cp e2) with 
    | Int v  -> cp (subst x (Int v) e3)
    | Bool v -> cp (subst x (Bool v) e3)
    | _ -> Let(x, cp e2, cp e3) 
  )
