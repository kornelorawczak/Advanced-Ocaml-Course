type bop = Mult | Div | Add | Sub | Eq | Lt | Gt | Leq | Geq | Neq | And | Or

type ident = string
                                                                         
type expr =
  | Int of int
  | Bool of bool
  | Var of ident
  | Binop of bop * expr * expr
  | If of expr * expr * expr
  | Let of ident * expr * expr


let closed (e : expr) : bool = 
  let rec checker (ident_list : ident list) (e : expr) : bool = 
  match e with 
  | Int _ | Bool _ -> true 
  | Var x -> List.mem x ident_list
  | Binop (op, e1, e2) -> checker ident_list e1 && checker ident_list e2
  | If (e1, e2, e3) -> checker ident_list e1 && checker ident_list e2 && checker ident_list e3
  | Let (x, e1, e2) -> checker ident_list e1 && checker (x :: ident_list) e2
  in checker [] e