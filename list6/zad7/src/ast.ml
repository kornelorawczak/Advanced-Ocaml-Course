(* abstract syntax tree *)

type bop = Mult | Div | Add | Sub | Eq | Less | LessEq | More | MoreEq | Diff

type expr =
  | Int of int
  | Bool of bool
  | Binop of bop * expr * expr
  | If of expr * expr * expr
  | Or of expr * expr 
  | And of expr * expr 
                               
