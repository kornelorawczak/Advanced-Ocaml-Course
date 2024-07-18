(* abstract syntax tree *)

type bop = Mult | Div | Add | Sub | Eq | Lt | Gt | Leq | Geq | Neq | And | Or

type ident = string
                                                                         
type expr =
  | Int of int
  | Bool of bool
  | Var of ident
  | Binop of bop * expr * expr
  | If of expr * expr * expr
  | Let of ident * expr * expr
  | Fun of ident * expr
  | App of expr * expr
  | Pair of expr * expr
  | Fst  of expr
  | Snd  of expr
  | Raise of expr (* Zmiana na raise z wyrażeniem obliczanym *)
  | Try of expr * ident * expr (* Zmiana na try z zmienną do której oblicza się raise *)
