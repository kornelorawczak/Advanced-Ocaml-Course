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
  | Raise4 of ident (* Raise z zadania 4 który ma etykietę *)
  | Raise5 of expr (* Raise z zadania 5 który ma wyrażenie do obliczenia i przekazania *)
  | Try of expr * ident * expr (* Try z obu zadań *)


(* Przykładowy program z zadania 4 do przetłumaczenia: 

   try raise "A"  
   with
      A -> 42 

   Parsowany jako Try( Raise "A", "A", Int 42) *)

(* Ten program w wersji z zadania 5: 

   try raise 42 
   with x -> x 

   Parsowany jako Try( Raise (Int 42), "x", Var "x") *)

let ex4 = Try(Raise4 "A", "A", Int 42)

let rec translate (e : expr) : expr = 
  match e with 
  | Int _ | Bool _ | Var _ -> e 
  | Binop(op, e1, e2) -> Binop(op, translate e1, translate e2)
  | Let(x, e1, e2) -> Let(x, translate e1, translate e2)
  | If(p, t, e) -> If(translate p, translate t, translate e)
  | Fun(x, e) -> Fun(x, translate e)
  | App(e1, e2) -> App(translate e1, translate e2)
  | Pair(e1, e2) -> Pair(translate e1, translate e2)
  | Fst e -> Fst(translate e)
  | Snd e -> Snd(translate e)
  | 