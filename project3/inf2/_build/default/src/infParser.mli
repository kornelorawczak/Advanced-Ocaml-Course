
(* The type of tokens. *)

type token = 
  | WRITE
  | WHILE
  | VAR
  | TRUE
  | TIMES
  | THEN
  | SKIP
  | RPAREN
  | RETURN
  | READ
  | PLUS
  | OR
  | NOT
  | NEQ
  | MINUS
  | LT
  | LPAREN
  | LEQ
  | INT of (int)
  | IF
  | IDENT of (string)
  | GT
  | GEQ
  | FUNCTION
  | FALSE
  | EQ
  | EOF
  | END
  | ELSE
  | DO
  | DIV
  | COMMA
  | BEGIN
  | ASSGN
  | AND

(* This exception is raised by the monolithic API functions. *)

exception Error

(* The monolithic API. *)

val prog: (Lexing.lexbuf -> token) -> Lexing.lexbuf -> (Ast.prog)
