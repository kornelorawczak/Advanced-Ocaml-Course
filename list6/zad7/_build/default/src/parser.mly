%{
open Ast
%}

%token <int> INT
%token TIMES
%token DIV
%token PLUS
%token MINUS
%token LPAREN
%token RPAREN
%token EQ
%token LESS
%token LESSEQ
%token MORE
%token MOREEQ
%token DIFF
%token TRUE
%token FALSE
%token IF
%token THEN
%token ELSE
%token EOF
%token OR
%token AND

%start <Ast.expr> prog

%nonassoc ELSE
%nonassoc AND OR 
%nonassoc EQ LESS LESSEQ MORE MOREEQ DIFF
%left PLUS MINUS
%left TIMES DIV

%%

prog:
  | e = expr; EOF { e }
  ;

expr:
  | i = INT { Int i }
  | e1 = expr; PLUS; e2 = expr { Binop(Add, e1, e2) }
  | e1 = expr; MINUS; e2 = expr { Binop(Sub, e1, e2) }
  | e1 = expr; DIV; e2 = expr { Binop(Div, e1, e2) }
  | e1 = expr; TIMES; e2 = expr { Binop(Mult, e1, e2) }
  | LPAREN; e = expr; RPAREN { e }
  | TRUE { Bool true }
  | FALSE { Bool false }
  | e1 = expr; EQ; e2 = expr { Binop(Eq, e1, e2) }
  | e1 = expr; LESS; e2 = expr { Binop(Less, e1, e2) }
  | e1 = expr; LESSEQ; e2 = expr { Binop(LessEq, e1, e2) }
  | e1 = expr; MORE; e2 = expr { Binop(More, e1, e2) }
  | e1 = expr; MOREEQ; e2 = expr { Binop(MoreEq, e1, e2) }
  | e1 = expr; DIFF; e2 = expr { Binop(Diff, e1, e2) }
  | e1 = expr; OR; e2 = expr { Or(e1, e2) }
  | e1 = expr; AND; e2 = expr { And(e1, e2) }
  | IF; e1 = expr; THEN; e2 = expr; ELSE; e3 = expr { If(e1, e2, e3) }
  ;
