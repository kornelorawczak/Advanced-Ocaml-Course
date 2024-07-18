open Ast

let parse (s : string) : expr =
  Parser.prog Lexer.read (Lexing.from_string s)

module M = Map.Make(String)

type env = value M.t

and value =
  | VInt of int
  | VBool of bool
  | VClosure of ident * expr * env

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
      let new_env = M.add x r env in
      eval_env new_env e2
  | Var x ->
      (match M.find_opt x env with
      | Some v -> v
      | None -> failwith ("unbound value " ^ x))
  | Fun (x, e) -> VClosure (x, e, env)
  | App (e1, e2) ->
      (match eval_env env e1, eval_env env e2 with
      | VClosure (x, body, clo_env), v -> eval_env (M.add x v clo_env) body
      | _, _ -> failwith "type error")

let initial_env = M.empty
  |> M.add "abs" (parse "fun x -> if x < 0 then 0 - x else x" |> eval_env M.empty)
  |> M.add "mod" (parse "fun x -> fun y -> x - (x / y) * y" |> eval_env M.empty)
  |> M.add "fix" (parse "fun f -> (fun x -> fun y -> f (x x) y) (fun x -> fun y -> f (x x) y)" |> eval_env M.empty)

let eval : expr -> value = eval_env initial_env 

let interp (s : string) : value =
  eval (parse s)

open Vm

let rec find_index (x : 'a) (xs : 'a list) : int option =
  match xs with
  | [] -> None
  | y :: ys -> if x = y then Some 0
               else Option.map (fun x -> x + 1) (find_index x ys)

type idx_env = ident list

let rec compile (e : expr) (env : idx_env) : cmd list =
  match e with
  | Int n -> [PushInt n]
  | Bool b -> [PushBool b]
  | Binop (op, e1, e2) ->
     compile e1 env @ compile e2 env @ [Prim op]
  | If (p, t, e) -> compile p env @ [CondJmp (compile t env, compile e env)]
  | Let (x, e1, e2) -> compile e1 env @ [Grab] @ compile e2 (x :: env) @ [EndLet]
  | Var x -> (match find_index x env with
              | Some i -> [Access i]
              | None -> failwith ("unbound var " ^ x))
  | Fun (x, e) -> [PushClo (compile e (x :: env) @ [Return])]
  | App (e1, e2) -> compile e2 env @ compile e1 env @ [Call]


let flatten (prog : cmd list) : T.cmd list = 
  let rec it (prog : cmd list) (acc : T.cmd list) (path : string) : T.cmd list = 
    match prog with 
    | [] -> acc 
    | PushInt n :: prog' -> it prog' (acc @ [T.PushInt n]) path 
    | PushBool b :: prog' -> it prog' (acc @ [T.PushBool b]) path 
    | Prim op :: prog' -> it prog' (acc @ [T.Prim op]) path 
    | Grab :: prog' -> it prog' (acc @ [T.Grab]) path 
    | Access i :: prog' -> it prog' (acc @ [T.Access i]) path
    | EndLet :: prog' -> it prog' (acc @ [EndLet]) path 
    | Call :: prog' -> it prog' (acc @ [Call]) path 
    | Return :: prog' -> it prog' (acc @ [Return]) path 
    | CondJmp (t, e) :: prog' -> (
      let false_path = path ^ "F" in let end_path = path ^ "E" in let true_path = path ^ "T" in 
      let new_acc = acc @ [T.CondJmp false_path] @ (it t [] true_path) @ [T.Jmp end_path] @ [T.Lbl false_path] @ (it e [] false_path) in 
      it prog' (new_acc @ [T.Lbl end_path]) (path ^ "C")   
    )
    | PushClo q :: prog' -> it prog' (acc @ [T.PushClo path] @ [T.Lbl path] @ (it q [] (path ^ "f"))) (path ^ "P")
  in it prog [] "#"

(*
let fib = {|
  let fix = fun f -> (fun x -> fun y -> f (x x) y) (fun x -> fun y -> f (x x) y) in
  let fib = fix (fun fib -> fun x -> if x <= 1 then x else fib (x - 1) + fib (x - 2)) in
  fib 22 |};;
*)
