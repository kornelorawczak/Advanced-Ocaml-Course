open Ast

let rec find_id (x : var) (env : var option list) : int = 
  match env with 
  | [] -> failwith ("unbound variable" ^ x)
  | v :: env' -> if v = Some x then 0 else 1 + find_id x env'

let neg (cmpop : cmpop) : cmpop = 
  match cmpop with 
  | Eq  -> Neq 
  | Neq -> Eq
  | Lt  -> Geq 
  | Gt  -> Leq 
  | Leq -> Gt
  | Geq -> Lt


let rec compile_aexp (exp : aexp) (env : var option list) (path : string) : cmd list = 
  match exp with 
  | Int n -> [CONST n]
  | Var x -> [TOP; LOAD (find_id x env)]
  | Binop (op, e1, e2) -> compile_aexp e1 env path @ [PUSH] @ compile_aexp e2 (None :: env) path @ [PRIM op]
  | Call (fname, args) -> 
    let compiled_args = List.concat_map (fun arg -> compile_aexp arg env path @ [PUSH]) args in 
    let new_name = if path = "" then fname else path ^ "_" ^ fname in 
    compiled_args @ [CALL new_name; LEAVE (List.length args)]


let rec compile_bexp (exp : bexp) (env : var option list) (path : string): cmd list = 
  match exp with 
  | Bool b -> if b then [CONST 1] else [CONST 0]
  | Cmp (cmpop, e1, e2) -> compile_aexp e1 env path @ [PUSH] @ compile_aexp e2 (None :: env) path @ [CMP cmpop]
  | And (b1, b2) -> compile_bexp b1 env path @ [BRANCH (compile_bexp b2 env path, [CONST 0])]
  | Or (b1, b2) ->  compile_bexp b1 env path @ [BRANCH ([CONST 1], compile_bexp b2 env path)]
  | Not b -> 
    (match b with 
    | Bool b' -> compile_bexp (Bool (not b')) env path
    | Cmp (cmpop, e1, e2) -> compile_bexp (Cmp(neg cmpop, e1, e2)) env path
    | And (b1, b2) -> compile_bexp (Or (Not b1, Not b2)) env path
    | Or (b1, b2) -> compile_bexp (And (Not b1, Not b2)) env path
    | Not b' -> compile_bexp b' env path)

(* num_of_fun_vars zwraca listę zmiennych wewnątrz ciała obecnie rozpatrywanej funkcji,
   Zmienne lokalne od globalnych oddzielane są poprzez None *)
let rec num_of_fun_vars (env : var option list) : int = 
  match env with 
  | [] | None :: _ -> 0
  | Some _ :: env' -> 1 + num_of_fun_vars env'

let rec compile (prog : stmt list) (env : var option list) (path : string) : cmd list = 
  match prog with 
  | Block stmts :: prog' -> compile stmts env path @ compile prog' env path
  | Assgn (x, exp) :: prog' -> [TOP; PUSH] @ compile_aexp exp (None :: env) path @ [STORE (find_id x env)] @ compile prog' env path
  | If (p, t, e) :: prog' -> compile_bexp p env path @ [BRANCH (compile [t] env path, compile [e] env path)] @ compile prog' env path
  | While (e, stmt) :: prog' -> [WHILE (compile_bexp e env path, compile [stmt] env path)] @ compile prog' env path
  | Read  x :: prog' -> [TOP; PUSH; READ; STORE (find_id x env)] @ compile prog' env path
  | Write exp :: prog' -> compile_aexp exp env path @ [WRITE] @ compile prog' env path
  | Return exp :: prog' -> compile_aexp exp env path @ [LEAVE (num_of_fun_vars env); RET] @ compile prog' env path
  | [] -> []

let rec update_env (env : var option list) (vars : var list) : var option list = 
  match vars with 
  | [] -> env 
  | v :: vars' -> update_env (Some v :: env) vars'

let rec flatten_funs (path : string) (f : func) : func list = 
  match f with 
  | Func(name, args, local_vars, local_funs, body) -> 
    let new_name = if path = "" then name else path ^ "_" ^ name in 
    let flattened_local_funs = 
      List.concat_map (flatten_funs new_name) local_funs
    in 
    (Func (new_name, args, local_vars, [], body)) :: flattened_local_funs


let rec compile_funs (funs : func list) (env : var option list) (path : string) : (name * cmd list) list = 
  match funs with 
  | [] -> []
  | Func (name, args, local_vars, local_funs, body) :: funs' ->
    let env' = (List.rev(List.map (fun x -> Some x) local_vars)) @ (None :: (update_env env args)) in 
    let compiled_body = [ENTER (List.length local_vars)] @ compile [body] env' path in 
    let new_name = if path = "" then name else path ^ "_" ^ name in 
    (name, compiled_body) :: compile_funs local_funs env new_name @ compile_funs funs' env path


let compile_prog (program : prog) : vm_prog =
  match program with 
  | (vars, funs, stmt) -> 
    let env = List.rev(List.map (fun x -> Some x) vars) in 
    ([ENTER (List.length vars)] @ compile [stmt] env "", (compile_funs funs (List.map (fun _ -> None) vars)) "")
