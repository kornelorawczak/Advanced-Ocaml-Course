open Ast

module StringMap = Map.Make(String)

type name_map = string StringMap.t


let rec find_id (x : var) (env : var option list) : int = 
  match env with 
  | [] -> failwith ("unbound variable" ^ x)
  | v :: env' -> if v = Some x then 0 else 1 + find_id x env'


let rec compile_aexp (exp : aexp) (env : var option list) (fname_map : name_map): cmd list = 
  match exp with 
  | Int n              -> [CONST n]
  | Var x              -> [TOP; LOAD (find_id x env)]
  | Binop (op, e1, e2) -> 
    compile_aexp e1 env fname_map @ [PUSH] 
    @ compile_aexp e2 (None :: env) fname_map @ [PRIM op]
  | Call (fname, args) -> 
    let found_name = StringMap.find fname fname_map in 
    let rec compile_args args env = 
      match args with 
      | [] -> []
      | x :: xs -> compile_aexp x env fname_map @ [PUSH] @ compile_args xs (None :: env) 
    in  
    compile_args args env @ [CALL found_name; LEAVE (List.length args)]


let rec compile_bexp (exp : bexp) (env : var option list) (fname_map : name_map): cmd list = 
  match exp with 
  | Bool false       -> [CONST 0]
  | Bool true        -> [CONST 1]
  | Cmp (op, e1, e2) -> compile_aexp e1 env fname_map @ [PUSH] @ compile_aexp e2 (None :: env) fname_map @ [CMP op]
  | And (b1, b2)     -> compile_bexp b1 env fname_map @ [BRANCH (compile_bexp b2 env fname_map, [CONST 0])]
  | Or (b1, b2)      -> compile_bexp b1 env fname_map @ [BRANCH ([CONST 1], compile_bexp b2 env fname_map)]
  | Not b            -> compile_bexp b  env fname_map @ [BRANCH ([CONST 0], [CONST 1])]

(* num_of_fun_vars zwraca listę zmiennych wewnątrz ciała obecnie rozpatrywanej funkcji,
   Zmienne lokalne od globalnych oddzielane są poprzez None *)
let rec num_of_fun_vars (env : var option list) : int = 
  match env with 
  | [] | None :: _ -> 0
  | Some _ :: env' -> 1 + num_of_fun_vars env'

let rec compile (prog : stmt list) (env : var option list) (fname_map : name_map) : cmd list = 
  match prog with 
  | [] -> []
  | Block stmts :: prog'     -> 
    compile stmts env fname_map 
    @ compile prog' env fname_map

  | Assgn (x, exp) :: prog'  -> 
    [TOP; PUSH] @ compile_aexp exp (None :: env) fname_map 
    @ [STORE (find_id x env)] @ compile prog' env fname_map

  | If (p, t, e) :: prog'    -> 
    compile_bexp p env fname_map 
    @ [BRANCH (compile [t] env fname_map, compile [e] env fname_map)] 
    @ compile prog' env fname_map

  | While (e, stmt) :: prog' -> 
    [WHILE (compile_bexp e env fname_map, compile [stmt] env fname_map)] 
    @ compile prog' env fname_map

  | Read  x :: prog'         -> 
    [TOP; PUSH; READ; STORE (find_id x env)] 
    @ compile prog' env fname_map

  | Write exp :: prog'       -> 
    compile_aexp exp env fname_map @ [WRITE] 
    @ compile prog' env fname_map

  | Return exp :: _          -> 
    compile_aexp exp env fname_map 
    @ [LEAVE (num_of_fun_vars env); RET] 


let rec update_env (env : var option list) (vars : var list) : var option list = 
  match vars with 
  | [] -> env 
  | v :: vars' -> update_env (Some v :: env) vars'

let rec flatten_funs (parent_name : string) (f : func) (n_map : name_map) : func list * name_map = 
  match f with 
  | Func(name, args, local_vars, local_funs, body) -> 
    let new_name = if parent_name = "" then name else parent_name ^ "_" ^ name in 
    let name_map = StringMap.add name new_name n_map in 
    let flattened_local_funs, name_map' = 
      List.fold_left (fun (acc, nm) func -> 
        let fl, nm' = flatten_funs new_name func nm in 
        (acc @ fl, nm')) ([], name_map) local_funs 
    in 
    (Func (new_name, args, local_vars, [], body)) :: flattened_local_funs, name_map'

let flatten_all (funs : func list) : func list * name_map = 
  List.fold_left (fun (acc, nm) func -> 
    let fl, nm' = flatten_funs "" func nm in 
    (acc @ fl, nm')) ([], StringMap.empty) funs

let rec compile_funs (funs : func list) (env : var option list) (fname_map : name_map) : (name * cmd list) list = 
  match funs with 
  | [] -> []
  | Func (name, args, local_vars, _, body) :: funs' ->
    let env' = (List.rev (List.map (fun x -> Some x) local_vars)) @ (None :: (update_env env args)) in 
    let compiled_body = [ENTER (List.length local_vars)] @ compile [body] env' fname_map in 
    (name, compiled_body) :: compile_funs funs' env fname_map


let compile_prog (program : prog) : vm_prog =
  match program with 
  | (vars, funs, stmt) -> 
    let flattened_funs, fname_map = flatten_all funs in 
    let env = List.rev (List.map (fun x -> Some x) vars) in 
    [ENTER (List.length vars)] @ compile [stmt] env fname_map, 
    (compile_funs flattened_funs (List.map (fun _ -> None) vars)) fname_map
