open Ast

type cmd =
  | PushInt of int
  | PushBool of bool
  | Prim of bop
  | CondJmp of cmd list * cmd list
  | Grab           (* wstaw wartosc ze stosu do srodowiska *)
  | Access of int  (* wstaw wartosc ze srodowiska na stos *)
  | EndLet
  | PushClo of cmd list
  | Call
  | Return
  | Raise
  | BeginTry of cmd list * cmd list
  | EndTry
            
type vm_value =
  | VMInt of int
  | VMBool of bool
  | VMClosure of cmd list * vm_value list
  | VMRetAddr of cmd list * vm_value list

let eval_vm_op (op : bop) (v1 : vm_value) (v2 : vm_value) : vm_value =
  match op, v1, v2 with
  | Add,  VMInt i1, VMInt i2 -> VMInt (i1 + i2)
  | Sub,  VMInt i1, VMInt i2 -> VMInt (i1 - i2)
  | Mult, VMInt i1, VMInt i2 -> VMInt (i1 * i2)
  | Div,  VMInt i1, VMInt i2 -> VMInt (i1 / i2)
  | Eq,   VMInt i1, VMInt i2 -> VMBool (i1 = i2)
  | Lt,   VMInt i1, VMInt i2 -> VMBool (i1 < i2)
  | Gt,   VMInt i1, VMInt i2 -> VMBool (i1 > i2)
  | Leq,  VMInt i1, VMInt i2 -> VMBool (i1 <= i2)
  | Geq,  VMInt i1, VMInt i2 -> VMBool (i1 >= i2)
  | Neq,  VMInt i1, VMInt i2 -> VMBool (i1 <> i2)
  | _ -> failwith "type error"

let stack_size = 4096

let exec_prog p =
  (* Create empty stack *)
  let stack = Array.make stack_size (VMInt 0) in
  (* Stack pointer *)
  let sp = ref stack_size in
  (* Push a value on a stack *)
  let push v = sp := !sp - 1; stack.(!sp) <- v in
  (* Pop a value from a stack *)
  let pop () = let v = stack.(!sp) in sp := !sp + 1; v in
  let rec exec (p : cmd list) (env : vm_value list) (handlers : (cmd list * vm_value list) list): vm_value =
    match p with
    | [] -> pop ()
    | PushInt n :: p' -> push (VMInt n); exec p' env handlers
    | PushBool b :: p' -> push (VMBool b); exec p' env handlers
    | Prim op :: p' ->
      let v1 = pop () in
      let v2 = pop () in
      push (eval_vm_op op v2 v1);
      exec p' env handlers
    | CondJmp (t, e) :: p' ->
      (match pop () with
      | VMBool true  -> exec (t @ p') env handlers
      | VMBool false -> exec (e @ p') env handlers
      | _ -> failwith "error")
    | Grab :: p' -> exec p' (pop () :: env) handlers
    | Access n :: p' -> push (List.nth env n); exec p' env handlers
    | EndLet :: p' -> exec p' (List.tl env) handlers
    | PushClo q :: p' -> push (VMClosure (q, env)); exec p' env handlers 
    | Call :: p' ->
      (match pop () with
      | VMClosure (q, env') ->
        let v = pop () in
        push (VMRetAddr (p', env));
        exec q (v :: env') handlers
      | _ -> failwith "error")
    | Return :: _ ->
      let v = pop () in
      (match pop () with
      | VMRetAddr (p, env') -> push v; exec p env' handlers
      | _ -> failwith "error")
    | BeginTry(p1, q) :: p' ->
      exec p1 env ((q @ p', env) :: handlers) 
    | EndTry :: p' ->
      exec p' env (List.tl handlers)
    | Raise :: _ ->
      (match handlers with 
      | (p', env') :: handlers' -> exec p' env' handlers'
      | [] -> failwith "unhandled exception" )
  in
  exec p [] []
 
let print_value v =
  print_endline
    (match v with
    | VMInt  n     -> string_of_int n
    | VMBool true  -> "true"
    | VMBool false -> "false"
    | VMClosure _  -> "<fun>"
    | VMRetAddr _  -> "<ret-addr>")