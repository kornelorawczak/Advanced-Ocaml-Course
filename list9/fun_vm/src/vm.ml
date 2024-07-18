open Ast

type cmd =
  | PushInt of int
  | PushBool of bool
  | Prim of bop
  | CondJmp of cmd list * cmd list
  | Grab           (* wstaw wartosc ze stosu do srodowisko *)
  | Access of int  (* wstaw wartosc ze srodowiska na stos *)
  | EndLet
  | PushClo of cmd list
  | Call
  | Return
            
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

let rec exec (p : cmd list) (s : vm_value list) (env : vm_value list) : vm_value =
  match p, s with
  | [], [v] -> v
  | PushInt n :: p', _ -> exec p' (VMInt n :: s) env
  | PushBool b :: p', _ -> exec p' (VMBool b :: s) env
  | Prim op :: p', (v1 :: v2 :: s) -> exec p' (eval_vm_op op v2 v1 :: s) env
  | CondJmp (t, e) :: p', VMBool v :: s' -> if v then exec (t @ p') s' env
                                            else exec (e @ p') s' env
  | Grab :: p', v :: s' -> exec p' s' (v :: env)
  | Access n :: p', _ -> exec p' (List.nth env n :: s) env
  | EndLet :: p', _ -> exec p' s (List.tl env)
  | PushClo q :: p', _ -> exec p' (VMClosure (q, env) :: s) env
  | Call :: p', VMClosure (q, env') :: v :: s' ->
     exec q (VMRetAddr (p', env) :: s') (v :: env')
  | Return :: _, v :: VMRetAddr (p, env') :: s' -> exec p (v :: s') env'
  | _, _ -> failwith "error"
       
let exe p = exec p [] []

module T = struct
  type cmd =
  | PushInt of int
  | PushBool of bool
  | Prim of bop
  | Jmp of string
  | CondJmp of string
  | Grab
  | Access of int
  | EndLet
  | PushClo of string
  | Call 
  | Return
  | Lbl of string
  end


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