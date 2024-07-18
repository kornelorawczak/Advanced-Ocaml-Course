open Ast

module M = Map.Make(String)

exception Type_error
exception Unbound_var of ident
exception Several_used  
exception MyExn

type env = value M.t

and value =
  | VUnit
  | VInt of int
  | VBool of bool
  | VClosure of ident * expr * env
  | VPair of value * value
  | VCtor of cname * value

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
  | _ -> raise Type_error

let rec cname_in_list (c : cname) (cs : cname list) = 
  match cs with 
  | [] -> false 
  | c' :: cs' -> if c = c' then true else cname_in_list c cs'

  let match_pattern env v p =
    let rec mp env v p used =
      match v, p with
      | _,       PWildcard  -> Some env, used
      | VUnit,   PUnit      -> Some env, used
      | _,       PUnit      -> None, used
      | VInt n,  PInt m when n = m -> Some env, used
      | _,       PInt _     -> None, used
      | VBool x, PBool y when x = y -> Some env, used
      | _,       PBool _    -> None, used
      | _,       PVar  x    -> 
        if List.mem x used 
          then failwith "double variable name in match"
        else 
          Some (M.add x v env), (x :: used)
      | VCtor(c1, v), PCtor(c2, p) when c1 = c2 ->
        mp env v p used
      | _, PCtor _ -> None, used
      | VPair(v1, v2), PPair(p1, p2) ->
        (match mp env v1 p1 used with
        | None, used -> None, used
        | Some env, used -> mp env v2 p2 used)
      | _, PPair _ -> None, used
    in 
    fst (mp env v p [])

let rec eval_env (env : env) (e : expr) : value =
  match e with
  | Unit  -> VUnit
  | Int n -> VInt n
  | Bool b -> VBool b
  | Ctor(c, e) -> VCtor(c, eval_env env e)
  | If (p, t, e) ->
      (match eval_env env p with
      | VBool true -> eval_env env t
      | VBool false -> eval_env env e
      | _ -> raise Type_error)
  | Binop (And, e1, e2) ->
      (match eval_env env e1 with
      | VBool true -> eval_env env e2
      | VBool false -> VBool false
      | _ -> raise Type_error)
  | Binop (Or, e1, e2) ->
      (match eval_env env e1 with
      | VBool false -> eval_env env e2
      | VBool true -> VBool true
      | _ -> raise Type_error)
  | Binop (op, e1, e2) -> eval_op op (eval_env env e1) (eval_env env e2)
  | Let (x, e1, e2) ->
      let r = eval_env env e1 in
      let new_env = M.add x r env in
      eval_env new_env e2
  | Var x ->
      (match M.find_opt x env with
      | Some v -> v
      | None -> raise (Unbound_var x))
  | Fun (x, e) -> VClosure (x, e, env)
  | App (e1, e2) ->
      (match eval_env env e1, eval_env env e2 with
      | VClosure (x, body, clo_env), v -> eval_env (M.add x v clo_env) body
      | _, _ -> raise Type_error)
  | Pair(e1, e2) ->
      VPair(eval_env env e1, eval_env env e2)
  | Fst e ->
      (match eval_env env e with
      | VPair(v1, _) -> v1
      | _ -> raise Type_error)
  | Snd e ->
      (match eval_env env e with
      | VPair(_, v2) -> v2
      | _ -> raise Type_error)
  | Raise -> raise MyExn
  | Try(e1, e2) ->
      (try eval_env env e1 with
      | MyExn -> eval_env env e2)
  | Match(e, cs) ->
    match_clauses env (eval_env env e) cs

and match_clauses env v cs =
  match cs with
  | [] -> failwith "match failure"
  | (p, e) :: cs ->
    match match_pattern env v p with
    | Some env -> eval_env env e
    | None -> match_clauses env v cs

let eval_prog = eval_env M.empty

let rec string_of_value v =
  match v with
  | VUnit       -> "()"
  | VInt n      -> string_of_int n
  | VBool true  -> "true"
  | VBool false -> "false"
  | VClosure _  -> "<fun>"
  | VPair(v1, v2) ->
    "(" ^ string_of_pair v1 v2 ^ ")"
  | VCtor(c, v) -> string_of_ctor c v 

and string_of_pair v1 v2 = 
  match v1,v2 with
  | VPair(a,b),VPair(c,d) -> string_of_pair a  b ^ ", " ^ string_of_pair c d 
  | VPair(a,b),c -> string_of_pair a b ^ ", " ^ string_of_value c
  | a,VPair(c,d) -> string_of_value a ^ ", " ^ string_of_pair c d
  | a,b -> string_of_value a ^ ", " ^ string_of_value b 
              
and string_of_ctor c v =
  match v with
  | VUnit -> c ^ " ()"
  | VInt n      -> c ^ " " ^ string_of_int n
  | VBool true  -> c ^ " true"
  | VBool false -> c ^ " false"
  | VClosure _  -> c ^ " <fun>"
  | VPair(v1,v2) -> c ^ " (" ^ string_of_pair v1 v2 ^ ")"
  | VCtor(c',v') -> c ^ " (" ^ string_of_ctor c' v' ^ ")"

let print_value v =
  print_endline (string_of_value v)
