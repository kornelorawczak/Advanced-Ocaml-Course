type ident = string

type qbf =
  | Top (* ⊤ *)
  | Bot (* ⊥ *)
  | Var of ident (* x *)
  | Disj of qbf * qbf (* ∨ *)
  | Conj of qbf * qbf (* ∧ *)
  | Not of qbf (* ¬ *)
  | Forall of ident * qbf (* ∀ *)
  | Exists of ident * qbf (* ∃ *)

module M = Map.Make(String)
type env = bool M.t

let rec eval (env : env) (f : qbf) : bool = 
  match f with 
  | Top -> true 
  | Bot -> false 
  | Var x -> (
    match M.find_opt x env with 
    | Some v -> v 
    | _ -> failwith ("unbound variable" ^ x) )
  | Disj (f1, f2) -> eval env f1 || eval env f2
  | Conj (f1 ,f2) -> eval env f1 && eval env f2
  | Not f0 -> not (eval env f0)
  | Forall (x, f0) ->
    eval (M.add x true env) f0 && eval (M.add x false env) f0
  | Exists (x, f0) ->
    eval (M.add x true env) f0 || eval (M.add x false env) f0