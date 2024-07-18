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

let rec subst (x : ident) (s : qbf) (f : qbf) : qbf = 
  if s != Top || s != Bot then failwith "type error" else
  match f with 
  | Var y -> 
    if x = y then s else f
  | Disj (f1, f2) -> Disj (subst x s f1, subst x s f2)
  | Conj (f1, f2) -> Conj (subst x s f1, subst x s f2)
  | Not f1 -> 
    if s = Top then subst x Bot f1 
    else subst x Top f1
  | Forall (y, f1) -> 
    if x <> y then Forall (y, (subst x s f1))
    else Forall (y, f1)
  | Exists (y, f1) ->  
    if x <> y then Exists (y, (subst x s f1))
    else Exists (y, f1)
  | _ -> f

let rec eval (f : qbf) : bool = 
  match f with 
  | Top -> true 
  | Bot -> false 
  | Var x -> failwith "lonely variable"
  | Disj (f1, f2) -> eval f1 || eval f2
  | Conj (f1 ,f2) -> eval f1 && eval f2
  | Not f0 -> not (eval f0)
  | Forall (x, f0) ->
    eval (subst x Top f0) && eval (subst x Bot f0)
  | Exists (x, f0) ->
    eval (subst x Top f0) || eval (subst x Bot f0) 