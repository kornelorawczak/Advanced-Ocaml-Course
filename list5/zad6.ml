type 'v nnf =
| NNFLit of bool * 'v
| NNFConj of 'v nnf * 'v nnf
| NNFDisj of 'v nnf * 'v nnf

type 'v formula =
| Var of 'v
| Neg of 'v formula
| Conj of 'v formula * 'v formula
| Disj of 'v formula * 'v formula

let rec to_nnf (formula : 'v formula) = match formula with
| Var v -> Var v 
| Conj (f1, f2) -> Conj(to_nnf f1, to_nnf f2)
| Disj (f1, f2) -> Disj(to_nnf f1, to_nnf f2)
| Neg formula' -> match formula' with 
  | Var v -> Neg (Var v)
  | Neg formula'' -> to_nnf formula''
  | Conj (f1, f2) -> to_nnf (Disj (Neg f1, Neg f2))
  | Disj (f1, f2) -> to_nnf (Conj (Neg f1, Neg f2))

let rec to_nnf (formula : 'v formula) = 
  let rec help formula sigma = 
    match formula with 
    | Var v -> NNFLit(sigma, v)
    | Neg f -> help f (not sigma)
    | Conj(f1, f2) -> if sigma = true then NNFConj(help f1 true, help f2 true) else 
      NNFDisj(help f1 false, help f2 false)
    | Disj(f1, f2) -> if sigma = true then NNFDisj(help f1 true, help f2 true) else 
      NNFConj(help f1 false, help f2 false)
    in help formula false 


let rec eval_formula (sigma : bool) (f : 'v formula) = match f with 
| Var v -> sigma 
| Neg f1 -> not (eval_formula  sigma f1)
| Conj (f1, f2) -> (eval_formula sigma f1) && (eval_formula sigma f2)
| Disj (f1, f2) -> (eval_formula sigma f1) || (eval_formula sigma f2)

let rec is_sorted (xs : int list) = match xs with 
  | [] -> true
  | x::[] -> true  
  | x::x'::xs' -> if x > x' then false else is_sorted (x'::xs')

let insert (x : int) (xs : int list) = 
  let rec it (x : int) (xs : int list) (acc : int list) = match xs with 
  | [] -> acc @ [x] 
  | x'::xs' -> if x < x' then (acc @ [x]) @ (xs) else it x xs' (acc @ [x'])
in it x xs [] 