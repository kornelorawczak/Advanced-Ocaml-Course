let all_subexprs expr = 
  let rec helper (bound : ident list) (e : expr) (acc) = 
    match e with
    | Int _ | Bool _ | Var _ -> acc
    | Binop (_, e1, e2) -> helper bound e1 (helper bound e2 ((e, bound) :: acc))
    | If (cond, e1, e2) -> helper bound cond (helper bound e1 (helper bound e2 ((e, bound) :: acc)))
    | Let (v, e1, e2) -> helper bound e1 (helper (v :: bound) e2 ((e, bound) :: acc))
in helper [] expr [] 


let free_variables (e : expr) (bound_initial : ident list)=
  let rec iter (e : expr) (bound : ident list) (free : ident list) = 
    match e with 
    | Int _ | Bool _ -> free 
    | Binop (op, e1, e2) -> (iter e1 bound free) @ (iter e2 bound free)
    | If (e1, e2, e3) -> (iter e1 bound free) @ (iter e2 bound free) @ (iter e3 bound free)
    | Var x -> if List.mem x bound = true then free else x :: free
    | Let (y, e1, e2) -> iter e2 (y :: bound) free 
  in List.sort_uniq String.compare (iter e bound_initial [])


  let all_subexprs (e : expr) : expr list = 
    let rec iter (e : expr) (vars : expr list) (acc : expr list) =
      match e with
      | Int _ | Bool _ | Var _ -> acc
      | Binop (_, e1, e2) ->  
        let new_acc_e1 = if check_expr e1 vars then e1 :: acc else acc in  
        let new_acc_e2 = if check_expr e2 vars then e2 :: acc else acc in      
        iter e1 vars new_acc_e1 @ iter e2 vars new_acc_e2
      | If (p, t, e) -> 
        let new_acc_p = if check_expr p vars then p :: acc else acc in
        let new_acc_t = if check_expr t vars then t :: acc else acc in
        let new_acc_e = if check_expr e vars then e :: acc else acc in
        iter p vars new_acc_p @ iter t vars new_acc_t @ iter e vars new_acc_e
      | Let (x, e1, e2) -> 
        let new_vars = (Var x :: vars) in 
        let new_acc_e1 = if check_expr e1 new_vars then e1 :: acc else acc in  
        let new_acc_e2 = if check_expr e2 new_vars then e2 :: acc else acc in      
        iter e1 new_vars new_acc_e1 @ iter e2 new_vars new_acc_e2
    in iter e [] [] 
  