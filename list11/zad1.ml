let exists f xs =
  let exception Found of bool in 
  try
    List.fold_left (fun _ x ->
      if f x then raise (Found true) else false
    ) false xs
  with
  | Found result -> result
