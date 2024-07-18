(*zadanie 1*)
let fold_left f a xs =
  let rec it xs acc =
    match xs with
    | [] -> acc
    | x :: xs' -> it xs' (f acc x)
  in it xs a

let product xs = 
  if xs = [] then 0 else
    let rec it_mult xs acc = 
      match xs with
      | [] -> acc
      | x::xs' -> it_mult xs' (acc*x)
    in it_mult xs 1

(*zadanie 2*)
(*compose sqaure inc 5 -> 
   compose square (5+1) -> 
    compose square 6 -> 
      compose 36 -> 36*)
(*compose inc square 5 -> 
   compose inc 25 -> 
    compose 26 -> 26*)

(*zadanie 3*)
let build_list n f = 
  let rec it i acc =
    if i<0 then acc 
    else it (i-1) ((f i)::acc)
  in it (n-1) [];; 

let negatives n = build_list n (fun x -> -1*(x+1))

let reciprocals n = build_list n (fun x -> 1./.float_of_int(x+1))

let evens n = build_list n (fun x -> 2*(x+1))
    
let identityM n = build_list n (fun x -> build_list n (fun i -> if i=x then 1 else 0))

(*zadanie 4*)

type 'a set = 'a -> bool

let empty_set : 'a set = fun _ -> false

let singleton (a : 'a) : 'a set = fun x -> x = a

let in_set (a : 'a) (s : 'a set) : bool = s a

let union (s : 'a set) (t : 'a set) : 'a set = fun x -> s x || t x 

let intersect (s : 'a set) (t : 'a set) : 'a set = fun x -> s x && t x 

(*zadanie 5*)
type int_tree = Leaf | Node of int_tree * int * int_tree

let t = Node ( Node ( Leaf , 2 , Leaf ) , 5 , Node (Node ( Leaf , 6 , Leaf ) , 8 ,  Node ( Leaf , 9 , Leaf )))

let rec insert_bst (tree : int_tree) (x : int) : int_tree =
  match tree with 
  | Leaf -> Node (Leaf, x, Leaf)
  | Node (l, v, r) -> 
    if x < v then Node ((insert_bst l x), v, r) 
    else Node (l, v, (insert_bst r x)) 
  
(*zadanie 6*)
let rec fold_tree f a t =
  match t with
  | Leaf -> a
  | Node (l, v, r) -> f (fold_tree f a l) v (fold_tree f a r)

let tree_product t = fold_tree (fun l v r -> l*v*r) 1 t

let tree_flip t = fold_tree (fun l v r -> Node(r,v,l)) Leaf t 

let tree_height t = fold_tree (fun l v r -> 1 + max l r) 0 t

let tree_span t = match t with 
| Leaf -> failwith "Empty tree"
| Node (left, value, right) -> 
  (fold_tree (fun l v r -> min v l) value left, fold_tree (fun l v r -> max v r) value right)

let preorder t = fold_tree (fun l v r -> [v] @ l @ r) [] t

(*zadanie 7*)
let rec flat_append t xs = 
  match t with 
  | Leaf -> xs 
  | Node (l, v, r) -> 
    flat_append l (v :: flat_append r xs)

let flatten t = flat_append t []

(*zadanie 8*)
let rec insert_bst (tree : int_tree) (x : int) : int_tree =
  match tree with 
  | Leaf -> Node (Leaf, x, Leaf)
  | Node (l, v, r) -> 
    if x < v then Node ((insert_bst l x), v, r) 
    else Node (l, v, (insert_bst r x)) 

let create_tree xs =
  let rec help xs acc = 
  match xs with 
  | [] -> acc
  | x::xs' -> help xs' (insert_bst acc x)
  in help xs Leaf 

let tree_sort xs = flatten (create_tree xs)

(*zadanie 9*)
let rec find_min t = 
  match t with 
  | Leaf -> failwith "Empty tree!"
  | Node (Leaf, v, _) -> v 
  | Node (l, v, _) -> find_min l
  
let rec delete tree x = 
  match tree with 
  | Leaf -> Leaf 
  | Node (l, v, r) -> 
    if x < v then Node ((delete l x), v, r ) 
    else if x > v then Node (l, v, (delete r x))
    else match (l, r) with 
    | (Leaf, _) -> r
    | (_, Leaf) -> l 
    | (_, _) -> 
      let min_right = find_min r in 
      Node (l, min_right, delete r min_right)

