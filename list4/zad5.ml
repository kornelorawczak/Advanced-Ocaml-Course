module LeftistHeap = struct
  type ('a , 'b ) heap =
  | HLeaf
  | HNode of int * ('a , 'b ) heap * 'a * 'b * ('a , 'b ) heap
  let rank = function HLeaf -> 0 | HNode (n , _ , _ , _ , _ ) -> n
  let heap_ordered p = function
  | HLeaf -> true
  | HNode (_ , _ , p', _ , _ ) -> p <= p'
  let rec is_valid = function
  | HLeaf -> true
  | HNode (n , l , p , v , r ) ->
  rank r <= rank l
  && rank r + 1 = n
  && heap_ordered p l
  && heap_ordered p r
  && is_valid l
  && is_valid r
  let make_node p v l r = 
    let nl = rank l in 
    let nr = rank r in 
    if nl >= nr then 
      HNode (nr + 1, l, p, v, r) 
    else
      HNode(nl + 1, r, p, v, l)
  let rec heap_merge a b = 
    match a, b with 
    | a, HLeaf -> a
    | HLeaf, b -> b 
    | HNode (n1, l1, p1, v1, r1), HNode(n2, l2, p2, v2, r2) -> 
      if p1 <= p2 then make_node p1 v1 (heap_merge r1 b) l1
      else make_node p2 v2 (heap_merge r2 a) l2
  end


module type PRIO_QUEUE = sig
  type ('a, 'b) pq
  
  val empty : ('a, 'b) pq
  val insert : 'a -> 'b -> ('a, 'b) pq -> ('a, 'b) pq
  val pop : ('a, 'b) pq -> ('a, 'b) pq
  val min_with_prio : ('a, 'b) pq -> 'a * 'b
end

module ListPrioQueue : PRIO_QUEUE = struct
  type ('a, 'b) pq = ('a * 'b) list

  let empty = []
  let rec insert a x q = match q with
  | [] -> [a, x]
  | (b, y) :: ys -> if a < b then (a, x) :: q else (b, y) :: insert a x ys
  let pop q = List.tl q
  let min_with_prio q = List.hd q
end

module LeftistHeapPrioQueue : PRIO_QUEUE = struct
  type ('a , 'b ) pq = ('a, 'b) LeftistHeap.heap

  let empty = LeftistHeap.HLeaf
  let rec insert p v h= 
    LeftistHeap.heap_merge h (LeftistHeap.make_node p v LeftistHeap.HLeaf LeftistHeap.HLeaf)
  let pop = function 
  | LeftistHeap.HLeaf -> LeftistHeap.HLeaf
  | LeftistHeap.HNode (n, l, p, v, r) -> LeftistHeap.heap_merge l r
  let min_with_prio = function
    | LeftistHeap.HLeaf -> failwith "Empty queue"
    | LeftistHeap.HNode (_, _, p, v, _) -> (p, v)
end
  
module PqSort (PQ : PRIO_QUEUE) = struct 
  let rec pq_of_list pq = function 
  | [] -> pq 
  | x :: xs' -> pq_of_list (PQ.insert x x pq) xs' 
  let rec list_of_pq q acc = 
    if PQ.empty = q then acc 
    else let (_, min_v) = PQ.min_with_prio q in 
    list_of_pq (PQ.pop q) acc @ min_v
  
  let pqsort xs = list_of_pq ((pq_of_list xs) [])
    
end 

module LeftistHeapSort = PqSort(LeftistHeapPrioQueue);;
module ListSort = PqSort(ListPrioQueue);;