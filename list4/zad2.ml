(*zadanie 2*)
module type DICT = sig
  type key (*Typ kluczy*) 
  type 'a dict (*słownik otypowany typem wartości*)
  val empty : 'a dict
  val insert : key -> 'a -> 'a dict -> 'a dict 
  (*Za argumenty podajemy klucz wartość i słownik i zwracany jest słownik z dodaną parą*)
  val remove : key -> 'a dict -> 'a dict
  val find_opt : key -> 'a dict -> 'a option
  val find : key -> 'a dict -> 'a
  val to_list : 'a dict -> (key * 'a) list
end

(*zadanie 3*)
module MakeListDict (M : Map.OrderedType) : DICT with type key = M.t = struct
  (*with type key = M.t ustala typ klucza w sygnaturze DICT, potem do klucza w tym module też przypisujemy M.t co zapewnia spójność typów*)
  type key = M.t
  type 'a dict = (key * 'a) list
  let empty = []
  let remove k d = List.filter (fun (k', _) -> (M.compare k k')!=0) d
  let insert k v d = (k, v) :: remove k d
  let find_opt k d = List.find_opt (fun (k', _) -> (M.compare k k')=0) d |> Option.map snd
  let find k d = List.find (fun (k', _) -> (M.compare k k')=0) d |> snd
  let to_list d = d
end

module CharListDict = MakeListDict (struct 
  type t = char 
  let compare = Char.compare 
end)



(*zadnie 4*)
(*przekazujemy do konstruktora modułu typ ordered (np. char) i potem do niego się odnosimy jako M*)
module MakeMapDict (M : Map.OrderedType) : DICT with type key = M.t = struct
  module MapDict = Map.Make(M)
  type key = M.t
  type 'a dict = 'a MapDict.t
  
  let empty = MapDict.empty
  
  let remove k d = MapDict.remove k d

  let insert k v d = MapDict.add k v d

  let find_opt k d = MapDict.find_opt k d

  let find k d = MapDict.find k d

  let to_list d = MapDict.bindings d
end

module CharMapDict = MakeMapDict(Char)