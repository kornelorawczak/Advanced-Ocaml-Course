type 'a symbol =
  | T of string
  | N of 'a

type 'a grammar = ('a * ('a symbol list) list) list

let generate (grammar : 'a grammar) (start : 'a) : string = 
  let rec evaluate_production prod = 
    match prod with 
    | [] -> []
    | sym :: rest -> 
      match sym with  
      | T terminal -> terminal :: evaluate_production rest
      | N non_terminal -> 
        let possible_productions = List.assoc non_terminal grammar in 
        let rand_production = List.nth possible_productions (Random.int (List.length possible_productions)) in 
        (evaluate_production rand_production) @ (evaluate_production rest)
  in
  let start_productions = List.assoc start grammar in 
  let rand_start_production = List.nth start_productions (Random.int (List.length start_productions)) in
  String.concat "" (evaluate_production rand_start_production) 

let expr : unit grammar =
  [(), [[N (); T "+"; N ()];
        [N (); T "*"; N ()];
        [T "("; N (); T ")"];
        [T "1"];
        [T "2"]]]

let pol : string grammar =
[ " zdanie " , [[ N " grupa - podmiotu " ; N " grupa - orzeczenia " ]]
; " grupa - podmiotu " , [[ N " przydawka " ; N " podmiot " ]]
; " grupa - orzeczenia " , [[ N " orzeczenie " ; N " dopelnienie " ]]
; " przydawka " , [[ T " Piekny " ];
[ T " Bogaty " ];
[ T " Wesoly " ]]
; " podmiot " , [[ T " policjant " ];
[ T " student " ];
[ T " piekarz " ]]
; " orzeczenie " , [[ T " zjadl " ];
[ T " pokochal " ];
[ T " zobaczyl " ]]
; " dopelnienie " , [[ T " zupe . " ];
[ T " studentke . " ];
[ T " sam siebie . " ];
[ T " instytut informatyki . " ]]
]