

(* e0 - Some
 (Let ("v", Binop (Add, Var "x", Var "y"),
   If (Binop (Gt, Var "v", Int 0), Var "v", Int 0))) *)
let e0 =
  If (Binop (Gt, Binop (Add, Var "x", Var "y"), Int 0),Binop (Add, Var "x", Var "y"),Int 0)

(* e1 - Some
 (Let ("v", Binop (Mult, Int 2, Var "x"),
   Binop (Add, Var "v", Binop (Add, Int 1, Var "v")))) *)
let e1 =
  Binop(Add, 
    Binop (Mult, Int 2, Var "x"),
    Binop (Add, Int 1, Binop (Mult, Int 2, Var "x")))

(* None *)
let e2 =
  Binop (Add,
    Binop (Mult, Var "x", Int 10),
    Let ("x", Int 3,
         Binop (Mult, Var "x", Int 10)))

(*(Let ("v2", Binop (Add, Var "x", Var "y"), Binop (Add, Var "v2", Var "v2")))*)
let e3 =
  Binop (Add,
    Binop(Add, Var "x", Var "y"),
    Binop(Add, Var "x", Var "y"))

(*przyklad alfa rownowaznosc
   (Let ("v3", Let ("x", Int 1, Binop (Add, Var "x", Var "z")),
   Binop (Add, Var "v3", Binop (Mult, Int 10, Var "v3"))))*)
let e4 =
  Binop (Add, Let ("x", Int 1, Binop (Add, Var "x", Var "z")),Binop (Mult,Int 10,Let ("y", Int 1, Binop (Add, Var "y", Var "z"))))

(*przyklad koniec zadania*)
(*(Let ("v4", Binop (Mult, Var "z", Int 10),
   If (Var "x", Binop (Add, Var "v4", Var "v4"), Int 0)))*)
let e5 = 
  If (
    Var "x",
    Binop (
      Add,
      Binop (Mult, Var "z", Int 10),
      Binop (Mult, Var "z", Int 10)
    ),
    Int 0
  )

(*przyklad 3 te same wyrazenia
(Let ("v5", Binop (Add, Var "x", Var "y"), If (Var "v5", Var "v5", Var "v5")))*)
let e6 =
  If (
    Binop (Add, Var "x", Var "y"),
    Binop (Add, Var "x", Var "y"),
    Binop (Add, Var "x", Var "y")
  )

let e7 = 
  Let ("x", Binop (Mult, Int 3, Int 10),
  Let ("x", Binop (Mult, Binop (Mult, Int 3, Int 10), Int 2),
    Binop (Add, Var "x", Binop (Mult, Int 3, Int 10))))

let e8 = Let("x", Binop(Add, Var "x", Int 10), Binop(Add, Var "x", Int 10))
(* e8 - None *)
let e9 = Let("y", Int 3, Binop(Add, Binop(Mult, Var "y", Int 10), Binop(Mult, Var "y", Int 10)))

(* e9 - NIE POWINNO BYC NONE *)
let e10 = Binop (Add, Binop (Mult,
Binop (Add, Var "x", Int 10),
Binop (Add, Var "x", Int 10)),
Let ("x", Int 1,
Binop (Add, Var "x", Int 10)))



