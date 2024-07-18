type loop = {
  n : int;
  m : int;
  body : unit -> i : int -> unit;
}

type definite_integral = {
  a : float;
  b : float;
  f : float -> float;
}