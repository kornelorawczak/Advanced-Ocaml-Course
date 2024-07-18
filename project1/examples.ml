type nonogram_spec = {rows: int list list ; cols: int list list}
let example_1 = {
  rows = [[2];[1];[1]];
  cols = [[1;1];[2]]
}

let example_2 = {
  rows = [[2];[2;1];[1;1];[2]];
  cols = [[2];[2;1];[1;1];[2]]
}

let big_example = {
  rows = [[1;2];[2];[1];[1];[2];[2;4];[2;6];[8];[1;1];[2;2]];
  cols = [[2];[3];[1];[2;1];[5];[4];[1;4;1];[1;5];[2;2];[2;1]]
}

let example_3 = {
  rows = [[2;3];[1;1;1];[3];[2;2];[5]];
  cols = [[2;2];[1;3];[3;1];[1;3];[2;2]]
}

let example_4 = {
  rows = [[1]];
  cols = [[1]]
}

let example_5 = {
  rows = [[1];[1]];
  cols = [[1];[1]]
}

let example_6 = {
  rows = [[1];[];[1]];
  cols = [[1];[];[1]]
}

let example_7 = {
  rows = [[1];[1]];
  cols = [[];[1];[1]]
}


