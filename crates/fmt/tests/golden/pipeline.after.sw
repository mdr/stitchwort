-- R13: a `|>` that starts a line goes at +2 from the expression's first line.
def a (xs: List Nat): Nat :=
  xs
    |> List.sort
    |> List.map (x => x * 2)

def b (xs: List Nat): Nat :=
  xs
    |> List.sort
    |> List.sum

def c (xs: List Nat): Nat :=
  let ys := xs
    |> List.sort
  List.sum ys

def d (n: Nat): Nat :=
  match n with
    | 0 => 1
    | _ => n
  |> k => k + 10
