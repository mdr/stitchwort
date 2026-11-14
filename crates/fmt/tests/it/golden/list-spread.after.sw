def front (xs: List Nat): List Nat := [1, ..xs]
def both (xs ys: List Nat): List Nat := [..xs, ..ys]
def mixed (xs ys: List Nat): List Nat := [1, ..xs, 2, ..f ys]
def joined (xs ys: List Nat): List Nat := [0, ..xs ++ ys]
def swap: List Nat → List Nat
  | [a, b, ..rest] => [b, a, ..rest]
  | other => other
