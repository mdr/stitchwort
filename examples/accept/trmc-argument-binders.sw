import Std (List, Nat, Text)

def show (xs: List Nat): Text := Text.join (xs.map Nat.toText) ','

def app (xs: List Nat) (rest: List Nat): List Nat :=
  match xs with
    | [] => rest
    | [y, ..ys] => Cons y (app ys rest)

-- The recursive call's argument binds a variable (a `let` from an inlined
-- function) that the loop built from `++` must not take as a parameter.
def step (acc: Nat) (x: List Nat): Nat :=
  let n := acc * 2 + x.length
  n + n

def flatten: List (List Nat) → Nat → List Nat
  | [], acc => [acc]
  | [xs, ..xss], acc => xs ++ flatten xss (step acc xs)

-- The same with a lambda applied in place.
def catL: List (List Nat) → List Nat → List Nat
  | [], acc => acc
  | [xs, ..xss], acc => app xs (catL xss (((z: List Nat) => Cons z.length z) (app xs acc)))

def main(): {IO} () :=
  IO.print (show (flatten [[1, 2], [], [3]] 1))
  IO.print (show (catL [[1, 2], [], [3]] [9]))
