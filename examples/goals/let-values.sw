-- A `let`-bound name is shown with its value.
import List (sum)

def average (xs: List Nat): Nat :=
  let total := sum xs
  let count := xs.length
  ?
