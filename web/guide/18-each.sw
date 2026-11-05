-- `Each` is a ready-made ability for "try every combination", the way a
-- nested loop or a list comprehension would. `each` picks one element of a
-- list and `require` drops the combinations that don't fit.
import Std (Each, List)
import Std.Each (each, require)

def pairsSummingTo (n: Nat): List (Nat, Nat) := Each.collect (() =>
  let a := each (List.between 1 n)
  let b := each (List.between a n)
  require (a + b == n)
  (a, b))

test "pairs" := pairsSummingTo 5 == [(1, 4), (2, 3)]
