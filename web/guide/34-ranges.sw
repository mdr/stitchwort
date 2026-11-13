import Std (Each, List, Nat)
import Std.Each (each, require)

-- `a ..< b` runs up to, not including, `b`; `a ..= b` runs through `b`.
-- A range is an ordinary list of numbers.
test "up to, not including" := 0 ..< 3 == [0, 1, 2]
test "through" := 1 ..= 3 == [1, 2, 3]
test "backwards gives nothing" := 5 ..< 2 == []

-- The end is any expression, and a range goes with `|>`.
def squares (xs: List Text): List Nat := 0 ..< xs.length |> .map (i => i * i)

test "squares" := squares ["a", "b", "c"] == [0, 1, 4]

-- `in` tests membership, and `each` picks one number at a time.
def isIndex (xs: List Text) (i: Nat): Bool := i in 0 ..< xs.length

def pairsSummingTo (n: Nat): List (Nat, Nat) := Each.collect (() =>
  let a := each (1 ..= n)
  let b := each (a ..= n)
  require (a + b == n)
  (a, b))

test "membership" := isIndex ["a", "b"] 1 && !isIndex ["a", "b"] 2
test "pairs" := pairsSummingTo 6 == [(1, 5), (2, 4), (3, 3)]

-- In a spread a range needs no brackets.
test "spread" := [0, ..2 ..< 5, 9] == [0, 2, 3, 4, 9]

-- In a proof, omega reads membership as the two bounds, and `a ..= b` is `a ..< b + 1`.
theorem inRange ∀ (x n: Nat) (h: x < n): x ∈ 0 ..< n := omega

theorem throughIsUpTo ∀ (a b: Nat): a ..= b = a ..< b + 1 := rfl

-- A range of bare dots is an error that says what to write:
-- def bad (n: Nat): List Nat := 1 .. n
