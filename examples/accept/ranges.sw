-- Ranges: `a ..< b` runs up to, not including, `b`; `a ..= b` runs through
-- `b`. A range is an ordinary `List Nat`, so everything lists do works on it.
import Std (List, Nat, Pair, Each)
import Std.Each (each, require)

def squares (n: Nat): List Nat := 0 ..< n |> .map (i => i * i)

test "up to, not including" := 0 ..< 3 == [0, 1, 2]
test "through" := 1 ..= 3 == [1, 2, 3]
test "backwards ends give nothing" := 5 ..< 2 == []
test "a single number" := 4 ..= 4 == [4]
test "squares" := squares 4 == [0, 1, 4, 9]
test "the end can be an expression" := 0 ..< [7, 8, 9].length == [0, 1, 2]
test "sums" := 1 ..= 100 |> .sum == 5050

-- `in` binds more loosely than a range.
test "membership" := 3 in 0 ..< 5 && !(5 in 0 ..< 5) && 5 in 0 ..= 5

-- A range in a spread needs no brackets.
test "spread" := [0, ..2 ..< 5, 9] == [0, 2, 3, 4, 9]

-- `each` over a range chooses one number at a time.
def pairsSummingTo (n: Nat): List (Pair Nat Nat) := Each.collect (() =>
  let a := each (1 ..= n)
  let b := each (a ..= n)
  require (a + b == n)
  (a, b))

test "pairs" := pairsSummingTo 6 == [(1, 5), (2, 4), (3, 3)]

-- Membership is the two bounds.
theorem inRange ∀ (x n: Nat) (h: x < n): x ∈ 0 ..< n := (List.memRange x 0 n).backward omega

theorem bounds ∀ (x a b: Nat) (h: x ∈ a ..< b): a ≤ x < b := (List.memRange x a b).forward h

-- `a ..= b` is `a ..< b + 1`: the same term.
theorem throughIsUpTo ∀ (a b: Nat): a ..= b = a ..< b + 1 := rfl
