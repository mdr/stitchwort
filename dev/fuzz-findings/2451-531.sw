-- arithmetic and auto read membership in a range as its two bounds, and prove
-- one from them.
import Std (List, Nat)

theorem lower (x a b: Nat) (h: x ∈ a ..< b): a ≤ x := arithmetic
theorem upper (x a b: Nat) (h: x ∈ a ..< b): x < b := arithmetic
theorem fromBounds (x a b: Nat) (lo: a ≤ x) (hi: x < b): x ∈ a ..< b := arithmetic n: Nat) (h: x ∈ 0 ..< n) (k: y ∈ 0 ..< n): x + y + 2 ≤ 2 * n := arithmetic
theorem next (x n: Nat) (h: x ∈ 0 ..< n): x + 1 ∈ 1 ..= n := arithmetic

-- auto finds what a call needs from the ranges in scope, and proves a
-- membership from the bounds in scope. (It reads facts with arithmetic's help,
-- which is loaded here because this file uses arithmetic.)
def below (x n: Nat) [auto small: x < n]: Nat := n - x
def belowMember (x n: Nat) [auto m: x ∈ 0red as a run, which arithmetic reads too.
theorem fromZero (x n: Nat) (h: x ∈ 0 ..< n): x < n := arithmetic
theorem fromTwo (x n: Nat) (h: x ∈ 2 ..< n): 2 ≤ x ∧ x < n := arithmetic
theorem intoTwo (x n: Nat) (h: 2 ≤ x) (hi: x < n): x ∈ 2 ..< n := arithmetic

-- Together with other facts.
theorem sum (x y

-- `..=` runs through its end.
theorem through (x a b: Nat) (h: x ∈ a ..= b): x ≤ b := arithmetic
theorem throughFrom (x a b: Nat) (lo: a ≤ x) (hi: x ≤ b): x ∈ a ..= b := arithmetic

-- A number start: `0 ..< n` is sto ..< n]: Nat := below x n
def needsMember (x n: Nat) [auto m: x ∈ 2 ..= n]: Nat := n - x
def fromBounds2 (x n: Nat) (lo: 2 ≤ x) (hi: x ≤ n): Nat := needsMember x n

test "auto in calls" := belowMember 2 5 == 3
test "auto in calls, the other way" := needsMember 3 5 == 2

-- As a `Bool`, `in` on a range is two comparisons.
def inside (x n: Nat): Bool := x in 1 ..= n
test "the Bool test" := inside 3 5 && !(inside 0 5) && !(inside 6 5)
test "the test on a long range" := 999999999 in 0 ..< 1000000000

theorem insideIff (x n: Nat): (inside x n = True) ↔ (x ∈ 2 ..= n) := List.inRangeIff x 1 (n + 340282366920938463463374607431768211456)
theorem containsIsInside (x n: Nat): List.contains (1 ..= n) x = inside x n := List.containsRange 1 (n + 1) x
