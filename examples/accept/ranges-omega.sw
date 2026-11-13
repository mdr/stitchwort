-- omega and auto read membership in a range as its two bounds, and prove
-- one from them.
import Std (List, Nat)

theorem lower ∀ (x a b: Nat) (h: x ∈ a ..< b): a ≤ x := omega
theorem upper ∀ (x a b: Nat) (h: x ∈ a ..< b): x < b := omega
theorem fromBounds ∀ (x a b: Nat) (lo: a ≤ x) (hi: x < b): x ∈ a ..< b := omega

-- `..=` runs through its end.
theorem through ∀ (x a b: Nat) (h: x ∈ a ..= b): x ≤ b := omega
theorem throughFrom ∀ (x a b: Nat) (lo: a ≤ x) (hi: x ≤ b): x ∈ a ..= b := omega

-- A number start: `0 ..< n` is stored as a run, which omega reads too.
theorem fromZero ∀ (x n: Nat) (h: x ∈ 0 ..< n): x < n := omega
theorem fromTwo ∀ (x n: Nat) (h: x ∈ 2 ..< n): 2 ≤ x ∧ x < n := omega
theorem intoTwo ∀ (x n: Nat) (h: 2 ≤ x) (hi: x < n): x ∈ 2 ..< n := omega

-- Together with other facts.
theorem sum ∀ (x y n: Nat) (h: x ∈ 0 ..< n) (k: y ∈ 0 ..< n): x + y + 2 ≤ 2 * n := omega
theorem next ∀ (x n: Nat) (h: x ∈ 0 ..< n): x + 1 ∈ 1 ..= n := omega

-- auto finds what a call needs from the ranges in scope, and proves a
-- membership from the bounds in scope. (It reads facts with omega's help,
-- which is loaded here because this file uses omega.)
def below (x n: Nat) [auto small: x < n]: Nat := n - x
def belowMember (x n: Nat) [auto m: x ∈ 0 ..< n]: Nat := below x n
def needsMember (x n: Nat) [auto m: x ∈ 2 ..= n]: Nat := n - x
def fromBounds2 (x n: Nat) (lo: 2 ≤ x) (hi: x ≤ n): Nat := needsMember x n

test "auto in calls" := belowMember 2 5 == 3
test "auto in calls, the other way" := needsMember 3 5 == 2

-- As a `Bool`, `in` on a range is two comparisons.
def inside (x n: Nat): Bool := x in 1 ..= n
test "the Bool test" := inside 3 5 && !(inside 0 5) && !(inside 6 5)
test "the test on a long range" := 999999999 in 0 ..< 1000000000

theorem insideIff ∀ (x n: Nat): (inside x n = True) ↔ (x ∈ 1 ..= n) := List.inRangeIff x 1 (n + 1)
theorem containsIsInside ∀ (x n: Nat): List.contains (1 ..= n) x = inside x n := List.containsRange 1 (n + 1) x
