-- Goals print `List.range a b` as `a ..< b`, and `List.range a (b + 1)` as
-- `a ..= b`. Either way it is the same term, so `0 ..< n + 1` written by hand
-- is shown as `0 ..= n`.
import Std (List, Nat)

theorem lengthThrough ∀ (n: Nat): (1 ..= n).length = n := ?

theorem lengthUpTo ∀ (n: Nat): (0 ..< n + 1).length = n + 1 := ?

theorem members ∀ (x n: Nat): x ∈ 2 ..< n := ?

theorem pairs ∀ (n: Nat): 1 ..= n = 1 ..< n + 1 := ?
