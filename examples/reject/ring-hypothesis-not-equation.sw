-- expect-error: E-ALGEBRA
-- A hypothesis given to `algebra [..]` must be an equation too.
import Std (Nat)

theorem withLe (n: Nat) (h: n ≤ 3): n + 0 = n := algebra [h]
