-- expect-error: E-RING
-- A hypothesis given to `ring [..]` must be an equation too.
import Std (Nat)

theorem withLe (n: Nat) (h: n <= 3): n + 0 = n := ring [h]
