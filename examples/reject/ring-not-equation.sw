-- expect-error: E-RING
-- `ring` proves equations, not inequalities.
import Std (Nat)

theorem le (a: Nat) (b: Nat): a ≤ a + b := ring
