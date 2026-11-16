-- expect-error: E-ALGEBRA
-- `algebra` proves equations, not inequalities.
import Std (Nat)

theorem le (a: Nat) (b: Nat): a ≤ a + b := algebra
