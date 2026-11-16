-- expect-error: E-ALGEBRA
-- `algebra` knows nothing about truncated subtraction, so `a - b` stays an atom.
import Std (Nat)

theorem subAdd (a: Nat) (b: Nat): (a - b) + b = a := algebra
