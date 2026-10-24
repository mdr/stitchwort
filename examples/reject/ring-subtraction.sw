-- expect-error: E-RING
-- `ring` knows nothing about truncated subtraction, so `a - b` stays an atom.
import Std (Nat)

theorem subAdd (a: Nat) (b: Nat): (a - b) + b = a := ring
