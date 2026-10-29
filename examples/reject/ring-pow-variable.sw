-- expect-error: E-RING
-- A power with a variable exponent is an atom, so `10 ^ (k + j)` is not `10 ^ k * 10 ^ j`.
import Std (Nat)

theorem powVar (k: Nat) (j: Nat) (b: Nat): Nat.pow 10 (k + j) * b = Nat.pow 10 k * b * Nat.pow 10 j := ring
