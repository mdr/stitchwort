-- expect-error: E-RING
-- A power with a variable exponent is an atom, so `10 ^ (k + 1)` is not `10 * 10 ^ k`.
import Std (Nat)

theorem powVar (k: Nat) (b: Nat): Nat.pow 10 (k + 1) * b = 10 * b * Nat.pow 10 k := ring
