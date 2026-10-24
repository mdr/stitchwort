-- expect-error: E-RING
-- A hypothesis that does not close the gap: the message says it was used.
import Std (Nat)

theorem tooFew (n: Nat) (p: Nat) (h: p + p = n): p + p + p = n + n := ring [h]
