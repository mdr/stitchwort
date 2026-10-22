-- expect-error: E-OMEGA
-- Products are compared up to swapping two factors only: `(x * y) * z` and
-- `x * (y * z)` are different atoms.
import Std (Nat)

theorem mulAssoc (x: Nat) (y: Nat) (z: Nat): x * y * z = x * (y * z) := omega
