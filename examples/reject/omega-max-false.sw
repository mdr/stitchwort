-- expect-error: E-OMEGA
-- `Nat.max a b <= a` is false when `a < b`; the message names the atom as `Nat.max a b`.
import Std (Nat)

theorem maxLe (a: Nat) (b: Nat): Nat.max a b ≤ a := omega
