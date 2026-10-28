-- expect-error: E-AUTO-STUCK
-- A power is nonzero when its base is positive; here the base is any
-- number, so neither the power as written nor what it computes to is
-- decided.

import Std (Nat)

def divideByPower (n: Nat) (base: Nat) (k: Nat): Nat := n / Nat.pow base (Succ k)
