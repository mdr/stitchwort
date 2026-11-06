-- expect-error: E-AUTO-STUCK
-- A power is nonzero when its base is positive; here the base is any
-- number, so neither the power as written nor what it computes to is
-- decided.

import Std (Nat)

def nonzero (d: Nat) [auto ok: d ≠ 0]: Nat := d

def power (base: Nat) (k: Nat): Nat := nonzero (Nat.pow base (Succ k))
