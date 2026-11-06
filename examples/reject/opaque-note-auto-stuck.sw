-- expect-error: E-AUTO-STUCK
-- `nonzero` needs `three n != 0`. With a transparent `three` that is `n + 3
-- != 0`, which holds for every `n`; `three` is opaque here, so its body
-- isn't used and the number is unknown.
-- (docs/proposals/opaque-definitions.md §6.10.)
import Std (Nat)

opaque def three (n: Nat): Nat := n + 3

def nonzero (d: Nat) [auto ok: d ≠ 0]: Nat := d

def ratio (n: Nat): Nat := nonzero (three n)
