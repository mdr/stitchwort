-- expect-error: E-AUTO-STUCK
-- Dividing needs `three n != 0`. With a transparent `three` that is `n + 3
-- != 0`, which holds for every `n`; `three` is opaque here, so its body
-- isn't used and the divisor is unknown.
-- (docs/proposals/opaque-definitions.md §6.10.)
import Std (Nat)

opaque def three (n: Nat): Nat := n + 3

def ratio (n: Nat): Nat := n / three n
