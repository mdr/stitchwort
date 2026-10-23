-- expect-error: E-RECORD-UPDATE
-- Updating `n` without the `xs` that depends on it is still rejected: the
-- old `xs` would have the wrong type (SW-386, D1091).

import Std (Nat, Vec)

type Two =
  | A (n: Nat) (xs: Vec Nat n) (m: Nat)
  | B (n: Nat) (xs: Vec Nat n) (m: Nat)

def resize (v: Two): Two := { v | n = 3 }
