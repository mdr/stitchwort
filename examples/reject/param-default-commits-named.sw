-- expect-error: E-TYPE-MISMATCH
-- The same for a named argument, in a call that leaves another required
-- parameter out (docs/proposals/signature-defaults.md §9, invariant 9).

import Std (Vec)

def pair (n: Nat := 3) (xs: Vec Nat n) (ys: Vec Nat n): Nat := n

def two: Vec Nat 2 := Vec.replicate 2 0

def withTwo: Vec Nat 3 -> Nat := pair (ys := two)
