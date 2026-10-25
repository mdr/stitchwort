-- expect-error: E-TYPE-MISMATCH
-- A parameter left out is a variable of the function the call makes, never
-- inferred from the arguments (docs/proposals/named-arguments.md §4.2 rule
-- 5): `use (xs := three)` must work for every `n`, so it doesn't check,
-- and the note says how to give `n`.

import Std (Vec)

def use (n: Nat) (xs: Vec Nat n): Nat := n

def three: Vec Nat 3 := Vec.replicate 3 0

def used: (n: Nat) → Nat := use (xs := three)
