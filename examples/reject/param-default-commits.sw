-- expect-error: E-TYPE-MISMATCH
-- Leaving a parameter out commits to its default before the arguments are
-- checked: `two` doesn't fit `Vec Nat 3`, and the note says why
-- (docs/proposals/signature-defaults.md §6.1, §6.5).

import Std (Vec)

def sized (n: Nat := 3) (xs: Vec Nat n): Nat := n

def two: Vec Nat 2 := Vec.replicate 2 0

def size: Nat := sized two
