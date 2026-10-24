-- expect-error: E-TYPE-MISMATCH
-- Leaving a field out commits to its default: `size` isn't inferred from
-- `cells`, so `cells` must be a `Vec Bool 0`
-- (docs/proposals/named-arguments.md §5.1 rule 3).

import Std (Vec)

type Sized = {
  size: Nat := 0,
  cells: Vec Bool size
}

def threeCells: Vec Bool 3 := Vec.replicate 3 False

def made: Sized := { cells = threeCells }
