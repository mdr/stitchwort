-- A `match` inside a `Partial` function: it is lifted to a helper like any
-- other nested `match`.
--
--   $ stitchwort run examples/accept/partial-match.sw
--   found 4 from 2

import Std (Nat)

-- The first number, counting up from `start`, whose predecessor-or-one is 3.
def search (start: Nat): {Partial} Nat :=
  let predecessor := match start with
    | 0 => 1
    | Succ before => before
  if predecessor == 3 then start else search (start + 1)

def main(): {IO, Partial} () := IO.print ("found " ++ Nat.toText (search 2) ++ " from 2")
