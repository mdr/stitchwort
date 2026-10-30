-- E-CANNOT-INFER, for review-brief.md: `.x` is looked up in the namespace
-- of the value's type, and where `g` is bound nothing says what `p`'s
-- type is; only the use below would (30 Oct 2026).
--
--   $ stitchwort check docs/proposals/postponement/brief-cannot-infer.sw

import Std (Nat)

type Point = { x: Nat, y: Nat }

def getX: Nat :=
  let g := p => p.x
  g { x = 1, y = 2 }
