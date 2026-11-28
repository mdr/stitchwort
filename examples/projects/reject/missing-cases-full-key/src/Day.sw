-- The file doing the match imports the function and one constructor, not
-- the type: `Shape` has no short name here. The missing case is written with
-- the type's full key, `Outer.Shape.Square`, so that it can be pasted back
-- (SW-2903).
namespace Day

import Outer (make, Circle)

def area (n: Nat): Nat :=
  match make n with
    | Circle r => r * r
