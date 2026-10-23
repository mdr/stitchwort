-- `Float` extracted to JS (docs/proposals/float.md §5): a `number` at the
-- boundary and inside generated code. Every `number` is accepted, `NaN`, the
-- infinities and `-0` included.
--
-- run: identity 80281.87
-- run: identity (-0.0)
-- run: identity Float.nan
-- run: identity (makeInfinity ())
-- run: shift 80281.87 (-1000)
-- run: shift 0.1 0.2
-- run: sameDouble 0.0 (-0.0)
-- run: tripleEquals 0.0 (-0.0)
-- run: sameDouble Float.nan Float.nan
-- run: tripleEquals Float.nan Float.nan
-- run: bits (-0.0)
-- run: bits (Float.infinity - Float.infinity)
-- run: fromBits 4611686018427387904
-- run: firstOf [1.5, -2.5]
-- run: firstOf []
-- run: magnitudes [-1.5, 0.0, -0.0, Float.nan]

import Std (Float, List, Option)

export def identity (x: Float): Float := x

export def makeInfinity (): Float := Float.infinity

export def shift (t: Float) (by: Float): Float := t + by

export def sameDouble (x: Float) (y: Float): Bool := x == y

export def tripleEquals (x: Float) (y: Float): Bool := Float.ieeeEq x y

export def bits (x: Float): Nat := x.bits

-- The record's constructor, with bits known only at run time.
export def fromBits (b: Nat): Option Float :=
  if h: Float.isValid b = True then Some ({ bits = b, valid = h }) else None

export def firstOf: List Float -> Option Float
  | Nil => None
  | Cons x xs => Some x

export def magnitudes (xs: List Float): List Float := List.map Float.abs xs
