-- A let-bound lambda with one parameter, used only through dot notation
-- (`shape.size`), called where the call's type is compared or computed
-- with (SW-2445). The body waits for the parameter's type, which only the
-- call fixes, so the function's result type is an unknown applied to the
-- parameter; the call's type waits for that dot call instead of being
-- reported as a mismatch.

import Std (Nat)

type Shape = | Circle (radius: Nat) | Square (side: Nat)

def Shape.size (shape: Shape): Nat := match shape with
  | Circle r => r
  | Square s => s

test "compared" :=
  let sizeOf := (shape) => shape.size
  sizeOf (Circle 4) == 4

def sizeTwice (shape: Shape): Nat :=
  let sizeOf := (s) => s.size
  sizeOf shape + sizeOf (Square 2)

test "added" := sizeTwice (Circle 3) == 5
