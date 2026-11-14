-- A let-bound lambda whose body waits (`shape.size`, on a parameter whose
-- type only the call fixes), called where a comparison also waits for the
-- call's type (SW-2439). The comparison's term stands in for its
-- placeholder with `sizeAt` replaced by its value, which is annotated with
-- its type: the kernel infers no type for a bare lambda applied to an
-- argument.

import Std (Nat)

type Shape = | Circle (radius: Nat) | Square (side: Nat)

def Shape.size (shape: Shape): Nat := match shape with
  | Circle r => r
  | Square s => s

test "tuple" :=
  let sizeAt := ((index, shape)) => index + shape.size
  sizeAt (1, Circle 4) == 5

def sizesMatch (n: Nat): Bool :=
  let sizeAt := ((index, shape)) => index + shape.size
  sizeAt (n, Square 2) == n + 2

test "applied in a definition" := sizesMatch 3
