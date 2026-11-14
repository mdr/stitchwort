-- A written annotation on a let-bound lambda that is applied, in a
-- comparison that waits, beside a lambda the comparison's term annotates
-- itself (`sizeAt`, SW-2439) and a pipe: the written one stays in the
-- term, so this definition's hash says it is kept.

import Std (Nat)

type Shape = | Circle (radius: Nat) | Square (side: Nat)

def Shape.size (shape: Shape): Nat := match shape with
  | Circle r => r
  | Square s => s

test "annotated use" :=
  let sizeAt := ((index, shape)) => index + shape.size
  let double := x => x * 2
  (double: Nat -> Nat) 3 + sizeAt (1, Circle 4) + (2 |> double) == 15
