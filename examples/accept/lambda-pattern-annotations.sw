-- A pattern parameter may have a written type: `((a, b): T) => e`. The
-- pattern is checked against the type, which gives dot notation the type of
-- the variables it binds.

import List (map)
import Std (List, Nat)

type Person = { name: Text, age: Nat }

type Shape =
  | Circle (radius: Nat)
  | Square (side: Nat)

def Shape.size (shape: Shape): Nat :=
  match shape with
    | Circle r => r
    | Square s => s

-- A tuple pattern; `shape.size` needs the type.
test "tuple" :=
  let sizeAt := ((index, shape): (Nat, Shape)) => index + shape.size
  sizeAt (1, Circle 4) == 5

-- A record pattern.
test "record" :=
  let ageDoubled := ({ age, .. }: Person) => age * 2
  ageDoubled { name = "Ada", age = 36 } == 72

-- A nested pattern.
test "nested" :=
  let total := ((a, (b, shape)): (Nat, (Nat, Shape))) => a + b + shape.size
  total (1, (2, Square 3)) == 6

-- Mixed with other parameters.
test "mixed" :=
  let f := x ((a, b): (Nat, Nat)) (y: Nat) => x + a + b + y
  f 1 (2, 3) 4 == 10

-- As an argument.
test "argument" :=
  [(0, Circle 1), (1, Square 2)].map (((i, s): (Nat, Shape)) => i + s.size) == [1, 3]
