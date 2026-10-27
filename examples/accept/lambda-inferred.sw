-- A lambda with no expected type and no annotations, such as one bound by
-- `let`: its parameters' types come from its patterns, its body, or how it
-- is used afterwards.

import Std (List)

def roll (sides: Nat): Nat := sides + 1

-- `()` fixes the parameter's type: `Unit`.
test "unit parameter" :=
  let later := () => roll 4
  later () == 5

-- The use fixes `x`'s type.
test "fixed by the use" :=
  let step := x => x + 1
  step 2 == 3

-- The body fixes `n`'s type.
test "fixed by the body" :=
  let twice := n => roll n + roll n
  twice 1 == 4

-- Several parameters, and a pair pattern.
test "several parameters" :=
  let add := x y => x + y
  let sum := (a, b) => a + b
  add 2 3 == 5 ∧ sum (4, 5) == 9

-- Used more than once, at the same types.
test "used twice" :=
  let wrap := x => [x]
  wrap 1 ++ wrap 2 == [1, 2]

-- Passed on to a function that takes a function.
test "passed on" :=
  let double := x => x * 2
  ([1, 2, 3] |> List.map double) == [2, 4, 6]
