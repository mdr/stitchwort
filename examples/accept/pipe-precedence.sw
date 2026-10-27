-- `|>` binds tighter than comparisons, `in`, `∧`, `∨` and `<->`, and looser
-- than `++`, arithmetic and application. So a comparison after a pipeline
-- compares its result, and a pipe after `∧` takes only its own operand.

import Std (List, Nat)

def inc (n: Nat): Nat := n + 1

-- `xs |> List.sum == 6` is `(xs |> List.sum) == 6`.
test "named function then compare" := [1, 2, 3] |> List.sum == 6
test "pipe then compare" := 4 |> inc == 5

-- `a ∧ xs |> .length == 4` is `a ∧ ((xs |> .length) == 4)`.
def allFour (a: Bool) (xs: List Nat): Bool := a ∧ xs |> .length == 4

test "conjunction then pipe" := allFour True [1, 2, 3, 4] ∧ !allFour False [1, 2, 3, 4]

-- A pipeline on both sides of a comparison.
test "both sides" := [3, 1, 2] |> List.sort == [3, 2, 1] |> List.reverse

-- Piping a comparison needs brackets.
def describe (b: Bool): Text := if b then "yes" else "no"

test "bracketed comparison" := ((1 == 1) |> describe) == "yes"

-- A multi-line pipeline whose last line is a comparison.
test "multi-line" :=
  [1, 2, 3, 4]
    |> List.filter (n => n % 2 == 0)
    |> List.map (* 10)
    |> List.sum == 60

theorem lengthOfPipe (xs: List Nat): xs |> List.length = xs.length := rfl
