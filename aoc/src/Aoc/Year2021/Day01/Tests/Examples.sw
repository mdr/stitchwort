--| Day 1's tests: the example from the puzzle and unit tests.
-- Kept apart from the program, so `stitchwort run Aoc.Year2021.Day01.main`
-- doesn't check them.

namespace Aoc.Year2021.Day01.Tests
import Aoc.Year2021.Day01 (..)
import Aoc.Year2021.Day01.Spec (..)
import Std (Fail, List, Text)

def example: Text := """
  199
  200
  208
  210
  200
  207
  240
  269
  260
  263
  """

def exampleDepths: List Nat := [199, 200, 208, 210, 200, 207, 240, 269, 260, 263]

def parsed (input: Text): Result (List Nat) Text := Fail.toResult (() => parseDepths input)

test "parse the example" := parsed example == Ok exampleDepths
test "example, part 1" := solvePart1 exampleDepths == 7
test "example, part 2" := solvePart2 exampleDepths == 5
test "example, as the puzzle states it" := (increases exampleDepths, windowIncreases 3 exampleDepths) == (7, 5)
test "the example's windows" := (slidingWindows 3 exampleDepths).map .sum == [607, 618, 618, 617, 647, 716, 769, 792]

test "a line that isn't a depth" := parsed "199\n2x0" == Err "line 2, column 2: expected the end of the line, got 'x'"
test "a blank line" := parsed "199\n\n200" == Err "line 2, column 1: expected a number, got the end of the line"
test "spaces around a depth" := parsed " 199\n200 \n" == Ok [199, 200]
test "a negative depth" := parsed "-1" == Err "line 1, column 1: expected a number, got '-'"
test "no lines" := parsed "" == Ok []

test "equal depths aren't an increase" := solvePart1 [5, 5, 5] == 0
test "fewer than four depths make no window increase" := solvePart2 [1, 2, 3] == 0
test "equal window sums aren't an increase" := solvePart2 [1, 9, 9, 1] == 0

--| The examples, proved by computing them.
theorem examplePart1: solvePart1 exampleDepths = 7 := rfl
theorem examplePart2: solvePart2 exampleDepths = 5 := rfl
