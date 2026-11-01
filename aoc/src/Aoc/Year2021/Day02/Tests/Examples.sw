--| Day 2's tests: the example from the puzzle and unit tests.
-- Kept apart from the program, so `stitchwort run Aoc.Year2021.Day02.main`
-- doesn't check them.

namespace Aoc.Year2021.Day02.Tests
import Aoc.Year2021.Day02 (..)
import Aoc.Year2021.Day02.Spec (..)
import Std (Fail, List, Text)

def example: Text := """
  forward 5
  down 5
  forward 8
  up 3
  down 8
  forward 2
  """

def exampleCommands: List Command := [Forward 5, Down 5, Forward 8, Up 3, Down 8, Forward 2]

def parsed (input: Text): Result (List Command) Text := Fail.toResult (() => parseCommands input)

test "parse the example" := parsed example == Ok exampleCommands
test "example, part 1" := solvePart1 exampleCommands == 150
test "example, part 2" := solvePart2 exampleCommands == 900
test "example, as the puzzle states it" := (part1 exampleCommands, part2 exampleCommands) == (150, 900)

test "an unknown command" := parsed "forward 5\nback 2" == Err "line 2, column 1: expected forward, down or up, got 'b'"
test "no space before the units" := parsed "down5" == Err "line 1, column 5: expected a space, got '5'"
test "no units" := parsed "up " == Err "line 1, column 4: expected a number, got the end of the line"
test "negative units" := parsed "down -3" == Err "line 1, column 6: expected a number, got '-'"
test "spaces around a command" := parsed "  up  3 \n" == Ok [Up 3]
test "no lines" := parsed "" == Ok []

test "no commands, no movement" := (solvePart1 [], solvePart2 []) == (0, 0)
test "up past the surface goes above it" := (solvePart1 [Up 3, Forward 2], part1 [Up 3, Forward 2]) == (-6, -6)
test "forward first moves at aim 0" := solvePart2 [Forward 4, Down 1, Forward 3] == 21

--| The examples, proved by computing them.
theorem examplePart1: solvePart1 exampleCommands = 150 := rfl
theorem examplePart2: solvePart2 exampleCommands = 900 := rfl
