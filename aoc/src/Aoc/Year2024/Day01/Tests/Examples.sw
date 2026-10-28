-- Day 1's tests: the example from the puzzle and unit tests. Kept apart from
-- the program, so `stitchwort run Aoc.Year2024.Day01.main` doesn't check them.

namespace Aoc.Year2024.Day01.Tests
import Aoc.Year2024.Day01 (..)
import Std (Fail, List, Text)

def example: Text := """
  3   4
  4   3
  2   5
  1   3
  3   9
  3   3
  """

def exampleLists: LocationLists := Fail.orElse { left = [], right = [] } (() => parseLocationLists example)

def parsed (input: Text): Result LocationLists Text := Fail.toResult (() => parseLocationLists input)

test "example, part 1" := solvePart1 exampleLists == 11
test "example, part 2" := solvePart2 exampleLists == 31
test "parse the example" := exampleLists == { left = [3, 4, 2, 1, 3, 3], right = [4, 3, 5, 3, 9, 3] }
test "a line with one id" := parsed "3   4\n5" == Err "line 2, column 2: expected a number"
test "a line with three ids" := parsed "3 4 5" == Err "line 1, column 5: expected the end"
test "a line that isn't numbers" := parsed "3   x" == Err "line 1, column 5: expected a number"
test "no lines" := parsed "" == Ok ({ left = [], right = [] })
test "an id missing from the right list scores 0" := solvePart2 { left = [7], right = [1, 2] } == 0
test "a repeated left id scores each time" := solvePart2 { left = [2, 2], right = [2, 2, 2] } == 12
test "lists of different lengths pair the shorter" := solvePart1 { left = [5, 1], right = [2] } == 1
