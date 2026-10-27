-- Day 2's tests: the example from the puzzle and unit tests. Kept apart from
-- the program, so `stitchwort run Aoc.Year2024.Day02.main` doesn't check them.

namespace Aoc.Year2024.Day02.Tests
import Aoc.Year2024.Day02 (..)
import Std (Fail, List, Text)

def example: List Text := """
  7 6 4 2 1
  1 2 7 8 9
  9 7 6 2 1
  1 3 2 4 5
  8 6 4 4 1
  1 3 6 7 9
  """.lines

def exampleReports: List Report := Fail.orElse [] (() => parseReports example)

def parsed (lines: List Text): Result (List Report) Text := Fail.toResult (() => parseReports lines)

def safe (levels: List Nat): Bool := isSafe { levels }

def safeWithDampener (levels: List Nat): Bool := isSafeWithDampener { levels }

test "example, part 1" := solvePart1 exampleReports == 2
test "example, part 2" := solvePart2 exampleReports == 4
test "each example report, part 1" := exampleReports.map isSafe == [True, False, False, False, False, True]
test "each example report, part 2" := exampleReports.map isSafeWithDampener == [True, False, False, True, True, True]
test "parse a report" := parsed ["7 6 4 2 1"] == Ok [{ levels = [7, 6, 4, 2, 1] }]
test "parse extra spaces" := parsed ["  1   3 "] == Ok [{ levels = [1, 3] }]
test "a level that isn't a number" := parsed ["1 2", "1 x 3"] == Err "line 2: expected a whole number, got 'x'"
test "an empty line" := parsed ["1 2", ""] == Err "line 2: expected levels like '7 6 4 2 1', got an empty line"
test "no lines" := parsed [] == Ok []
test "one level is safe" := safe [5]
test "two equal levels are unsafe" := !(safe [5, 5])
test "a rise of three is safe" := safe [1, 4]
test "a rise of four is unsafe" := !(safe [1, 5])
test "a fall of three is safe" := safe [4, 1]
test "a fall of four is unsafe" := !(safe [5, 1])
test "rising then falling is unsafe" := !(safe [1, 2, 1])
test "falling from zero" := safe [3, 2, 1, 0]
test "removing the first level" := safeWithDampener [9, 1, 2, 3]
test "removing the last level" := safeWithDampener [1, 2, 3, 9]
test "removing a level in the middle" := safeWithDampener [1, 2, 9, 3]
test "two bad levels are too many" := !(safeWithDampener [1, 9, 2, 9, 3])
test "removing a level can fix the direction" := safeWithDampener [5, 6, 4, 3]
test "removeAt" := [1, 2, 3].removeAt 1 == [1, 3]
test "removeAt past the end" := [1, 2, 3].removeAt 3 == [1, 2, 3]
