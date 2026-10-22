-- Day 5's tests: the example from the puzzle and unit tests. Kept apart from
-- the program, so `stitchwort run Aoc.Day05.main` doesn't check them.

namespace Aoc.Day05.Tests
import Aoc.Day05 (..)
import Std (List, Text)

def example: List Text := """
  3-5
  10-14
  16-20
  12-18

  1
  5
  8
  11
  17
  32
  """.lines

test "example parse" := (parseDatabase example).available == [1, 5, 8, 11, 17, 32]

test "example part 1" := solvePart1 (parseDatabase example) == 3

test "example part 2" := solvePart2 (parseDatabase example) == 14
test "no ranges" := solvePart2 { fresh = [], available = [] } == 0

test "example merged" := merge (parseDatabase example).fresh == [{ from = 3, to = 5 }, { from = 10, to = 20 }]
test "touching ranges merge" := merge [{ from = 4, to = 6 }, { from = 1, to = 3 }] == [{ from = 1, to = 6 }]
test "nested range" := merge [{ from = 1, to = 9 }, { from = 2, to = 3 }] == [{ from = 1, to = 9 }]
test "gap stays" := merge [{ from = 1, to = 2 }, { from = 4, to = 5 }] == [{ from = 1, to = 2 }, { from = 4, to = 5 }]
test "same start, shorter second range" := merge [{ from = 1, to = 9 }, { from = 1, to = 3 }] == [{ from = 1, to = 9 }]
test "duplicate range" := solvePart2 { fresh = [{ from = 2, to = 4 }, { from = 2, to = 4 }], available = [] } == 3
test "singleton range" := merge [{ from = 5, to = 5 }] == [{ from = 5, to = 5 }]
