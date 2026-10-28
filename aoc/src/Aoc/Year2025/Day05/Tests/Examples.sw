-- Day 5's tests: the example from the puzzle and unit tests. Kept apart from
-- the program, so `stitchwort run Aoc.Year2025.Day05.main` doesn't check them.

namespace Aoc.Year2025.Day05.Tests
import Aoc.Year2025.Day05 (..)
import Std (Fail, List, Text)

def example: Text := """
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
  """

def parsed (input: Text): Result Database Text := Fail.toResult (() => parseDatabase input)

def exampleDatabase: Database := Fail.orElse emptyDatabase (() => parseDatabase example)

test "example parse" := exampleDatabase.available == [1, 5, 8, 11, 17, 32]

test "example part 1" := solvePart1 exampleDatabase == 3

test "example part 2" := solvePart2 exampleDatabase == 14
test "no ranges" := solvePart2 { fresh = [], available = [] } == 0

test "example merged" := merge exampleDatabase.fresh == [{ from = 3, to = 5 }, { from = 10, to = 20 }]
test "touching ranges merge" := merge [{ from = 4, to = 6 }, { from = 1, to = 3 }] == [{ from = 1, to = 6 }]
test "nested range" := merge [{ from = 1, to = 9 }, { from = 2, to = 3 }] == [{ from = 1, to = 9 }]
test "gap stays" := merge [{ from = 1, to = 2 }, { from = 4, to = 5 }] == [{ from = 1, to = 2 }, { from = 4, to = 5 }]
test "same start, shorter second range" := merge [{ from = 1, to = 9 }, { from = 1, to = 3 }] == [{ from = 1, to = 9 }]
test "duplicate range" := solvePart2 { fresh = [{ from = 2, to = 4 }, { from = 2, to = 4 }], available = [] } == 3
test "singleton range" := merge [{ from = 5, to = 5 }] == [{ from = 5, to = 5 }]

test "a line that is neither a range nor an id" := parsed "3-5\nx-7\n\n1\n" == Err "line 2, column 1: expected a number or a blank line, got 'x'"
test "a bad id" := parsed "3-5\n\n1\ntwo\n" == Err "line 4, column 1: expected a number or the end of the input, got 't'"
test "no blank line" := parsed "3-5\n4-6\n" == Err "line 3, column 1: expected a number or a blank line, got the end of the input"
test "a backwards range" := parsed "5-3\n\n1\n" == Err "line 1, column 4: the range 5-3 ends before it starts"
test "spaces around numbers" := parsed " 3 - 5 \n\n 4 \n" == Ok ({ fresh = [{ from = 3, to = 5 }], available = [4] })
