-- Day 5's tests: the example from the puzzle and unit tests. Kept apart from
-- the program, so `stitchwort run Aoc.Day05.main` doesn't check them.

namespace Aoc.Day05.Tests
import Aoc.Day05 (..)
import Std (Fail, List, Text)

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

def parsed (lines: List Text): Result Database Text := Fail.toResult (() => parseDatabase lines)

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

test "a line that is neither a range nor an id" := parsed ["3-5", "x-7", "", "1"] == Err "line 2: expected a range like 11-22, got 'x-7'"
test "a bad id" := parsed ["3-5", "", "1", "two"] == Err "line 4: expected a whole number, got 'two'"
test "no blank line" := parsed ["3-5", "4-6"] == Err "expected a blank line between the ranges and the ids, got none"
test "spaces around lines" := parsed [" 3 - 5 ", " ", " 4 "] == Ok { fresh = [{ from = 3, to = 5 }], available = [4] }
