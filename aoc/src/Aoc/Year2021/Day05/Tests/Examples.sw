--| Day 5's tests: the example from the puzzle and unit tests.
-- Kept apart from the program, so `stitchwort run Aoc.Year2021.Day05.main`
-- doesn't check them.

namespace Aoc.Year2021.Day05.Tests
import Aoc.Common (..)
import Aoc.Year2021.Day05 (..)
import Aoc.Year2021.Day05.Spec (..)
import Std (Fail, List, Text)

def example: Text := """
  0,9 -> 5,9
  8,0 -> 0,8
  9,4 -> 3,4
  2,2 -> 2,1
  7,0 -> 7,4
  6,4 -> 2,0
  0,9 -> 2,9
  3,4 -> 1,4
  0,0 -> 8,8
  5,5 -> 8,2
  """

def exampleLines: List Line := Fail.orElse [] (() => parseLines example)

def parsed (input: Text): Result (List Line) Text := Fail.toResult (() => parseLines input)

def line (x1 y1 x2 y2: Nat): Line := { from = { x = x1, y = y1 }, to = { x = x2, y = y2 } }
def point (x y: Nat): Point := { x, y }

test "parse the example" := exampleLines.length == 10 ∧ exampleLines.headOr (line 1 1 1 1) == line 0 9 5 9
test "example, part 1" := solvePart1 exampleLines == 5
test "example, part 2" := solvePart2 exampleLines == 12

--| "An entry like 1,1 -> 1,3 covers points 1,1, 1,2, and 1,3", and so on.
test "a vertical line's points" := (line 1 1 1 3).points == [point 1 1, point 1 2, point 1 3]
test "a horizontal line's points" := (line 9 7 7 7).points == [point 9 7, point 8 7, point 7 7]
test "a diagonal line's points" := (line 1 1 3 3).points == [point 1 1, point 2 2, point 3 3]
test "the other diagonal's points" := (line 9 7 7 9).points == [point 9 7, point 8 8, point 7 9]
test "a line of one point" := (line 4 4 4 4).points == [point 4 4]

--| The spec says the same of those lines, point by point, around them.
def around: List Point := List.range 0 11 |> .flatMap (x => List.range 0 11 |> .map (y => point x y))
def agrees (l: Line): Bool := around.all (p => covers l p == l.points.contains p)
test "the spec's points" :=
  [line 1 1 1 3, line 9 7 7 7, line 1 1 3 3, line 9 7 7 9, line 4 4 4 4, line 8 0 0 8, line 5 5 8 2].all agrees
--| A line at another angle: the spec has its grid points, (0, 0), (2, 1)
--| and (4, 2); the program, which steps one point at a time, wouldn't.
test "a line at another angle" :=
  around.filter (covers (line 0 0 4 2)) == [point 0 0, point 2 1, point 4 2]
    ∧ (line 0 0 4 2).points == [point 0 0, point 1 1, point 2 2, point 3 3, point 4 4]

--| The example's overlaps, as the spec counts them: part 1 has 5 points
--| with two lines or more, part 2 has 12.
def overlapsIn (lines: List Line): List Point := around.filter (overlap lines)
test "the spec, part 1" := (overlapsIn (exampleLines.filter horizontalOrVertical)).length == 5
test "the spec, part 2" := (overlapsIn exampleLines).length == 12

test "a line at 30 degrees" := parsed "0,0 -> 4,2\n" == Err "line 1 isn't horizontal, vertical or diagonal"
test "not a number" := parsed "1,x -> 3,4\n" == Err "line 1, column 3: expected a number, got 'x'"
test "no lines" := (solvePart1 [], solvePart2 []) == (0, 0)
--| Two lines over the same stretch overlap at each of its points; three
--| count once.
test "the same stretch" := solvePart1 [line 0 0 3 0, line 1 0 5 0] == 3
test "three over one point" := solvePart2 [line 0 0 2 2, line 2 0 0 2, line 1 0 1 4] == 1
test "a line overlaps itself" := solvePart1 [line 0 0 0 2, line 0 2 0 0] == 3

--| The examples, proved by computing them.
theorem examplePart1: solvePart1 exampleLines = 5 := rfl
theorem examplePart2: solvePart2 exampleLines = 12 := rfl
