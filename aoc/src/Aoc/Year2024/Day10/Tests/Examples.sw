--| Day 10's tests: the examples from the puzzle and unit tests.
--
-- Kept apart from the program, so
-- `stitchwort run Aoc.Year2024.Day10.main` doesn't check them.

namespace Aoc.Year2024.Day10.Tests
import Aoc.Year2024.Day10 (..)
import Aoc.Year2024.Day10.Spec (isHikingTrail, isStep, pathsOf)
import Aoc.Common (Grid, Position)
import Std (Fail, List, Nat, Option, Result, Text)

def example: Text := """
  89010123
  78121874
  87430965
  96549874
  45678903
  32019012
  01329801
  10456732
  """

--| The first small example: one trailhead, reaching one 9.
def smallest: Text := """
  0123
  1234
  8765
  9876
  """

--| One trailhead with a score of 2.
def scoreTwo: Text := """
  ...0...
  ...1...
  ...2...
  6543456
  7.....7
  8.....8
  9.....9
  """

--| One trailhead with a score of 4 and a rating of 13.
def scoreFour: Text := """
  ..90..9
  ...1.98
  ...2..7
  6543456
  765.987
  876....
  987....
  """

--| Two trailheads, with scores of 1 and 2.
def twoTrailheads: Text := """
  10..9..
  2...8..
  3...7..
  4567654
  ...8..3
  ...9..2
  .....01
  """

--| One trailhead with a rating of 3.
def ratingThree: Text := """
  .....0.
  ..4321.
  ..5..2.
  ..6543.
  ..7..4.
  ..8765.
  ..9....
  """

--| One trailhead with a rating of 227.
def ratingLarge: Text := """
  012345
  123456
  234567
  345678
  4.6789
  56789.
  """

def parsed (input: Text): Result TopographicMap Text := Fail.toResult (() => parseMap input)

--| A function of the parsed map, or why it didn't parse: a parse failure fails the test.
def onMap (input: Text) (f: TopographicMap -> a): Result a Text := parsed input |> .map f

def at (row column: Nat): Position := { row, column }

test "example, part 1" := onMap example solvePart1 == Ok 36
test "example, part 2" := onMap example solvePart2 == Ok 81

test "example, the trailheads in reading order" :=
  onMap example (map => map.trailheads) == Ok [at 0 2, at 0 4, at 2 4, at 4 6, at 5 2, at 5 5, at 6 0, at 6 6, at 7 1]

test "example, each trailhead's score" :=
  onMap example (map => map.trailheads.map map.score) == Ok [5, 6, 5, 3, 1, 3, 5, 3, 5]

test "example, each trailhead's rating" :=
  onMap example (map => map.trailheads.map map.rating) == Ok [20, 24, 10, 4, 1, 4, 5, 8, 5]

test "smallest example" := onMap smallest solvePart1 == Ok 1
test "a score of 2" := onMap scoreTwo solvePart1 == Ok 2
test "a score of 4" := onMap scoreFour solvePart1 == Ok 4
test "two trailheads" := onMap twoTrailheads (map => map.trailheads.map map.score) == Ok [1, 2]
test "a rating of 3" := onMap ratingThree solvePart2 == Ok 3
test "a rating of 13" := onMap scoreFour solvePart2 == Ok 13
test "a rating of 227" := onMap ratingLarge solvePart2 == Ok 227 && onMap ratingLarge solvePart1 == Ok 2

--| The three trails of the rating-3 example, and some paths that aren't
--| trails, by the spec.
test "the spec's trails" :=
  let down := [at 0 5, at 1 5, at 2 5, at 3 5, at 4 5, at 5 5, at 5 4, at 5 3, at 5 2, at 6 2]
  let across := [at 0 5, at 1 5, at 1 4, at 1 3, at 1 2, at 2 2, at 3 2, at 4 2, at 5 2, at 6 2]
  let middle := [at 0 5, at 1 5, at 2 5, at 3 5, at 3 4, at 3 3, at 3 2, at 4 2, at 5 2, at 6 2]
  onMap ratingThree (map =>
    [down, across, middle].all (isHikingTrail map)
      && !isHikingTrail map (down.take 9)
      && !isHikingTrail map (down.drop 1)
      && !isHikingTrail map []
      && !isHikingTrail map [at 0 5, at 1 5, at 2 5, at 3 5, at 4 5, at 5 5, at 5 4, at 5 3, at 6 2, at 6 2])
    == Ok True

--| Up, down, left or right, and one higher: not diagonally, and not on the
--| spot.
test "the spec's steps" := onMap """
  012
  123
  234
  """ (map =>
  isStep map (at 1 1) (at 1 2)
    && isStep map (at 1 1) (at 2 1)
    && !isStep map (at 1 1) (at 0 1)
    && !isStep map (at 1 1) (at 2 2)
    && !isStep map (at 1 1) (at 1 1))
  == Ok True

test "the spec's paths" :=
  onMap "01\n" (map => pathsOf map 2) == Ok [[at 0 0, at 0 0], [at 0 0, at 0 1], [at 0 1, at 0 0], [at 0 1, at 0 1]]

test "parse" := parsed """
  01
  .9
  """ == Ok { grid = Grid.of [[Some 0, Some 1], [None, Some 9]] }
test "parse without a final line break" := parsed "01\n23" == Ok { grid = Grid.of [[Some 0, Some 1], [Some 2, Some 3]] }
test "nothing" := parsed "" == Err "expected a grid, got no cells"
test "a bad tile" :=
  parsed "0123\n12x4\n" == Err "line 2, column 3: expected a digit, '.' or the end of the line, got 'x'"
test "a short row" := parsed "0123\n124\n" == Err "line 2: expected 4 cells, as on the first line, got 3"

test "heights off the map" := onMap """
  01
  23
  """ (map => (map.heightAt (at 1 1), map.heightAt (at 2 0), map.heightAt (at 0 2))) == Ok (Some 3, None, None)

test "no trailheads" := onMap """
  123
  456
  """ solvePart1 == Ok 0 && onMap """
  123
  456
  """ solvePart2 == Ok 0
test "one straight trail" := onMap "0123456789\n" solvePart1 == Ok 1 && onMap "0123456789\n" solvePart2 == Ok 1
test "a trail must reach 9" := onMap "012345678\n" solvePart1 == Ok 0 && onMap "012345678\n" solvePart2 == Ok 0
--| Each row climbs its own way, and a trail can switch rows where a 4 meets a
--| 5: each 0 reaches both 9s, by one trail each.
test "trails cross between rows" := onMap """
  0123456789
  9876543210
  """ solvePart1 == Ok 4 && onMap """
  0123456789
  9876543210
  """ solvePart2 == Ok 4

--| A ladder two wide: the one step right can come at any of the nine steps,
--| so one 9 and nine trails.
test "many trails to one 9" := onMap """
  01
  12
  23
  34
  45
  56
  67
  78
  89
  """ solvePart1 == Ok 1 && onMap """
  01
  12
  23
  34
  45
  56
  67
  78
  89
  """ solvePart2 == Ok 9

--| A trailhead whose 1 leads nowhere.
test "a dead end" := onMap """
  01.
  ...
  """ solvePart1 == Ok 0 && onMap "01\n" (map => map.uphill (at 0 0)) == Ok [at 0 1]
