-- Day 10's tests: the examples from the puzzle and unit tests. Kept apart
-- from the program, so `stitchwort run Aoc.Year2024.Day10.main` doesn't
-- check them.

namespace Aoc.Year2024.Day10.Tests
import Aoc.Year2024.Day10 (..)
import Aoc.Year2024.Day10.Spec (isHikingTrail, isOrthogonalStep, pathsOf)
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

-- The first small example: one trailhead, reaching one 9.
def smallest: Text := """
  0123
  1234
  8765
  9876
  """

-- One trailhead with a score of 2.
def scoreTwo: Text := """
  ...0...
  ...1...
  ...2...
  6543456
  7.....7
  8.....8
  9.....9
  """

-- One trailhead with a score of 4 and a rating of 13.
def scoreFour: Text := """
  ..90..9
  ...1.98
  ...2..7
  6543456
  765.987
  876....
  987....
  """

-- Two trailheads, with scores of 1 and 2.
def twoTrailheads: Text := """
  10..9..
  2...8..
  3...7..
  4567654
  ...8..3
  ...9..2
  .....01
  """

-- One trailhead with a rating of 3.
def ratingThree: Text := """
  .....0.
  ..4321.
  ..5..2.
  ..6543.
  ..7..4.
  ..8765.
  ..9....
  """

-- One trailhead with a rating of 227.
def ratingLarge: Text := """
  012345
  123456
  234567
  345678
  4.6789
  56789.
  """

def parsed (input: Text): Result TopographicMap Text := Fail.toResult (() => parseMap input)

def topography (input: Text): TopographicMap := Fail.orElse { rows = [] } (() => parseMap input)

def at (row: Nat) (column: Nat): Position := { row, column }

test "example, part 1" := solvePart1 (topography example) == 36
test "example, part 2" := solvePart2 (topography example) == 81

test "example, the trailheads in reading order" :=
  (topography example).trailheads == [at 0 2, at 0 4, at 2 4, at 4 6, at 5 2, at 5 5, at 6 0, at 6 6, at 7 1]

test "example, each trailhead's score" :=
  let map := topography example
  map.trailheads.map map.score == [5, 6, 5, 3, 1, 3, 5, 3, 5]

test "example, each trailhead's rating" :=
  let map := topography example
  map.trailheads.map map.rating == [20, 24, 10, 4, 1, 4, 5, 8, 5]

test "smallest example" := solvePart1 (topography smallest) == 1
test "a score of 2" := solvePart1 (topography scoreTwo) == 2
test "a score of 4" := solvePart1 (topography scoreFour) == 4
test "two trailheads" := (topography twoTrailheads |> .trailheads |> .map (topography twoTrailheads).score) == [1, 2]
test "a rating of 3" := solvePart2 (topography ratingThree) == 3
test "a rating of 13" := solvePart2 (topography scoreFour) == 13
test "a rating of 227" := solvePart2 (topography ratingLarge) == 227 && solvePart1 (topography ratingLarge) == 2

-- The three trails of the rating-3 example, and some paths that aren't
-- trails, by the spec.
test "the spec's trails" :=
  let map := topography ratingThree
  let down := [at 0 5, at 1 5, at 2 5, at 3 5, at 4 5, at 5 5, at 5 4, at 5 3, at 5 2, at 6 2]
  let across := [at 0 5, at 1 5, at 1 4, at 1 3, at 1 2, at 2 2, at 3 2, at 4 2, at 5 2, at 6 2]
  let middle := [at 0 5, at 1 5, at 2 5, at 3 5, at 3 4, at 3 3, at 3 2, at 4 2, at 5 2, at 6 2]
  [down, across, middle].all (isHikingTrail map)
    && !isHikingTrail map (down.take 9)
    && !isHikingTrail map (down.drop 1)
    && !isHikingTrail map []
    && !isHikingTrail map [at 0 5, at 1 5, at 2 5, at 3 5, at 4 5, at 5 5, at 5 4, at 5 3, at 6 2, at 6 2]

test "the spec's steps are orthogonal" :=
  isOrthogonalStep (at 1 1) (at 0 1) && isOrthogonalStep (at 1 1) (at 1 2) && !isOrthogonalStep (at 1 1) (at 2 2) && !isOrthogonalStep (at 1 1) (at 1 1)

test "the spec's paths" :=
  let map := topography "01\n"
  pathsOf map 2 == [[at 0 0, at 0 0], [at 0 0, at 0 1], [at 0 1, at 0 0], [at 0 1, at 0 1]]

test "parse" := parsed "01\n.9\n" == Ok ({ rows = [[Some 0, Some 1], [None, Some 9]] })
test "parse without a final line break" := parsed "01\n23" == Ok ({ rows = [[Some 0, Some 1], [Some 2, Some 3]] })
test "nothing" := parsed "" == Err "line 1, column 1: expected a digit or '.', got the end of the input"
test "a bad tile" := parsed "0123\n12x4\n" == Err "line 2, column 3: expected a digit or '.' or the end of the line, got 'x'"
test "a short row" := parsed "0123\n124\n" == Err "line 2: expected 4 tiles, as on the first line, got 3"

test "neighbours in the corner" := (at 0 0).neighbours == [at 0 1, at 1 0]
test "neighbours on the top row" := (at 0 3).neighbours == [at 0 2, at 0 4, at 1 3]
test "neighbours inside" := (at 2 3).neighbours == [at 1 3, at 2 2, at 2 4, at 3 3]

test "heights off the map" :=
  let map := topography "01\n23\n"
  map.heightAt (at 1 1) == Some 3 && map.heightAt (at 2 0) == None && map.heightAt (at 0 2) == None

test "no trailheads" := solvePart1 (topography "123\n456\n") == 0 && solvePart2 (topography "123\n456\n") == 0
test "one straight trail" := solvePart1 (topography "0123456789\n") == 1 && solvePart2 (topography "0123456789\n") == 1
test "a trail must reach 9" := solvePart1 (topography "012345678\n") == 0 && solvePart2 (topography "012345678\n") == 0
-- Each row climbs its own way, and a trail can switch rows where a 4 meets a
-- 5: each 0 reaches both 9s, by one trail each.
test "trails cross between rows" := solvePart1 (topography "0123456789\n9876543210\n") == 4 && solvePart2 (topography "0123456789\n9876543210\n") == 4

-- A ladder two wide: the one step right can come at any of the nine steps,
-- so one 9 and nine trails.
test "many trails to one 9" :=
  let ladder := "01\n12\n23\n34\n45\n56\n67\n78\n89\n"
  solvePart1 (topography ladder) == 1 && solvePart2 (topography ladder) == 9

-- A trailhead whose 1 leads nowhere.
test "a dead end" := solvePart1 (topography "01.\n...\n") == 0 && (topography "01\n").uphill (at 0 0) == [at 0 1]
