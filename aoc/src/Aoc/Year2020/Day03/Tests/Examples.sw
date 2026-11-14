--| Day 3's tests: the example from the puzzle and unit tests.
--
-- Kept apart from the program, so `stitchwort run Aoc.Year2020.Day03.main`
-- doesn't check them.

namespace Aoc.Year2020.Day03.Tests
import Aoc.Common (Grid)
import Aoc.Year2020.Day03 (..)
import Std (Fail, List, Result, Text)

def example: Text := """
  ..##.......
  #...#...#..
  .#....#..#.
  ..#.#...#.#
  .#...##..#.
  ..#.##.....
  .#.#.#....#
  .#........#
  #.##...#...
  #...##....#
  .#..#...#.#
  """

def exampleMap: Result (Grid Square) Text := parsed example

def parsed (input: Text): Result (Grid Square) Text := Fail.toResult (() => parseMap input)

test "example" := exampleMap.map (map => (solvePart1 map, solvePart2 map)) == Ok (7, 336)
test "example, slope by slope" := exampleMap.map (map => slopes.map (treesOn map)) == Ok [2, 7, 3, 4, 2]
test "a map parsed" := parsed """
  .#
  #.""" == Ok (Grid.of [[Open, Tree], [Tree, Open]])
test "an unknown square" :=
  parsed "..\n.O" == Err "line 2, column 2: expected '.' or '#' or the end of the line, got 'O'"
test "a ragged map" := parsed "..\n." == Err "line 2: expected 2 cells, as on the first line, got 1"

test "the start isn't counted" := treesOn (Grid.of [[Tree], [Open]]) { right = 0, down = 1 } == 0
test "the map repeats to the right" :=
  treesOn (Grid.of [[Open, Open], [Open, Tree], [Tree, Open]]) { right = 3, down = 1 } == 2
test "down 2 skips a row" := treesOn (Grid.of [[Open], [Tree], [Tree], [Open], [Tree]]) { right = 0, down = 2 } == 2
test "a step past the bottom ends it" := treesOn (Grid.of [[Open], [Tree]]) { right = 0, down = 2 } == 0
test "a map with no columns isn't read" := parsed "" == Err "expected a grid, got no cells"
