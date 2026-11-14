--| Day 9's tests: the example from the puzzle and unit tests.
-- Kept apart from the program, so `stitchwort run Aoc.Year2021.Day09.main`
-- doesn't check them.

namespace Aoc.Year2021.Day09.Tests
import Aoc.Year2021.Day09 (..)
import Aoc.Year2021.Day09.Spec (..)
import Aoc.Common (Grid, Position, adjacent, firstWidth)
import Std (Fail, Fin, Graph, List, Map, Text)

def exampleText: Text := """
  2199943210
  3987894921
  9856789892
  8767896789
  9899965678
  """

def parsed (input: Text): Result HeightMap Text := Fail.toResult (() => parseHeightMap input)

--| A map of these heights, row by row; the first row has a location.
def heightsOf (rows: List (List (Fin 10))) [auto nonEmpty: (firstWidth rows == 0) = False]: HeightMap :=
  { grid = Grid.of rows }

def example: HeightMap := Fail.orElse (heightsOf [[0]]) (() => parseHeightMap exampleText)

def at (row column: Nat): Position := { row, column }

test "parse the example" := example.grid.rows.length == 5 ∧ example.grid.rows.all (row => row.length == 10)
test "heights" :=
  example.heightAt (at 0 0) == Some 2 ∧ example.heightAt (at 4 9) == Some 8 ∧ example.heightAt (at 5 0) == None
test "a short row" := parsed "123\n45\n" == Err "line 2: expected 3 cells, as on the first line, got 2"
test "a letter" := parsed "123\n4x6\n" == Err "line 2, column 2: expected a digit or the end of the line, got 'x'"

test "the example's low points" :=
  example.lowPoints == [(at 0 1, 1), (at 0 9, 0), (at 2 2, 5), (at 4 6, 5)] ∧ lowPoints example == example.lowPoints
test "example, part 1" := solvePart1 example == 15 ∧ part1 example == 15
test "the example's basins" := example.basinSizes == [3, 9, 14, 9]
test "example, part 2" := solvePart2 example == 1134

test "neighbours in a corner" := (at 0 0).neighbours == [at 0 1, at 1 0]
test "neighbours inside" := (at 2 3).neighbours == [at 1 3, at 2 4, at 3 3, at 2 2]
test "adjacent" :=
  adjacent (at 2 3) (at 1 3)
    ∧ adjacent (at 2 3) (at 2 4)
    ∧ not (adjacent (at 2 3) (at 3 4))
    ∧ not (adjacent (at 2 3) (at 2 3))
test "a path in the example's top left basin" :=
  isPath example (at 0 1) [at 0 0, at 1 0] (at 1 0) ∧ not (isPath example (at 0 1) [at 1 1] (at 1 1))

test "a map of one 9" := solvePart1 (heightsOf [[9]]) == 10 ∧ solvePart2 (heightsOf [[9]]) == 0
test "a flat map has no low points" := solvePart1 (heightsOf [[5, 5], [5, 5]]) == 0
test "fewer than three basins" := solvePart2 (heightsOf [[1, 9, 0, 1]]) == 2

--| The locations each basin has, by the flood fill.
def basinLocations (map: HeightMap): List (List Position) :=
  let graph := map.graph
  map.lowPoints.map (((low, _)) => (graph.breadthFirst [low]).keys)

--| The puzzle's promise (`EachInOneBasin`), as far as a test can say it:
--| the basins have every location that isn't a 9 between them (no
--| location is in none), and their sizes add up to the number of those
--| locations (none is in two).
def eachInOneBasin (map: HeightMap): Bool :=
  let open := map.cells.filterMap (match some | (at, _) if map.isOpen at => at)
  let found := basinLocations map |> .concat
  open.all (location => found.contains location) ∧ found.length == open.length

test "the example keeps the promise" := parsed exampleText |> .map eachInOneBasin == Ok True
test "two low points in one area break it" := not (eachInOneBasin (heightsOf [[0, 1, 0]]))
