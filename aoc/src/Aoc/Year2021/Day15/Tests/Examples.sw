--| Day 15's tests: the example from the puzzle and unit tests.
-- Kept apart from the program, so
-- `stitchwort run Aoc.Year2021.Day15.main` doesn't check them.

namespace Aoc.Year2021.Day15.Tests
import Aoc.Year2021.Day15 (..)
import Aoc.Year2021.Day15.Spec (..)
import Aoc.Common (Grid, Position, firstWidth)
import Aoc.Common.Proofs (route)
import Std (Fail, Fin, List, Nat, Option, Text)

def exampleText: Text := """
  1163751742
  1381373672
  2136511328
  3694931569
  7463417111
  1319128137
  1359912421
  3125421639
  1293138521
  2311944581
  """

def parsed (input: Text): Result Cave Text := Fail.toResult (() => parseCave input)

--| A cave of these levels, row by row; the first row has a digit.
def caveOf (rows: List (List (Fin 10))) [auto nonEmpty: (firstWidth rows == 0) = False]: Cave := { grid = Grid.of rows }

def example: Cave := Fail.orElse (caveOf [[0]]) (() => parseCave exampleText)

def at (row column: Nat): Position := { row, column }

test "parse the example" :=
  example.height == 10 ∧ example.width == 10 ∧ levelAt example (at 0 0) == Some 1 ∧ levelAt example (at 9 9) == Some 1
test "a short row" := parsed "123\n45\n" == Err "line 2: expected 3 cells, as on the first line, got 2"
test "no digits" := parsed "" == Err "expected a grid, got no cells"
test "a letter" := parsed "123\n4x6\n" == Err "line 2, column 2: expected a digit or the end of the line, got 'x'"

test "example, part 1" := solvePart1 example == 40
test "example, part 2" := solvePart2 example == 315

--| The program's map has the spec's levels, on and off the example.
def agreeOn (cave: Cave) (rows columns: Nat): Bool :=
  List.range 0 rows
    |> .all (row =>
      List.range 0 columns |> .all (column => levelAt cave (at row column) == cave.risks.levelAt (at row column)))

def tiledAgreeOn (cave: Cave) (rows columns: Nat): Bool :=
  List.range 0 rows
    |> .all (row =>
      List.range 0 columns |> .all (column => tiledLevelAt cave (at row column) == cave.tiled.levelAt (at row column)))

test "the example's levels" := parsed exampleText |> .map (cave => agreeOn cave 12 12) == Ok True
test "the full example's levels" := parsed exampleText |> .map (cave => tiledAgreeOn cave 52 52) == Ok True

--| The puzzle's own illustration: a single 8, tiled, raises to 9, then
--| wraps to 1, 2 and 3 along the top row; the bottom right tile is 8 + 8,
--| wrapped to 7.
test "a single 8, tiled" :=
  [0, 1, 2, 3, 4].map (column => tiledLevelAt (caveOf [[8]]) (at 0 column)) == [Some 8, Some 9, Some 1, Some 2, Some 3]
    ∧ tiledLevelAt (caveOf [[8]]) (at 4 4) == Some 7
    ∧ tiledLevelAt (caveOf [[8]]) (at 5 0) == None
--| The full example's first row, from the puzzle.
test "the full example's first row" :=
  (List.range 0 50 |> .map (column => tiledLevelAt example (at 0 column) |> .getOrElse 0))
    == [1, 1, 6, 3, 7, 5, 1, 7, 4, 2, 2, 2, 7, 4, 8, 6, 2, 8, 5, 3, 3, 3, 8, 5, 9, 7, 3, 9, 6, 4, 4, 4, 9, 6, 1, 8, 4,
      1, 7, 5, 5, 5, 1, 7, 2, 9, 5, 2, 8, 6]

--| Paths and their total risk, in the spec's terms.
test "along the top, then down" :=
  isPath (levelAt example) topLeft (route 10 10) (bottomRight 10 10) ∧ totalRisk (levelAt example) (route 10 10) == 75
test "a diagonal step isn't a path" := not (isPath (levelAt example) topLeft [at 1 1] (at 1 1))
test "a step off the map isn't a path" := not (isPath (levelAt (caveOf [[1]])) topLeft [at 0 1] (at 0 1))

test "one position" := solvePart1 (caveOf [[5]]) == 0 ∧ solvePart2 (caveOf [[5]]) == 6 + 7 + 8 + 9 + 1 + 2 + 3 + 4
test "zeros cost nothing" := solvePart1 (caveOf [[0, 0], [0, 0]]) == 0
test "a cheaper path round a wall" := solvePart1 (caveOf [[1, 9, 1, 1], [1, 9, 1, 1], [1, 1, 1, 1]]) == 5
