--| Tests for the shared Game of Life step.

namespace Aoc.Common.Tests
import Aoc.Common (..)
import Std (Bool, Int, List, Nat, Set)

-- A line of cells where a cell is alive next with exactly one live neighbour.
def lineCells (x: Int): List Int := [x - 1, x + 1]
def oneNeighbour (alive: Bool) (count: Nat): Bool := count == 1

test "lifeStep on a line grows from one cell" := (lifeStep lineCells oneNeighbour [0].toSet).toList == [-1, 1]
test "lifeStep on a line, two generations" :=
  (lifeStep lineCells oneNeighbour (lifeStep lineCells oneNeighbour [0].toSet)).toList == [-2, 2]
test "lifeStep of no cells is none" := (lifeStep lineCells oneNeighbour (Set.empty: Set Int)).toList == []
test "lifeCounts counts every hit" := (lifeCounts lineCells [0, 2].toSet).toList == [(-1, 1), (1, 2), (3, 1)]

-- Day 24's tiles on a hexagonal grid (axial coordinates): black stays with
-- one or two black neighbours, white turns black with exactly two.
def hexCells (tile: (Int, Int)): List (Int, Int) :=
  let (q, r) := tile
  [(q + 1, r), (q - 1, r), (q, r + 1), (q, r - 1), (q + 1, r - 1), (q - 1, r + 1)]
def tileRule (black: Bool) (count: Nat): Bool := if black then count == 1 || count == 2 else count == 2

test "lifeStep on hexagons: two neighbouring black tiles" :=
  (lifeStep hexCells tileRule [(0, 0), (1, 0)].toSet).toList == [(0, 0), (0, 1), (1, -1), (1, 0)]
test "lifeStep on hexagons: a lone black tile turns white" := (lifeStep hexCells tileRule [(0, 0)].toSet).toList == []
