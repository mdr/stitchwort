-- Advent of Code 2021, day 15: a cave mapped as a grid of risk levels, one
-- digit per position. A path moves up, down, left or right, from the top
-- left position to the bottom right one, and its total risk adds up the
-- levels of the positions it enters (not the one it starts on). Part 1
-- asks for the lowest total risk. Part 2 asks the same of the full cave,
-- five times larger each way: the map repeats as tiles, and each tile's
-- levels are the first tile's raised by its distance in tiles from the
-- top left, with levels past 9 wrapping round to 1.
--
--   $ cd aoc && stitchwort run Aoc.Year2021.Day15.main < inputs/2021/day15.txt
--
-- The puzzle input is committed in aoc/inputs/2021/.
--
-- Both parts are std's Dijkstra search (`Graph.distances`) on the graph
-- whose edges step to a neighbouring position, costing that position's
-- level; only the levels differ. The full cave isn't built: a position's
-- level is computed from the first tile's. The proofs that the answers
-- are the lowest total risks, for every input the parser accepts, are in
-- `Aoc.Year2021.Day15.Proofs` (Proofs/), the tests in
-- `Aoc.Year2021.Day15.Tests` (Tests/); `run` checks neither.

namespace Aoc.Year2021.Day15
import Aoc.Year2021.Day09 (Position)
import Std (Bool, Fail, Fin, Graph, IO, List, Map, Nat, Option, Parse, Text)
import Std.Parse (digit, many1)

def main(): {IO, Fail} () :=
  let cave := parseCave IO.readAll()
  IO.print "Part 1: ${solvePart1 cave}"
  IO.print "Part 2: ${solvePart2 cave}"

-- The positions are day 9's (`Aoc.Year2021.Day09.Position`, a row and a
-- column), with its four `neighbours`.

-- The risk levels, row by row: digits, so 0 to 9 by their type.
type Cave = { rows: List (List (Fin 10)) }

-- One row of digits per line, at least one digit, every row as long as
-- the first (the puzzle's map is a rectangle).
def parseCave (input: Text): {Fail} Cave := checkCave (Parse.eachLine input (() => many1 digit))

-- The cave, if it has a digit and every row is as long as the first;
-- otherwise fail, saying why.
def checkCave (rows: List (List (Fin 10))): {Fail} Cave :=
  if width rows == 0 then Fail.fail "expected a map of risk levels, got no digits"
  else
    match firstRagged rows with
      | Some (index, row) => Fail.fail "line ${index + 1}: expected ${width rows} digits, as on the first line, got ${row.length}"
      | None => { rows }

-- The first row's length.
def width (rows: List (List (Fin 10))): Nat := rows.headOr [] |> .length

-- The first row not as long as the first, with its index.
def firstRagged (rows: List (List (Fin 10))): Option (Nat, List (Fin 10)) :=
  rows.withIndex.find (((_, row)) => row.length != width rows)

def Cave.height (cave: Cave): Nat := cave.rows.length

def Cave.width (cave: Cave): Nat := width cave.rows

-- A map of risk levels: `level` gives each position's, for the positions
-- in its `height` rows and `width` columns.
type RiskMap = { height: Nat, width: Nat, level: Position → Nat }

-- The level at `position`; `None` off the map.
def RiskMap.levelAt (risks: RiskMap) (position: Position): Option Nat :=
  if position.row < risks.height && position.column < risks.width then Some (risks.level position) else None

-- A step to each neighbour on the map, costing its level.
def RiskMap.edges (risks: RiskMap) (position: Position): List (Position, Nat) :=
  position.neighbours.filterMap (next => risks.levelAt next |> .map (level => (next, level)))

-- Every position on the map, row by row.
def RiskMap.positions (risks: RiskMap): List Position :=
  List.range risks.height |> .flatMap (row => List.range risks.width |> .map (column => ({ row, column }: Position)))

-- The map as a graph for std's search. Every step leads to a position on
-- the map (`edgesListed`, in Steps.sw).
def RiskMap.graph (risks: RiskMap): Graph Position := {
  edges = risks.edges,
  states = risks.positions,
  listed = position next weight edge => risks.edgesListed position next weight edge
}

def RiskMap.start (risks: RiskMap): Position := { row = 0, column = 0 }

def RiskMap.target (risks: RiskMap): Position := { row = risks.height - 1, column = risks.width - 1 }

-- The lowest total risk from the top left to the bottom right: Dijkstra's
-- search from the top left, starting at 0 (its level isn't counted).
def RiskMap.lowestRisk (risks: RiskMap): Nat := risks.graph.distances [(risks.start, 0)] |> .getOr risks.target 0

-- The levels by row and column, for lookups in O(log n).
def Cave.table (cave: Cave): Map Nat (Map Nat Nat) := cave.rows.map (row => row.map Fin.toNat |> Map.byPosition) |> Map.byPosition

-- The level in row `row`, column `column` of the table; 0 off it.
def lookUp (table: Map Nat (Map Nat Nat)) (row: Nat) (column: Nat): Nat := (table.getOr row Map.empty).getOr column 0

-- The cave's own map.
def Cave.risks (cave: Cave): RiskMap :=
  let table := cave.table
  { height = cave.height, width = cave.width, level = position => lookUp table position.row position.column }

-- A level raised by up to 8, wrapping past 9 round to 1.
def wrap (level: Nat): Nat := if level > 9 then level - 9 else level

-- The full cave, five tiles each way: the tile `position` is in (its row
-- and column divided by the cave's height and width) raises the level at
-- the same place in the first tile (the remainders) by the tile's row
-- plus its column.
def Cave.tiles (cave: Cave) [auto tall: cave.height ≠ 0] [auto wide: cave.width ≠ 0]: RiskMap :=
  let table := cave.table
  let height := cave.height
  let width := cave.width
  {
    height = 5 * height,
    width = 5 * width,
    level = position =>
      let base := lookUp table (position.row % height) (position.column % width)
      wrap (base + (position.row / height + position.column / width))
  }

-- The full cave; a cave with no levels has no tiles.
def Cave.tiled (cave: Cave): RiskMap :=
  if tall: cave.height != 0 then if wide: cave.width != 0 then cave.tiles else cave.risks else cave.risks

def solvePart1 (cave: Cave): Nat := cave.risks.lowestRisk

def solvePart2 (cave: Cave): Nat := cave.tiled.lowestRisk
