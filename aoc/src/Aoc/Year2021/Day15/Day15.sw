--| Advent of Code 2021, day 15: a cave mapped as a grid of risk levels, one
--| digit per position. A path moves up, down, left or right, from the top
--| left position to the bottom right one, and its total risk adds up the
--| levels of the positions it enters (not the one it starts on). Part 1
--| asks for the lowest total risk. Part 2 asks the same of the full cave,
--| five times larger each way: the map repeats as tiles, and each tile's
--| levels are the first tile's raised by its distance in tiles from the top
--| left, with levels past 9 wrapping round to 1.
--|
--|   $ cd aoc && stitchwort run Aoc.Year2021.Day15.main < inputs/2021/day15.txt
--|
--| The puzzle input is committed in aoc/inputs/2021/.
--|
--| Both parts are std's Dijkstra search (`Graph.distances`) on the graph
--| whose edges step to a neighbouring position, costing that position's
--| level; only the levels differ. The full cave isn't built: a position's
--| level is computed from the first tile's. The proofs that the answers
--| are the lowest total risks, for every input the parser accepts, are in
--| `Aoc.Year2021.Day15.Proofs` (Proofs/), the tests in
--| `Aoc.Year2021.Day15.Tests` (Tests/); `run` checks neither.

namespace Aoc.Year2021.Day15
import Aoc.Common (Grid, Position, boxEnter, boxGraph, boxIndex, parseGrid)
import Std (Bool, Fail, Fin, Graph, IO, List, Map, Nat, Option, Parse, Text)
import Std.Parse (digit)

def main(): {IO, Fail} () :=
  let cave := parseCave IO.readAll()
  IO.print "Part 1: ${solvePart1 cave}"
  IO.print "Part 2: ${solvePart2 cave}"

-- Positions, their four `neighbours`, the parser and the graph of a
-- rectangle are the shared grid code's (`Aoc.Common`, Common/Grid.sw).

--| The risk levels: digits, so 0 to 9 by their type.
type Cave = { grid: Grid (Fin 10) }

--| One row of digits per line, at least one digit, every row as long as
--| the first (the puzzle's map is a rectangle; `parseGrid` checks it).
def parseCave (input: Text): {Fail} Cave := { grid = parseGrid input digit }

def Cave.height (cave: Cave): Nat := cave.grid.height

def Cave.width (cave: Cave): Nat := cave.grid.width

--| A map of risk levels: `level` gives each position's, for the positions
--| in its `height` rows and `width` columns.
type RiskMap = { height: Nat, width: Nat, level: Position → Nat }

--| The level at `position`; `None` off the map.
def RiskMap.levelAt (risks: RiskMap) (position: Position): Option Nat :=
  boxEnter risks.height risks.width risks.level position

--| The map as a graph for std's search: a step to each neighbour on the
--| map, costing its level.
def RiskMap.graph (risks: RiskMap): Graph Position := boxGraph risks.height risks.width risks.level

--| The map's positions numbered row by row, for the search to keep their
--| costs in arrays.
def RiskMap.index (risks: RiskMap): Graph.Index Position := boxIndex risks.height risks.width

def RiskMap.start (risks: RiskMap): Position := { row = 0, column = 0 }

def RiskMap.target (risks: RiskMap): Position := { row = risks.height - 1, column = risks.width - 1 }

--| The lowest total risk from the top left to the bottom right: Dijkstra's
--| search from the top left, starting at 0 (its level isn't counted).
def RiskMap.lowestRisk (risks: RiskMap): Nat :=
  risks.graph.distances (index := risks.index) [(risks.start, 0)] |> .getOr risks.target 0

--| The levels, looked up in O(log n); 0 off the cave.
def Cave.levels (cave: Cave): Position → Nat := (cave.grid.map (_ digit => digit.toNat)).lookupOr 0

--| The cave's own map.
def Cave.risks (cave: Cave): RiskMap := { height = cave.height, width = cave.width, level = cave.levels }

--| A level raised by up to 8, wrapping past 9 round to 1.
def wrap (level: Nat): Nat := if level > 9 then level - 9 else level

--| The full cave, five tiles each way: the tile `position` is in (its row
--| and column divided by the cave's height and width) raises the level at
--| the same place in the first tile (the remainders) by the tile's row
--| plus its column.
def Cave.tiles (cave: Cave): RiskMap :=
  let find := cave.levels
  let height := cave.height
  let width := cave.width
  {
    height = 5 * height,
    width = 5 * width,
    level = position =>
      let base := find { row = position.row % height, column = position.column % width }
      wrap (base + (position.row / height + position.column / width))
  }

--| The full cave; a cave with no levels has no tiles.
def Cave.tiled (cave: Cave): RiskMap :=
  if tall: cave.height != 0 then if wide: cave.width != 0 then cave.tiles else cave.risks else cave.risks

def solvePart1 (cave: Cave): Nat := cave.risks.lowestRisk

def solvePart2 (cave: Cave): Nat := cave.tiled.lowestRisk
