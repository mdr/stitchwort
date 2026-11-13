--| Advent of Code 2024, day 12: a map of garden plots, each growing one plant
--| (a letter). Plots with the same plant touching up, down, left or right form
--| a region. Part 1 adds up, over the regions, area times perimeter; part 2
--| adds up area times the number of sides.
--|
--|   $ cd aoc && stitchwort run Aoc.Year2024.Day12.main < examples/2024/day12.txt
--|
--| The proofs are in `Aoc.Year2024.Day12.Proofs` (Proofs/) and the tests in
--| `Aoc.Year2024.Day12.Tests` (Tests/); `run` checks neither.

namespace Aoc.Year2024.Day12
import Aoc.Common (Direction, Position, directions)
import Std (Bool, Char, DecEq, Fail, IO, List, Map, Nat, Option, Parse, Set, Text, Void)

def main(): {IO, Fail} () :=
  let garden := parseGarden IO.readAll()
  IO.print "Part 1: ${solvePart1 garden}"
  IO.print "Part 2: ${solvePart2 garden}"

--| The plant of each plot, by position.
type Garden = { plots: Map Position Char }

--| One plot: its plant, a letter.
def plantLetter(): {Parse} Char := Parse.satisfy "a letter" .isAsciiLetter

--| One row per line, all as long as the first.
def parseGarden (input: Text): {Fail} Garden :=
  let grid := Parse.all input (() => Parse.grid plantLetter)
  let rows := grid.toList.map .toList
  let width := grid.head.length
  rows.withIndex |> .map (((row, plants)) =>
    Fail.ensure (plants.length == width) "line ${row + 1}: expected ${width} plots, as on the first line, got ${plants.length}")
  let plots := rows.gridCells |> .map ((((row, column), plant)) => (({ row, column }: Position), plant))
  { plots = plots.toMap }

--| The plant at `position`; `None` off the map.
def Garden.plantAt (garden: Garden) (position: Position): Option Char := garden.plots.get position

--| Every plot of the map, row by row.
def Garden.positions (garden: Garden): List Position := garden.plots.keys

-- Positions, directions and a step (none above row 0 or left of column 0)
-- are the shared grid code's (`Aoc.Common`).

--| Whether the plot one step in `direction` grows the same plant.
def Garden.sameAcross (garden: Garden) (position: Position) (direction: Direction): Bool :=
  (position.step direction |> .flatMap garden.plantAt) == garden.plantAt position

--| The neighbours growing `plant`.
def Garden.neighboursGrowing (garden: Garden) (plant: Char) (position: Position): List Position :=
  directions.filterMap position.step |> .filter (next => garden.plantAt next == Some plant)

--| How many positions the fill has still to visit: it gets smaller each time
--| the fill takes a plot.
def Garden.unvisited (garden: Garden) (visited: Set Position): Nat := garden.positions.count (position => !visited.contains position)

--| A position growing a plant is on the list.
theorem Garden.positionsComplete ∀ (garden: Garden) (position: Position) (plant: Char) (grows: garden.plantAt position = Some plant):
    position ∈ garden.positions :=
  Map.memKeysOfContains garden.plots position (Map.containsOfGet garden.plots position plant grows)

--| Taking a plot not yet visited leaves fewer to visit.
theorem Garden.unvisitedInsert ∀ (garden: Garden) (visited: Set Position) (position: Position) (plant: Char)
    (grows: garden.plantAt position = Some plant) (fresh: visited.contains position = False):
    garden.unvisited (visited.insert position) < garden.unvisited visited :=
  List.countLtMem garden.positions (other => !(visited.insert position).contains other) (other => !visited.contains other)
    (other member kept =>
      match same: visited.contains other with
        | True => rewrite Set.containsInsertMono visited position other same at kept in kept
        | False => rfl)
    position (garden.positionsComplete position plant grows) (rewrite fresh in rfl) (rewrite Set.containsInsert position visited in rfl)

--| The plots growing `plant` reachable from the stack, joined to `members`:
--| a depth-first flood fill. `visited` has the members, for quick lookup.
def Garden.fill (garden: Garden) (plant: Char) (stack: List Position) (visited: Set Position) (members: List Position): List Position
    decreasing (garden.unvisited visited, stack.length)
:= match stack with
  | [] => members
  | [position, ..rest] =>
    if fresh: visited.contains position = False then
      if grows: garden.plantAt position = Some plant then
        garden.fill plant (garden.neighboursGrowing plant position ++ rest) (visited.insert position) [position, ..members]
          [decreasing := Nat.LexLess.First (garden.unvisitedInsert visited position plant grows fresh)]
      else garden.fill plant rest visited members [decreasing := Nat.LexLess.Second rfl (omega)]
    else garden.fill plant rest visited members [decreasing := Nat.LexLess.Second rfl (omega)]

--| A region: the plots joined to each other, growing one plant, each listed
--| once.
type Region = { plots: List Position }

--| The region containing `start`: the plots joined to it.
def Garden.regionOf (garden: Garden) (start: Position): Region := match garden.plantAt start with
  | Some plant => { plots = garden.fill plant [start] Set.empty [] }
  | None => { plots = [] }

--| The regions, each once, from the positions not yet in a region.
def Garden.regionsFrom (garden: Garden): (starts: List Position) → (seen: Set Position) → List Region
  | [], seen => []
  | [start, ..rest], seen =>
    if seen.contains start then garden.regionsFrom rest seen
    else
      let region := garden.regionOf start
      [region, ..garden.regionsFrom rest (region.plots.foldLeft seen Set.insert)]

def Garden.regions (garden: Garden): List Region := garden.regionsFrom garden.positions Set.empty

--| A plot's sides with a fence: those not facing the same plant.
def Garden.fences (garden: Garden) (position: Position): Nat := directions.count (direction => !garden.sameAcross position direction)

--| The number of plots in the region.
def Region.area (region: Region): Nat := region.plots.length

--| Whether `position` is a plot of the region.
def Region.contains (region: Region) (position: Position): Bool := region.plots.contains position

--| The length of the region's fence: the plots' sides with a fence.
def Region.perimeter (region: Region) (garden: Garden): Nat := region.plots.sumBy garden.fences

--| The four corners of a plot: the side up or down, and the side left or
--| right.
def quadrants: List (Direction, Direction) := [(Up, Left), (Up, Right), (Down, Left), (Down, Right)]

--| The grid point diagonally across a plot's corner.
def Position.diagonal (position: Position) (vertical: Direction) (horizontal: Direction): Option Position :=
  position.step vertical |> .flatMap (.step horizontal)

--| A corner of the region's fence at a plot: outside, where neither side
--| faces the same plant, or inside, where both do but the plot diagonally
--| across doesn't.
def Garden.isCorner (garden: Garden) (position: Position) (vertical: Direction) (horizontal: Direction): Bool :=
  (garden.sameAcross position vertical, garden.sameAcross position horizontal) |> matches
    | (False, False)
    | (True, True) => (position.diagonal vertical horizontal |> .flatMap garden.plantAt) != garden.plantAt position

def Garden.cornerCount (garden: Garden) (position: Position): Nat := quadrants.count (quadrant => garden.isCorner position quadrant.fst quadrant.snd)

--| The number of sides of the region's fence, counted as its corners (a
--| polygon has as many sides as corners).
def Region.sides (region: Region) (garden: Garden): Nat := region.plots.sumBy garden.cornerCount

def solvePart1 (garden: Garden): Nat := garden.regions |> .sumBy (region => region.area * region.perimeter garden)

def solvePart2 (garden: Garden): Nat := garden.regions |> .sumBy (region => region.area * region.sides garden)
