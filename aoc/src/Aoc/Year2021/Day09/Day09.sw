--| Advent of Code 2021, day 9: a height map of the floor of a cave, one
--| digit per location, 0 the lowest and 9 the highest. A low point is a
--| location lower than each of the locations up, down, left and right of
--| it. Part 1 adds up each low point's risk level, its height plus 1. Part
--| 2 finds the basins, the areas that drain to each low point, walled in
--| by the 9s, and multiplies the sizes of the three largest.
--|
--|   $ cd aoc && stitchwort run Aoc.Year2021.Day09.main < inputs/2021/day09.txt
--|
--| The puzzle input is committed in aoc/inputs/2021/.
--|
--| A basin is found by a flood fill from its low point, through the
--| locations that aren't 9: std's breadth-first search
--| (`Graph.breadthFirst`) on the graph whose edges are the steps between
--| such neighbours. The proofs that both answers are the puzzle's, for every
--| height map, are in `Aoc.Year2021.Day09.Proofs` (Proofs/), and the tests
--| in `Aoc.Year2021.Day09.Tests` (Tests/); `run` checks neither.
-- Positions, neighbours, lookups, the parser and the grid's graph are the
-- shared grid code's (`Aoc.Common`, Common/Grid.sw).

namespace Aoc.Year2021.Day09
import Aoc.Common (Grid, Position, parseGrid)
import Std (Fail, Fin, Graph, IO, List, Map, Nat, Option, Ord, Parse, Text)
import Std.Parse (digit)

def main(): {IO, Fail} () :=
  let map := parseHeightMap IO.readAll()
  IO.print "Part 1: ${solvePart1 map}"
  IO.print "Part 2: ${solvePart2 map}"

--| The heights of the floor: digits, so 0 to 9 by their type.
type HeightMap = { grid: Grid (Fin 10) }

--| One row of digits per line, every row as long as the first (the
--| puzzle's map is a rectangle; `parseGrid` checks it).
def parseHeightMap (input: Text): {Fail} HeightMap := { grid = parseGrid input digit }

--| Every location with its height, row by row.
def HeightMap.cells (map: HeightMap): List (Position, Nat) :=
  map.grid.cells |> .map (((at, height)) => (at, height.toNat))

--| The height at `position`; `None` off the map.
def HeightMap.heightAt (map: HeightMap) (position: Position): Option Nat := map.grid.at position |> .map Fin.toNat

--| Lower than every neighbour (up, right, down and left) on the map. A
--| neighbour past the far edges has no height.
def HeightMap.isLowPoint (map: HeightMap) (position: Position) (height: Nat): Bool :=
  position.neighbours.all (next => map.heightAt next |> .all (other => height < other))

--| The low points, each with its height.
def HeightMap.lowPoints (map: HeightMap): List (Position, Nat) :=
  map.cells.filter (((position, height)) => map.isLowPoint position height)

def solvePart1 (map: HeightMap): Nat := map.lowPoints.sumBy (((_, height)) => height + 1)

--| On the map and not a 9: a location some basin has.
def HeightMap.isOpen (map: HeightMap) (position: Position): Bool := map.heightAt position |> .any (!= 9)

--| Entering a location that isn't a 9 takes a step.
def enterOpen (position: Position) (height: Fin 10): Option Nat := if height.toNat != 9 then Some 1 else None

--| The map as a graph for std's search: a step to each neighbour that
--| isn't a 9.
def HeightMap.graph (map: HeightMap): Graph Position := map.grid.graph enterOpen

--| The number of locations in the basin of `low`: those the flood fill
--| from it reaches in `graph`, the map's. A 9 is in no basin (and a low
--| point is a 9 only on a map of one location).
def HeightMap.basinSize (map: HeightMap) (graph: Graph Position) (low: Position): Nat :=
  if map.isOpen low then (graph.breadthFirst [low]).size else 0

--| Each low point's basin size.
-- The graph is built once: its `states` list, every location, is
-- computed when it is built.
def HeightMap.basinSizes (map: HeightMap): List Nat :=
  let graph := map.graph
  map.lowPoints.map (((low, _)) => map.basinSize graph low)

--| The product of the three largest sizes (of all of them, if fewer).
def largestThreeProduct (sizes: List Nat): Nat := sizes.sort [ord := Ord.reverse] |> .take 3 |> .product

def solvePart2 (map: HeightMap): Nat := largestThreeProduct map.basinSizes
