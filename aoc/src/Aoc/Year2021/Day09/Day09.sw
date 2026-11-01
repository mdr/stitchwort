-- Advent of Code 2021, day 9: a height map of the floor of a cave, one
-- digit per location, 0 the lowest and 9 the highest. A low point is a
-- location lower than each of the locations up, down, left and right of
-- it. Part 1 adds up each low point's risk level, its height plus 1. Part
-- 2 finds the basins, the areas that drain to each low point, walled in
-- by the 9s, and multiplies the sizes of the three largest.
--
--   $ cd aoc && stitchwort run Aoc.Year2021.Day09.main < inputs/2021/day09.txt
--
-- The puzzle input is committed in aoc/inputs/2021/.
--
-- A basin is found by a flood fill from its low point, through the
-- locations that aren't 9: std's breadth-first search (`Graph.breadthFirst`)
-- on the graph whose edges are the steps between such neighbours. The
-- proofs that both answers are the puzzle's, for every height map, are in
-- `Aoc.Year2021.Day09.Proofs` (Proofs/), and the tests in
-- `Aoc.Year2021.Day09.Tests` (Tests/); `run` checks neither.

namespace Aoc.Year2021.Day09
import Std (Fail, Fin, Graph, IO, List, Map, Nat, Option, Ord, Parse, Text)
import Std.Parse (digit, many1)

def main(): {IO, Fail} () :=
  let map := parseHeightMap IO.readAll()
  IO.print "Part 1: ${solvePart1 map}"
  IO.print "Part 2: ${solvePart2 map}"

type Position = { row: Nat, column: Nat }

-- The heights, row by row: digits, so 0 to 9 by their type.
type HeightMap = { rows: List (List (Fin 10)) }

-- One row of digits per line, every row as long as the first (the
-- puzzle's map is a rectangle).
def parseHeightMap (input: Text): {Fail} HeightMap := checkRows (Parse.eachLine input (() => many1 digit))

-- The map, if every row is as long as the first; otherwise fail, naming
-- the first that isn't.
def checkRows (rows: List (List (Fin 10))): {Fail} HeightMap :=
  match firstRagged rows with
    | Some (index, row) => Fail.fail "line ${index + 1}: expected ${width rows} digits, as on the first line, got ${row.length}"
    | None => { rows }

-- The first row's length.
def width (rows: List (List (Fin 10))): Nat := rows.headOr [] |> .length

-- The first row not as long as the first, with its index.
def firstRagged (rows: List (List (Fin 10))): Option (Nat, List (Fin 10)) :=
  rows.withIndex.find (((_, row)) => row.length != width rows)

-- Every location with its height, row by row.
def HeightMap.cells (map: HeightMap): List (Position, Nat) :=
  map.rows.gridCells |> .map (((at, height)) => (({ row = at.fst, column = at.snd }: Position), height.toNat))

-- The height at `position`; `None` off the map.
def HeightMap.heightAt (map: HeightMap) (position: Position): Option Nat :=
  map.rows.getOr position.row Nil |> .get position.column |> .map Fin.toNat

-- The positions one step up, left, right and down: none above row 0 or
-- left of column 0, as positions are `Nat`s. One right of the last column
-- or below the last row is off the map, with no height.
def Position.neighbours (position: Position): List Position :=
  let up := match position.row with
    | Zero => Nil
    | Succ above => [{ position | row = above }]
  let left := match position.column with
    | Zero => Nil
    | Succ before => [{ position | column = before }]
  up ++ left ++ [{ position | column = position.column + 1 }, { position | row = position.row + 1 }]

-- Lower than every neighbour on the map.
def HeightMap.isLowPoint (map: HeightMap) (position: Position) (height: Nat): Bool :=
  position.neighbours.all (next => map.heightAt next |> .all (other => height < other))

-- The low points, each with its height.
def HeightMap.lowPoints (map: HeightMap): List (Position, Nat) := map.cells.filter (((position, height)) => map.isLowPoint position height)

def solvePart1 (map: HeightMap): Nat := map.lowPoints.sumBy (((_, height)) => height + 1)

-- On the map and not a 9: a location some basin has.
def HeightMap.isOpen (map: HeightMap) (position: Position): Bool := map.heightAt position |> .any (height => height != 9)

-- A step from `position` to each neighbour that isn't a 9.
def HeightMap.edges (map: HeightMap) (position: Position): List (Position, Nat) :=
  position.neighbours.filter map.isOpen |> .map (next => (next, 1))

-- The map as a graph for std's search. Every step leads to a location on
-- the map (`edgesListed`, in Steps.sw).
def HeightMap.graph (map: HeightMap): Graph Position := {
  edges = map.edges,
  states = map.cells.map Pair.fst,
  listed = position next weight edge => map.edgesListed position next weight edge
}

-- The number of locations in the basin of `low`: those the flood fill
-- from it reaches in `graph`, the map's. A 9 is in no basin (and a low
-- point is a 9 only on a map of one location).
def HeightMap.basinSize (map: HeightMap) (graph: Graph Position) (low: Position): Nat :=
  if map.isOpen low then (graph.breadthFirst [low]).size else 0

-- Each low point's basin size. The graph is built once: its `states`
-- list, every location, is computed when it is built.
def HeightMap.basinSizes (map: HeightMap): List Nat :=
  let graph := map.graph
  map.lowPoints.map (((low, _)) => map.basinSize graph low)

-- The product of the three largest sizes (of all of them, if fewer).
def largestThreeProduct (sizes: List Nat): Nat := sizes.sort [ord := Ord.reverse] |> .take 3 |> .product

def solvePart2 (map: HeightMap): Nat := largestThreeProduct map.basinSizes
