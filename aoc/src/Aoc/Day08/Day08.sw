-- Advent of Code 2025, day 8: junction boxes floating in 3D space. Joining
-- two boxes with a string of lights puts them in the same circuit. Part 1
-- joins the closest pairs of boxes, 1,000 of them, and multiplies the sizes
-- of the three biggest circuits. Part 2 keeps joining until every box is in
-- one circuit and multiplies the x coordinates of the last two boxes joined.
--
--   $ cd aoc && stitchwort run Aoc.Day08.main < inputs/day08.txt
--
-- The puzzle input is committed in aoc/inputs/ (D119).
--
-- Every pair of boxes is a candidate, about half a million for 1,000 boxes.
-- They are sorted once, closest first (`closestFirst`), and both parts walk
-- that list, joining the pairs in order. A box's circuit is a label, kept in
-- a `Map` from the box's number to its label; joining two circuits gives
-- all of one label the other's (`Circuits.join`). A pair that is already in
-- one circuit changes nothing, but it still counts as one of part 1's 1,000.
--
-- The tests are in `Aoc.Day08.Tests` (Tests/); `run` checks none of them.

namespace Aoc.Day08
import Std (Abort, IO, List, Map, Nat, Option, Text)
import Std.Abort (toOption)

def main(): {IO} () :=
  let boxes := parseBoxes IO.readAllLines()
  IO.print "Part 1: ${solvePart1 1000 boxes}"
  match solvePart2 boxes with
    | None        => IO.print "Part 2: the boxes are already in one circuit."
    | Some answer => IO.print "Part 2: ${answer}"

type Point = { x: Nat, y: Nat, z: Nat }

-- The boxes, and every pair of them closest first (`closestFirst`), sorted
-- once for both parts.
type Boxes = { points: List Point, pairs: List Connection }

def parseBoxes (lines: List Text): Boxes := Boxes.of (parsePoints lines)

def Boxes.of (points: List Point): Boxes := { points, pairs = closestFirst points }

-- Lines that aren't three numbers (a blank line at the end) are skipped.
def parsePoints (lines: List Text): List Point := lines.filterMap parsePoint

def parsePoint (line: Text): Option Point := toOption (() => readPoint line)

-- Each number that isn't one makes the whole line give up.
def readPoint (line: Text): {Abort} Point :=
  match line.split ',' with
    | [xText, yText, zText] => { x = xText.toNat.orAbort, y = yText.toNat.orAbort, z = zText.toNat.orAbort }
    | _                     => Abort.abort()

-- The straight-line distance squared: it orders pairs the same way as the
-- distance, and needs no square root.
def Point.squaredDistance (p: Point) (q: Point): Nat :=
  square (Nat.absDiff p.x q.x) + square (Nat.absDiff p.y q.y) + square (Nat.absDiff p.z q.z)

def square (n: Nat): Nat := n * n

-- A pair of boxes, with the boxes numbered by their place in the list and
-- the first before the second. Connections are ordered by those three
-- numbers in turn (the derived `Ord`: fields left to right), so pairs at
-- the same distance come in the order of their box numbers.
type Connection = { distance: Nat, first: Nat, second: Nat }

-- Every pair of boxes, closest first.
def closestFirst (points: List Point): List Connection :=
  points.withIndex.pairs
    |> .map (((first, second)) => Connection.between first second)
    |> .sort

-- The connection of two numbered boxes.
def Connection.between (first: (Nat, Point)) (second: (Nat, Point)): Connection :=
  { distance = first.snd.squaredDistance second.snd, first = first.fst, second = second.fst }

-- Which circuit each box is in, and how many circuits there are. The label
-- of a circuit is the number of one of its boxes.
type Circuits = { labels: Map Nat Nat, count: Nat }

-- Every box in a circuit of its own.
def Circuits.separate (boxes: Nat): Circuits :=
  { labels = Map.fromList (List.range boxes |> .map (box => (box, box))), count = boxes }

-- Every box has a label, so the box number is never the label returned.
def Circuits.labelOf (circuits: Circuits) (box: Nat): Nat := circuits.labels |> Map.getOr box box

-- Joins the circuits of two boxes: every box in the first box's circuit
-- takes the second's label.
def Circuits.join (circuits: Circuits) (first: Nat) (second: Nat): Circuits :=
  let firstLabel := circuits.labelOf first
  let secondLabel := circuits.labelOf second
  if firstLabel == secondLabel then circuits
  else
    { labels = circuits.labels |> Map.map (label => if label == firstLabel then secondLabel else label)
    , count = circuits.count - 1
    }

-- Joins the two boxes of a pair from `closestFirst`.
def Circuits.connect (circuits: Circuits) (connection: Connection): Circuits :=
  circuits.join connection.first connection.second

-- How many boxes are in each circuit, a circuit counted once, at its first
-- (lowest-numbered) box.
def Circuits.sizes (circuits: Circuits) (boxes: Nat): List Nat :=
  let labels := List.range boxes |> .map circuits.labelOf
  List.range boxes
    |> .filter (box => !(labels.take box |> .any (label => label == circuits.labelOf box)))
    |> .map (box => labels.count (label => label == circuits.labelOf box))

-- Part 1: join the closest `connections` pairs (1,000 for the puzzle input,
-- 10 for its example), then multiply the sizes of the three biggest circuits.
def solvePart1 (connections: Nat) (boxes: Boxes): Nat :=
  let joined := boxes.pairs.take connections
    |> .foldLeft Circuits.connect (Circuits.separate boxes.points.length)
  joined.sizes boxes.points.length |> .sortBy (a b => Nat.compare b a) |> .take 3 |> .product

-- Part 2: the product of the x coordinates of the two boxes whose joining
-- leaves one circuit. `None` if there are no such boxes: the points start in
-- one circuit (one point, or none).
def solvePart2 (boxes: Boxes): Option Nat :=
  (lastJoin (Circuits.separate boxes.points.length) boxes.pairs).map (((first, second)) =>
    (boxes.points.getOr origin first).x * (boxes.points.getOr origin second).x)

-- Every box number is in range, so this default is never used.
def origin: Point := { x = 0, y = 0, z = 0 }

-- The pair that leaves one circuit, joining the pairs in order from the
-- circuits given.
def lastJoin (circuits: Circuits): List Connection -> Option (Nat, Nat)
  | Nil                  => None
  | Cons connection rest =>
    let joined := circuits.connect connection
    if circuits.count > 1 && joined.count == 1 then Some (connection.first, connection.second)
    else lastJoin joined rest
