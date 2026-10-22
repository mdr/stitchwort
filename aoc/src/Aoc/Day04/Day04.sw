-- Advent of Code 2025, day 4: a grid of paper rolls (@) and empty floor (.).
-- A roll is accessible when fewer than four of its eight neighbours are
-- rolls. Part 1 counts the accessible rolls. Part 2 removes them, repeats
-- until none are accessible, and counts every roll removed.
--
--   $ cd aoc && stitchwort run Aoc.Day04.main < inputs/day04.txt
--
-- The puzzle input is committed in aoc/inputs/ (D119).
--
-- The grid is a vector of rows, each a vector of cells (a roll or floor), so
-- it is rectangular by its type; parsing refuses lines of different lengths.
-- A roll's "window" is the 3 by 3 block around it, itself included, so it is
-- accessible when its window holds fewer than 5 rolls. For each row, add it
-- to the rows above and below column by column, then add each column's sum to
-- its neighbours' (`peelRow`).
--
-- Both parts are proved right for every grid in `Aoc.Day04.Proofs`
-- (Proofs/Spec.sw states the puzzle by positions; Proofs/Part1.sw and
-- Proofs/Part2.sw; the parser in Proofs/Parse.sw), and the tests are in
-- `Aoc.Day04.Tests` (Tests/); `run` checks neither.

namespace Aoc.Day04
import Std (IO, Option, Pair, Vec)

type Cell =
  | Roll
  | Floor

-- How many rolls a cell holds.
def Cell.count: Cell -> Nat
  | Roll  => 1
  | Floor => 0

-- `height` rows of `width` cells each.
type Grid = { height: Nat, width: Nat, rows: Vec (Vec Cell width) height }

def main(): {IO} () :=
  match parseGrid IO.readAllLines() with
    | None   => IO.print "The lines are not all the same length."
    | Some grid =>
      IO.print "Part 1: ${solvePart1 grid}"
      IO.print "Part 2: ${solvePart2 grid}"

-- Part 1: the rolls one round removes.
def solvePart1 (grid: Grid): Nat := grid.rolls - grid.round.rolls

-- Part 2: the rolls removed by rounds until none is accessible.
def solvePart2 (grid: Grid): Nat := grid.rolls - grid.settle.rolls

-- `None` if the lines are not all as long as the first.
def parseGrid (lines: List Text): Option Grid :=
  let width := (lines.headOr "").length
  Vec.fromList lines
    |> Vec.traverseOption (line => Vec.ofList width (parseLine line))
    |> Option.map (rows => ({ height = lines.length, width, rows }: Grid))

def parseLine (line: Text): List Cell := line.toList.map parseChar

def parseChar (ch: Char): Cell := if ch == '@' then Roll else Floor

def Grid.rolls (grid: Grid): Nat := grid.rows.sumBy (row => row.sumBy .count)

-- Remove every accessible roll, all at once: each row is peeled with the
-- rows above and below it as they were, and a row of floor past either end.
def Grid.round (grid: Grid): Grid :=
  { grid | rows = grid.rows.around (Vec.replicate grid.width Floor) peelRow }

-- Remove the accessible rolls of one row, given the rows above and below:
-- add the three rows column by column, then each column's sum to its
-- neighbours' (the window of 3 by 3 cells).
def peelRow (above row below: Vec Cell w): Vec Cell w :=
  let columns := Vec.zipWith3 (a r b => a.count + r.count + b.count) above row below
  let windows := columns.around 0 (left here right => left + here + right)
  Vec.zipWith (roll window => if roll == Roll && 5 <= window then Roll else Floor) row windows

-- Rows marked with whether they changed in the last pass.
type Marked (w h: Nat) = Vec (Vec Cell w, Bool) h

-- Like `round`, but going down the grid, each row sees the row above it
-- after its rolls were removed. Removing a roll never stops another from
-- being accessible, so the end state is the same as with `round`, reached in
-- fewer passes. A row is only looked at again when it or the row below
-- changed in the last pass, or the row above changed in this one; the rest
-- are passed over.
def sweep (grid: Marked w h): Marked w h :=
  let gap := Vec.replicate w Floor
  sweepFrom gap gap False grid

-- `above` is the (already swept) row above the first row of the grid, and
-- `aboveChanged` says whether this pass changed it.
def sweepFrom (gap above: Vec Cell w) (aboveChanged: Bool): Marked w h -> Marked w h
  | VNil                    => VNil
  | VCons (row, moved) rest =>
    let (below, belowMoved) := rest.headOr (gap, False)
    let (swept, changed) := sweepRow above aboveChanged row moved below belowMoved
    VCons (swept, changed) (sweepFrom gap swept changed rest)

-- One row of a pass, and whether it changed: peeled if it or the row below
-- changed in the last pass, or the row above in this one; else kept.
def sweepRow (above: Vec Cell w) (aboveChanged: Bool) (row: Vec Cell w) (moved: Bool) (below: Vec Cell w) (belowMoved: Bool): (Vec Cell w, Bool) :=
  if moved || belowMoved || aboveChanged then
    let swept := peelRow above row below
    (swept, not (swept.toList == row.toList))
  else (row, False)

-- Sweep until a pass removes no roll. A pass that changes something removes
-- one (`fewerRolls`, Proofs/Part2.sw), and the rolls left measure the
-- recursion: the guard tests the decrease itself.
def Grid.settle (grid: Grid): Grid :=
  { grid | rows = Vec.map Pair.fst (settleMarked (grid.rows.map (row => (row, True)))) }

-- The rolls in a marked grid.
def Marked.rolls (grid: Marked w h): Nat := (grid.map Pair.fst).sumBy (row => row.sumBy .count)

def settleMarked (grid: Marked w h): Marked w h
  decreasing Marked.rolls grid
:=
  let next := sweep grid
  if fewer: Marked.rolls next < Marked.rolls grid then settleMarked next else next

