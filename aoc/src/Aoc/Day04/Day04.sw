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
-- it is rectangular by its type; parsing refuses lines of different lengths
-- and characters other than @ and . (naming the line and column).
-- A roll's "window" is the 3 by 3 block around it, itself included, so it is
-- accessible when its window holds fewer than 5 rolls. For each row, add it
-- to the rows above and below column by column, then add each column's sum to
-- its neighbours' (`peelRow`). Part 2 repeats such rounds until one removes
-- nothing.
--
-- Both parts are proved right for every grid in `Aoc.Day04.Proofs`
-- (Spec/Spec.sw states the puzzle by positions; Proofs/Part1.sw and
-- Proofs/Part2.sw; the parser in Proofs/Parse.sw), and the tests are in
-- `Aoc.Day04.Tests` (Tests/); `run` checks neither.

namespace Aoc.Day04
import Std (Fail, IO, Option, Result, Vec)

type Cell =
  | Roll
  | Floor

-- How many rolls a cell holds.
def Cell.count: Cell → Nat
  | Roll => 1
  | Floor => 0

-- `height` rows of `width` cells each.
type Grid = { height: Nat, width: Nat, rows: Vec (Vec Cell width) height }

def main(): {IO, Fail} () :=
  let grid := (parseGrid IO.readAllLines()).orFail
  IO.print "Part 1: ${solvePart1 grid}"
  IO.print "Part 2: ${solvePart2 grid}"

-- Part 1: the rolls one round removes.
def solvePart1 (grid: Grid): Nat := grid.rolls - grid.round.rolls

-- Part 2: the rolls removed by rounds until none is accessible.
def solvePart2 (grid: Grid): Nat := grid.rolls - grid.settle.rolls

-- An error for a character other than @ and ., or for lines that are not all
-- as long as the first.
def parseGrid (lines: List Text): Result Grid Text :=
  match findStray lines with
    | Some (row, column, ch) => Err "line ${row}, column ${column}: expected '@' or '.', got '${ch}'"
    | None => gridOf lines |> .toResult "expected lines that are all the same length, got a line of a different length"

-- The line and column (both from 1) of the first character that is neither
-- @ nor ., and the character.
def findStray (lines: List Text): Option (Nat, Nat, Char) :=
  lines.withIndex.findMap (((rowIndex, line)) =>
    line.toList.withIndex.findMap (((columnIndex, ch)) =>
      if ch == '@' ∨ ch == '.' then None else Some (rowIndex + 1, columnIndex + 1, ch)))

-- `None` if the lines are not all as long as the first.
def gridOf (lines: List Text): Option Grid :=
  let width := lines.headOr "" |> .length
  Vec.fromList lines
    |> .traverseOption (line => Vec.ofList width (parseLine line))
    |> .map (rows => ({ height = lines.length, width, rows }: Grid))

def parseLine (line: Text): List Cell := line.toList.map parseChar

-- `findStray` has checked that anything but @ is a `.`.
def parseChar (ch: Char): Cell := if ch == '@' then Roll else Floor

def Grid.rolls (grid: Grid): Nat := countRolls grid.rows

-- The rolls in some rows.
def countRolls (rows: Vec (Vec Cell w) h): Nat := rows.sumBy (.sumBy .count)

def Grid.round (grid: Grid): Grid := { grid | rows = roundRows grid.rows }

-- Remove every accessible roll, all at once: each row is peeled with the
-- rows above and below it as they were, and a row of floor past either end.
def roundRows (rows: Vec (Vec Cell w) h): Vec (Vec Cell w) h := rows.around (Vec.replicate w Floor) peelRow

-- Remove the accessible rolls of one row, given the rows above and below:
-- add the three rows column by column, then each column's sum to its
-- neighbours' (the window of 3 by 3 cells).
def peelRow (above row below: Vec Cell w): Vec Cell w :=
  let columns := Vec.zipWith3 above row below (aboveCell rowCell belowCell => aboveCell.count + rowCell.count + belowCell.count)
  let windows := columns.around 0 (left here right => left + here + right)
  Vec.zipWith row windows (roll window => if roll == Roll ∧ 5 ≤ window then Roll else Floor)

def Grid.settle (grid: Grid): Grid := { grid | rows = settleRows grid.rows }

-- Rounds until one removes no roll; then none is accessible. The rolls left
-- measure the recursion: the guard tests the decrease itself.
def settleRows (rows: Vec (Vec Cell w) h): Vec (Vec Cell w) h
    decreasing countRolls rows
:=
  let next := roundRows rows
  if fewer: countRolls next < countRolls rows then settleRows next else rows
