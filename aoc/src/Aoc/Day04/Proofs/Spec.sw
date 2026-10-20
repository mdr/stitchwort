-- Day 4 as the puzzle states it, cell by cell, for the proof in
-- Proofs/Part1.sw.
--
-- In plain words:
--   - The input's lines are the rows of a grid. A cell holds a roll of paper
--     when it is `@`; anything else is floor, and so is everything off the
--     grid.
--   - "The forklifts can only access a roll of paper if there are fewer than
--     four rolls of paper in the eight adjacent positions": a roll is
--     accessible when fewer than 4 of the 8 cells around it hold rolls.
--   - Part 1 counts the accessible rolls.
--
-- The grid is rectangular in the puzzle; the proof assumes it (all lines as
-- long as each other), and only that.
--
-- Shared with the program: `parseChar` (`@` is a roll, 1; anything else 0).

namespace Aoc.Day04.Proofs
import Aoc.Day04 (..)

-- Row R, column C of the grid with an empty border around it: rows and
-- columns are counted from 1, and row 0 and column 0 (and everything past
-- the grid) hold no roll. 1 for a roll, 0 for none.
def rollAt (lines: List Text) (row: Nat) (col: Nat): Nat :=
  List.getOr 0 col (Cons 0 (List.getOr Nil row (Cons Nil (lines.map (line => line.toList.map parseChar)))))

-- How many of the eight cells around the cell in row r, column c (counted
-- from 0) hold rolls: the column to its left, the cells above and below it,
-- and the column to its right.
def neighbours (lines: List Text) (r: Nat) (c: Nat): Nat :=
  (rollAt lines r c + rollAt lines (r + 1) c + rollAt lines (r + 2) c) +
    (rollAt lines r (c + 1) + rollAt lines (r + 2) (c + 1)) +
    (rollAt lines r (c + 2) + rollAt lines (r + 1) (c + 2) + rollAt lines (r + 2) (c + 2))

-- The cell holds a roll that a forklift can access.
def accessible (lines: List Text) (r: Nat) (c: Nat): Bool := rollAt lines (r + 1) (c + 1) == 1 && neighbours lines r c < 4

-- Part 1: the accessible rolls, row by row.
def part1Spec (lines: List Text): Nat :=
  List.range lines.length |> .sumBy (r =>
    List.range (List.getOr "" r lines).length |> .sumBy (c => if accessible lines r c then 1 else 0))

test "spec on the example" := part1Spec example == 13
test "spec cells" := (rollAt example 1 3, rollAt example 0 3, rollAt example 1 0, neighbours example 0 2, accessible example 0 2) == (1, 0, 0, 3, True)
