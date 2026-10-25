-- Day 4 as the puzzle states it, position by position, for the proofs in
-- Proofs/Part1.sw and Proofs/Part2.sw.
--
-- In plain words:
--   - The grid has `height` rows and `width` columns. What a position holds
--     is a function from (row, column) to a cell, a roll or floor; off the
--     grid, everything is floor.
--   - "The forklifts can only access a roll of paper if there are fewer than
--     four rolls of paper in the eight adjacent positions": a position's
--     neighbours are the other positions whose row and column each differ
--     from its own by at most 1, and a roll is accessible when fewer than 4
--     of them hold rolls.
--   - Part 1 counts the accessible rolls.
--   - Part 2: "Once a roll of paper can be accessed by a forklift, it can be
--     removed. Once a roll of paper is removed, the forklifts might be able
--     to access more rolls of paper": remove the accessible rolls (all at
--     once, a round), and repeat until none is accessible. Count the rolls
--     removed. Each round that changes anything removes a roll, so as many
--     rounds as there are rolls are enough; Proofs/Rounds.sw proves that no
--     roll is accessible after them (`roundsStable`).
--
-- Shared with the program: `Cell` and the grid's type, `Grid`.

namespace Aoc.Day04.Spec
import Aoc.Day04 (..)
import Std (List, Nat, Option, Vec)

-- What each position holds, (row, column) -> cell.
type Cells = Nat → Nat → Cell

-- The grid's cells: row r (counted from 0, and a row of floor past the last),
-- then cell c of it (floor past the last).
def cellsOf (grid: Grid): Cells :=
  r c => grid.rows |> Vec.getOr (Vec.replicate grid.width Floor) r |> Vec.getOr Floor c

-- How many positions (r, c) of the grid satisfy `p`.
def countPositions (grid: Grid) (p: Nat → Nat → Bool): Nat :=
  List.range grid.height |> .sumBy (r => List.range grid.width |> .count (c => p r c))

-- Positions (r, c) and (r2, c2) are next to each other: different, with
-- rows and columns each at most 1 apart.
def adjacent (r: Nat) (c: Nat) (r2: Nat) (c2: Nat): Bool :=
  Nat.absDiff r r2 ≤ 1 ∧ Nat.absDiff c c2 ≤ 1 ∧ not (r == r2 ∧ c == c2)

-- How many positions next to (r, c) hold rolls.
def neighbours (grid: Grid) (cells: Cells) (r: Nat) (c: Nat): Nat :=
  countPositions grid (r2 c2 => adjacent r c r2 c2 ∧ cells r2 c2 == Roll)

-- Position (r, c) holds a roll that a forklift can access.
def accessible (grid: Grid) (cells: Cells) (r: Nat) (c: Nat): Bool :=
  cells r c == Roll ∧ neighbours grid cells r c < 4

-- Part 1: the accessible rolls.
def part1Spec (grid: Grid): Nat := countPositions grid (r c => accessible grid (cellsOf grid) r c)

-- The rolls on the grid.
def rollCount (grid: Grid) (cells: Cells): Nat := countPositions grid (r c => cells r c == Roll)

-- One round: every accessible roll is removed, all at once.
def removeAccessible (grid: Grid) (cells: Cells): Cells :=
  r c => if accessible grid cells r c then Floor else cells r c

-- n rounds.
def rounds (grid: Grid) (n: Nat) (cells: Cells): Cells := Nat.iterate n (removeAccessible grid) cells

-- Part 2: the rolls removed by as many rounds as there are rolls.
def part2Spec (grid: Grid): Nat :=
  let start := rollCount grid (cellsOf grid)
  start - rollCount grid (rounds grid start (cellsOf grid))
