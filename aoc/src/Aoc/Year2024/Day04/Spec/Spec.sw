-- Day 4 as the puzzle states it, position by position, for the proofs in
-- Proofs/.
--
-- In plain words:
--   - Row r of the grid is the r-th line (from 0), and its letters are
--     columns 0, 1, 2, ... of it. A position off the grid holds no letter.
--   - "This word search allows words to be horizontal, vertical, diagonal,
--     written backwards, or even overlapping other words": from a position,
--     a word runs in one of eight directions, each a step of -1, 0 or +1 in
--     the row and in the column, but not both 0.
--   - Part 1, "how many times does XMAS appear?": the starting positions and
--     directions from which the letters spell XMAS.
--   - Part 2, "two MAS in the shape of an X ... each MAS can be written
--     forwards or backwards": the positions at the centre of a MAS from top
--     left to bottom right and of a MAS from top right to bottom left, each
--     either way round.

namespace Aoc.Year2024.Day04.Spec
import Aoc.Year2024.Day04 (..)
import Std (Bool, List, Nat, Option)

-- The letter at row r and column c, or `None` off the grid.
def letterAt (grid: Grid) (r: Nat) (c: Nat): Option Char := grid.rows.getOr r [] |> .get c

-- One step along the rows or the columns.
type Step =
  | Back
  | Stay
  | Ahead

-- A direction: a step down the rows and a step along the columns.
type Direction = { down: Step, across: Step }

-- Every direction but staying put.
def directions: List Direction := [
  { down = Back, across = Back },
  { down = Back, across = Stay },
  { down = Back, across = Ahead },
  { down = Stay, across = Back },
  { down = Stay, across = Ahead },
  { down = Ahead, across = Back },
  { down = Ahead, across = Stay },
  { down = Ahead, across = Ahead }
]

-- `distance` steps from `start`; `None` before 0.
def moved (start: Nat) (step: Step) (distance: Nat): Option Nat :=
  match step with
    | Back => if distance ≤ start then Some (start - distance) else None
    | Stay => Some start
    | Ahead => Some (start + distance)

-- The letter `distance` steps from row r, column c in `direction`.
def letterAlong (grid: Grid) (r: Nat) (c: Nat) (direction: Direction) (distance: Nat): Option Char :=
  match moved r direction.down distance, moved c direction.across distance with
    | Some row, Some column => letterAt grid row column
    | _, _ => None

-- The letters from row r, column c in `direction` spell `word`.
def spells (word: List Char) (grid: Grid) (r: Nat) (c: Nat) (direction: Direction): Bool :=
  List.range word.length |> .all (distance => letterAlong grid r c direction distance == word.get distance)

-- How many positions (r, c) of the grid satisfy `p`: every column of every
-- row.
def countPositions (grid: Grid) (p: Nat → Nat → Nat): Nat :=
  List.range grid.rows.length |> .sumBy (r => List.range (grid.rows.getOr r []).length |> .sumBy (c => p r c))

-- Part 1: every position and direction where XMAS starts.
def part1Spec (grid: Grid): Nat :=
  countPositions grid (r c => directions.count (spells ['X', 'M', 'A', 'S'] grid r c))

-- The letters one step from row r, column c towards `start`, at it, and one
-- step towards `end` spell MAS, one way or the other.
def masThrough (grid: Grid) (r: Nat) (c: Nat) (start: Direction) (end: Direction): Bool :=
  let letters := [letterAlong grid r c start 1, letterAt grid r c, letterAlong grid r c end 1]
  letters == [Some 'M', Some 'A', Some 'S'] ∨ letters == [Some 'S', Some 'A', Some 'M']

-- Row r, column c is the centre of an X-MAS: a MAS from top left to bottom
-- right, and one from top right to bottom left.
def crossAt (grid: Grid) (r: Nat) (c: Nat): Bool :=
  masThrough grid r c { down = Back, across = Back } { down = Ahead, across = Ahead }
    ∧ masThrough grid r c { down = Back, across = Ahead } { down = Ahead, across = Back }

-- Part 2: the centres of X-MAS.
def part2Spec (grid: Grid): Nat := countPositions grid (r c => Bool.toNat (crossAt grid r c))
