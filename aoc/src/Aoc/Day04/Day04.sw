-- Advent of Code 2025, day 4: a grid of paper rolls (@) and empty floor (.).
-- A roll is accessible when fewer than four of its eight neighbours are
-- rolls. Part 1 counts the accessible rolls. Part 2 removes them, repeats
-- until none are accessible, and counts every roll removed.
--
--   $ cd aoc && stitchwort run Aoc.Day04.main < inputs/day04.txt
--
-- The puzzle input is not in git (aoc/inputs/ is ignored).
--
-- The grid is a list of rows of 0 (floor) and 1 (roll). A roll's "window" is
-- the 3 by 3 block around it, itself included, so it is accessible when its
-- window holds fewer than 5 rolls. Sum each row horizontally in threes once,
-- then add the sums of the rows above, at, and below to get every window.

namespace Aoc.Day04

type Grid = List (List Nat)

def main(): {IO} () :=
  let grid := parseGrid (IO.readAllLines())
  IO.print "Part 1: ${solvePart1 grid}"
  IO.print "Part 2: ${solvePart2 grid}"

-- Part 1: the rolls one round removes.
def solvePart1 (grid: Grid): Nat := grid.rolls - grid.round.rolls

-- Part 2: the rolls removed by rounds until none is accessible.
def solvePart2 (grid: Grid): Nat := grid.rolls - (grid.settle grid.rolls).rolls

def example: List Text :=
  [ "..@@.@@@@.", "@@@.@.@.@@", "@@@@@.@.@@", "@.@@@@..@.", "@@.@@@@.@@",
    ".@@@@@@@.@", ".@.@.@.@@@", "@.@@@.@@@@", ".@@@@@@@@.", "@.@.@@@.@." ]

test "example" := (solvePart1 (parseGrid example), solvePart2 (parseGrid example)) == (13, 43)
test "lone roll" := (solvePart1 [[1]], solvePart2 [[1]]) == (1, 1)
test "full square" := (solvePart1 [[1, 1], [1, 1]], solvePart2 [[1, 1], [1, 1]]) == (4, 4)

def plus: Grid := [[0, 1, 0], [1, 1, 1], [0, 1, 0]]

test "plus shape keeps its centre" := (solvePart1 plus, solvePart2 plus) == (4, 5)

def parseGrid (lines: List Text): Grid := lines.map parseLine

def parseLine (line: Text): List Nat := line.toList.map parseChar

-- A roll is 1, floor is 0.
def parseChar: Char -> Nat
  | '@' => 1
  | _   => 0

def Grid.rolls (grid: Grid): Nat := grid |> .sumBy List.sum

test "rolls" := (parseGrid example).rolls == 71

-- Remove every accessible roll, all at once.
def Grid.round (grid: Grid): Grid :=
  let sums := grid.map rowSums
  let gap := List.replicate ((grid.headOr []).length) 0
  let above := Cons gap sums
  let below := sums.drop 1 |> .append [gap]
  let windows := Grid.zipWith Nat.add (Grid.zipWith Nat.add above sums) below
  Grid.zipWith (roll window => if roll == 1 && 5 <= window then 1 else 0) grid windows

-- Remove the accessible rolls of one row, given the rows above and below:
-- add the three rows column by column, then walk along the row with each
-- column's sum and its neighbours' (the window of 3 by 3 cells).
def peelRow (above row below: List Nat): List Nat :=
  peelCells 0 (List.zipWith3 (\a r b => a + r + b) above row below) row

-- `left` is the column sum before the first of `columns`.
def peelCells (left: Nat): List Nat -> List Nat -> List Nat
  | Cons here columns, Cons roll rolls =>
    let window := left + here + columns.headOr 0
    Cons (if roll == 1 && 5 <= window then 1 else 0) (peelCells here columns rolls)
  | _, _ => Nil
-- A grid whose rows are marked with whether they changed in the last pass.
type Marked = List (List Nat, Bool)

-- Like `round`, but going down the grid, each row sees the row above it
-- after its rolls were removed. Removing a roll never stops another from
-- being accessible, so the end state is the same as with `round`, reached in
-- fewer passes. A row is only looked at again when it or a neighbour changed
-- since it was last looked at; the rest are passed over.
def sweep (grid: Marked): Marked :=
  let width := (grid.headOr ([], False)).fst.length
  sweepFrom (List.replicate width 0) False grid

-- `above` is the (already swept) row above the first row of the grid, and
-- `aboveChanged` says whether this pass changed it.
def sweepFrom (above: List Nat) (aboveChanged: Bool): Marked -> Marked
  | Nil                   => Nil
  | Cons (row, moved) rest =>
    let (below, belowMoved) := rest.headOr (List.replicate row.length 0, False)
    if moved || belowMoved || aboveChanged then
      let swept := peelRow above row below
      let changed := not (swept == row)
      Cons (swept, changed) (sweepFrom swept changed rest)
    else
      Cons (row, False) (sweepFrom row False rest)

-- Sweep until a pass changes nothing. Every pass that changes something
-- removes a roll, so as many passes as there are rolls is enough.
def Grid.settle (grid: Grid) (rolls: Nat): Grid :=
  (settleMarked (grid.map (\row => (row, True))) rolls).map Pair.fst

def settleMarked (grid: Marked): Nat -> Marked
  | Zero   => grid
  | Succ n =>
    let next := sweep grid
    if next.any Pair.snd then settleMarked next n else next


-- Each cell becomes the sum of itself and its left and right neighbours.
def rowSums (row: List Nat): List Nat :=
  let left := Cons 0 row
  let right := row.drop 1 |> .append [0]
  List.zipWith Nat.add (List.zipWith Nat.add left row) right

test "row sums" := rowSums [1, 0, 1, 1] == [1, 2, 2, 2]

-- Combine two grids of the same shape cell by cell.
def Grid.zipWith (f: Nat -> Nat -> Nat) (a b: Grid): Grid := List.zipWith (List.zipWith f) a b
