-- Advent of Code 2025, day 4: a grid of paper rolls (@) and empty floor (.).
-- A roll is accessible when fewer than four of its eight neighbours are
-- rolls. Part 1 counts the accessible rolls. Part 2 removes them, repeats
-- until none are accessible, and counts every roll removed.
--
--   $ cd aoc && stitchwort run Aoc.Day04.main < inputs/day04.txt
--
-- The puzzle input is committed in aoc/inputs/ (D119).
--
-- The grid is a list of rows of cells, each a roll or floor. A roll's "window"
-- is the 3 by 3 block around it, itself included, so it is accessible when its
-- window holds fewer than 5 rolls. For each row, add it to the rows above and
-- below column by column, then walk along it with each column's sum and its
-- neighbours' (`peelRow`).
--
-- Part 1 is proved right for every rectangular grid in `Aoc.Day04.Proofs`
-- (Proofs/Spec.sw, Proofs/Part1.sw), which `run` does not check.

namespace Aoc.Day04

type Cell =
  | Roll
  | Floor

-- How many rolls a cell holds.
def Cell.count: Cell -> Nat
  | Roll  => 1
  | Floor => 0

type Grid = List (List Cell)

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
test "lone roll" := (solvePart1 [[Roll]], solvePart2 [[Roll]]) == (1, 1)
test "full square" := (solvePart1 [[Roll, Roll], [Roll, Roll]], solvePart2 [[Roll, Roll], [Roll, Roll]]) == (4, 4)

def plus: Grid := [[Floor, Roll, Floor], [Roll, Roll, Roll], [Floor, Roll, Floor]]

test "plus shape keeps its centre" := (solvePart1 plus, solvePart2 plus) == (4, 5)

def parseGrid (lines: List Text): Grid := lines.map parseLine

def parseLine (line: Text): List Cell := line.toList.map parseChar

def parseChar (ch: Char): Cell := if ch == '@' then Roll else Floor

def Grid.rolls (grid: Grid): Nat := grid |> .sumBy (row => row.sumBy Cell.count)

test "rolls" := (parseGrid example).rolls == 71

-- Remove every accessible roll, all at once: each row sees the rows above
-- and below as they were.
def Grid.round (grid: Grid): Grid :=
  let gap := List.replicate ((grid.headOr []).length) Floor
  roundFrom gap gap grid

-- `above` is the row above the first of `rows`; `gap` stands for the missing
-- row past the bottom.
def roundFrom (gap above: List Cell): Grid -> Grid
  | Nil           => Nil
  | Cons row rest => Cons (peelRow above row (rest.headOr gap)) (roundFrom gap row rest)

-- Remove the accessible rolls of one row, given the rows above and below:
-- add the three rows column by column, then walk along the row with each
-- column's sum and its neighbours' (the window of 3 by 3 cells).
def peelRow (above row below: List Cell): List Cell :=
  peelCells 0 (List.zipWith3 (a r b => a.count + r.count + b.count) above row below) row

-- `left` is the column sum before the first of `columns`.
def peelCells (left: Nat): List Nat -> List Cell -> List Cell
  | Cons here columns, Cons roll rolls =>
    let window := left + here + columns.headOr 0
    Cons (if roll == Roll && 5 <= window then Roll else Floor) (peelCells here columns rolls)
  | _, _ => Nil
-- A grid whose rows are marked with whether they changed in the last pass.
type Marked = List (List Cell, Bool)

-- Like `round`, but going down the grid, each row sees the row above it
-- after its rolls were removed. Removing a roll never stops another from
-- being accessible, so the end state is the same as with `round`, reached in
-- fewer passes. A row is only looked at again when it or a neighbour changed
-- since it was last looked at; the rest are passed over.
def sweep (grid: Marked): Marked :=
  let width := (grid.headOr ([], False)).fst.length
  sweepFrom (List.replicate width Floor) False grid

-- `above` is the (already swept) row above the first row of the grid, and
-- `aboveChanged` says whether this pass changed it.
def sweepFrom (above: List Cell) (aboveChanged: Bool): Marked -> Marked
  | Nil                   => Nil
  | Cons (row, moved) rest =>
    let (below, belowMoved) := rest.headOr (List.replicate row.length Floor, False)
    if moved || belowMoved || aboveChanged then
      let swept := peelRow above row below
      let changed := not (swept == row)
      Cons (swept, changed) (sweepFrom swept changed rest)
    else
      Cons (row, False) (sweepFrom row False rest)

-- Sweep until a pass changes nothing. Every pass that changes something
-- removes a roll, so as many passes as there are rolls is enough.
def Grid.settle (grid: Grid) (rolls: Nat): Grid :=
  (settleMarked (grid.map (row => (row, True))) rolls).map Pair.fst

def settleMarked (grid: Marked): Nat -> Marked
  | Zero   => grid
  | Succ n =>
    let next := sweep grid
    if next.any Pair.snd then settleMarked next n else next

