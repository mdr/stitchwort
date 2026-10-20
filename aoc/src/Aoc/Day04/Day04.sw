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
-- to the rows above and below column by column, then walk along it with each
-- column's sum and its neighbours' (`peelRow`).
--
-- Both parts are proved right for every grid in `Aoc.Day04.Proofs`
-- (Proofs/Spec.sw states the puzzle by positions; Proofs/Part1.sw and
-- Proofs/Part2.sw), which `run` does not check.

namespace Aoc.Day04

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
  match parseGrid (IO.readAllLines()) with
    | Nothing   => IO.print "The lines are not all the same length."
    | Just grid =>
      IO.print "Part 1: ${solvePart1 grid}"
      IO.print "Part 2: ${solvePart2 grid}"

-- Part 1: the rolls one round removes.
def solvePart1 (grid: Grid): Nat := grid.rolls - grid.round.rolls

-- Part 2: the rolls removed by rounds until none is accessible.
def solvePart2 (grid: Grid): Nat := grid.rolls - grid.settle.rolls

def example: List Text :=
  [ "..@@.@@@@.", "@@@.@.@.@@", "@@@@@.@.@@", "@.@@@@..@.", "@@.@@@@.@@",
    ".@@@@@@@.@", ".@.@.@.@@@", "@.@@@.@@@@", ".@@@@@@@@.", "@.@.@@@.@." ]

-- Both answers for some lines, if they make a grid.
def answers (lines: List Text): Maybe (Nat, Nat) := Maybe.map (grid => (solvePart1 grid, solvePart2 grid)) (parseGrid lines)

test "example" := answers example == Just (13, 43)
test "lone roll" := answers ["@"] == Just (1, 1)
test "full square" := answers ["@@", "@@"] == Just (4, 4)
test "plus shape keeps its centre" := answers [".@.", "@@@", ".@."] == Just (4, 5)
test "no lines" := answers [] == Just (0, 0)
test "ragged" := answers ["@@", "@"] == Nothing

-- `Nothing` if the lines are not all as long as the first.
def parseGrid (lines: List Text): Maybe Grid :=
  let width := (lines.headOr "").length
  Vec.fromList lines
    |> Vec.traverseMaybe (line => Vec.ofList width (parseLine line))
    |> Maybe.map (rows => ({ height = lines.length, width, rows }: Grid))

def parseLine (line: Text): List Cell := line.toList.map parseChar

def parseChar (ch: Char): Cell := if ch == '@' then Roll else Floor

def Grid.rolls (grid: Grid): Nat := grid.rows.sumBy (row => row.sumBy Cell.count)

test "rolls" := Maybe.map Grid.rolls (parseGrid example) == Just 71

-- Remove every accessible roll, all at once: each row sees the rows above
-- and below as they were.
def Grid.round (grid: Grid): Grid :=
  let gap := Vec.replicate grid.width Floor
  { grid | rows = roundFrom gap gap grid.rows }

-- `above` is the row above the first of `rows`; `gap` stands for the missing
-- row past the bottom.
def roundFrom (gap above: Vec Cell w): Vec (Vec Cell w) h -> Vec (Vec Cell w) h
  | VNil           => VNil
  | VCons row rest => VCons (peelRow above row (rest.headOr gap)) (roundFrom gap row rest)

-- Remove the accessible rolls of one row, given the rows above and below:
-- add the three rows column by column, then walk along the row with each
-- column's sum and its neighbours' (the window of 3 by 3 cells).
def peelRow (above row below: Vec Cell w): Vec Cell w :=
  peelCells 0 (Vec.zipWith3 (a r b => a.count + r.count + b.count) above row below) row

-- `left` is the column sum before the first of `columns`.
def peelCells (left: Nat): Vec Nat w -> Vec Cell w -> Vec Cell w
  | VNil,               VNil            => VNil
  | VCons here columns, VCons roll rolls =>
    let window := left + here + columns.headOr 0
    VCons (if roll == Roll && 5 <= window then Roll else Floor) (peelCells here columns rolls)

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
    if moved || belowMoved || aboveChanged then
      let swept := peelRow above row below
      let changed := not (swept.toList == row.toList)
      VCons (swept, changed) (sweepFrom gap swept changed rest)
    else
      VCons (row, False) (sweepFrom gap row False rest)

-- Sweep until a pass changes nothing. Every pass that changes something
-- removes a roll, so as many passes as there are rolls are enough.
def Grid.settle (grid: Grid): Grid :=
  { grid | rows = Vec.map Pair.fst (settleMarked (grid.rows.map (row => (row, True))) grid.rolls) }

def settleMarked (grid: Marked w h): Nat -> Marked w h
  | Zero   => grid
  | Succ n =>
    let next := sweep grid
    if next.any Pair.snd then settleMarked next n else next

