-- Advent of Code 2024, day 4: a word search of the letters X, M, A and S.
-- Part 1 counts every XMAS, in any of the eight directions; part 2 counts the
-- X-MAS crosses, an A at the centre of two MAS on the diagonals.
--
--   $ cd aoc && stitchwort run Aoc.Year2024.Day04.main < inputs/2024/day04.txt
--
-- The grid is a list of rows of letters. Every line of four cells is four
-- lists read side by side: a row and itself shifted by one, two and three
-- columns (across), or four rows in a run, as they are (down) or each shifted
-- one column further than the last (the two diagonals). `List.zipWith4` reads
-- them in step and stops at the shortest, so a line that would leave the grid
-- is never read. Crosses are found the same way, in three rows and three
-- columns.
--
-- The proofs are in `Aoc.Year2024.Day04.Proofs` (Proofs/) and the tests in
-- `Aoc.Year2024.Day04.Tests` (Tests/); `run` checks neither.

namespace Aoc.Year2024.Day04
import Std (IO, List, Nat, Text)

-- The rows of the word search, top to bottom, letter by letter.
type Grid = { rows: List (List Char) }

def main(): {IO} () :=
  let grid := parseGrid IO.readAllLines()
  IO.print "Part 1: ${solvePart1 grid}"
  IO.print "Part 2: ${solvePart2 grid}"

-- One row per line. Any character is a letter of the search, and rows may
-- differ in length.
def parseGrid (lines: List Text): Grid := { rows = lines.map Text.toList }

-- Four letters in a line spell XMAS, one way or the other.
def spellsXmas (first: Char) (second: Char) (third: Char) (fourth: Char): Bool :=
  (first == 'X' ∧ second == 'M' ∧ third == 'A' ∧ fourth == 'S') ∨ (first == 'S' ∧ second == 'A' ∧ third == 'M' ∧ fourth == 'X')

-- The lines of four that spell XMAS, taking one cell from each list at the
-- same index.
def countXmas (first: List Char) (second: List Char) (third: List Char) (fourth: List Char): Nat :=
  List.zipWith4 first second third fourth spellsXmas |> .count (found => found)

-- Across one row: four cells side by side.
def countAcross (row: List Char): Nat := countXmas row (row.drop 1) (row.drop 2) (row.drop 3)

-- Through four rows in a run: straight down, down to the right, and down to
-- the left.
def countThrough (first: List Char) (second: List Char) (third: List Char) (fourth: List Char): Nat :=
  countXmas first second third fourth
    + countXmas first (second.drop 1) (third.drop 2) (fourth.drop 3)
    + countXmas (first.drop 3) (second.drop 2) (third.drop 1) fourth

-- Part 1: every XMAS across a row or through a run of four rows.
def solvePart1 (grid: Grid): Nat :=
  let rows := grid.rows
  let through := List.zipWith4 rows (rows.drop 1) (rows.drop 2) (rows.drop 3) countThrough |> .sum
  rows.sumBy countAcross + through

-- The two ends of a diagonal of a cross are an M and an S.
def isMas (oneEnd: Char) (otherEnd: Char): Bool := (oneEnd == 'M' ∧ otherEnd == 'S') ∨ (oneEnd == 'S' ∧ otherEnd == 'M')

-- Three columns of three cells (top, middle, bottom) are an X-MAS: an A in
-- the centre and MAS along both diagonals.
def isCross (left: (Char, Char, Char)) (centre: (Char, Char, Char)) (right: (Char, Char, Char)): Bool :=
  let (topLeft, _, bottomLeft) := left
  let (_, middle, _) := centre
  let (topRight, _, bottomRight) := right
  middle == 'A' ∧ isMas topLeft bottomRight ∧ isMas topRight bottomLeft

-- The crosses in three rows in a run: their columns, three at a time.
def countCrosses (above: List Char) (middle: List Char) (below: List Char): Nat :=
  let columns := List.zipWith3 above middle below (top centre bottom => (top, centre, bottom))
  List.zipWith3 columns (columns.drop 1) (columns.drop 2) isCross |> .count (found => found)

-- Part 2: the crosses in every run of three rows.
def solvePart2 (grid: Grid): Nat :=
  let rows := grid.rows
  List.zipWith3 rows (rows.drop 1) (rows.drop 2) countCrosses |> .sum
