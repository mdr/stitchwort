-- Advent of Code 2025, day 6: a worksheet of column problems. The input is a
-- grid of characters: rows of numbers, then a row of operators (+ or *).
-- Each problem is a block of columns, and a column of only spaces separates
-- two problems. The operator under a block says whether to add or multiply
-- the problem's numbers; the answer is the sum of all the problems' results.
-- Part 1 reads each row of a block as one number. Part 2 reads each column
-- of a block as one number, its digits top to bottom (a cephalopod reads the
-- columns right to left, but adding and multiplying don't mind the order).
--
--   $ cd aoc && stitchwort run Aoc.Day06.main < inputs/day06.txt
--
-- The puzzle input is committed in aoc/inputs/ (D119).
--
-- The lines are turned into columns, a short line read as ending in spaces
-- (editors trim the trailing ones), and split into blocks at the blank
-- columns. Each block gives a problem its operator and both readings.
--
-- Both answers are proved right for every input, against the puzzle's own
-- wording read cell by cell, in `Aoc.Day06.Proofs` (Proofs/Spec.sw,
-- Proofs/Correct.sw; the columns' shape in Proofs/Grid.sw), and the tests are
-- in `Aoc.Day06.Tests` (Tests/); `run` checks neither.

namespace Aoc.Day06
import Std (Char, IO, Nat, Text)

def main(): {IO} () :=
  let problems := parseWorksheet IO.readAllLines()
  IO.print "Part 1: ${solvePart1 problems}"
  IO.print "Part 2: ${solvePart2 problems}"

type Operator =
  | Add
  | Multiply

-- A problem's numbers as read by each part, and its operator (none if the
-- block has no + or *).
type Problem = { operator: Option Operator, rowNumbers: List Nat, columnNumbers: List Nat }

def parseWorksheet (lines: List Text): List Problem := (blocks lines).map parseProblem

def isBlank (column: List Char): Bool := column.all .isSpace

-- The blocks of columns that make the problems: the runs of columns that
-- aren't blank. A short line reads as spaces past its end, and there are as
-- many columns as the longest line is long.
def blocks (lines: List Text): List (List (List Char)) :=
  (lines.map .toList).transposeFill ' ' |> .splitBy isBlank

-- One block of columns, the last character of each being the operator row.
def parseProblem (columns: List (List Char)): Problem :=
  let rows := columns.transpose
  { operator = (columns.filterMap (.last.flatMap Operator.parse)).head
  , rowNumbers = rows.init.map readNumber
  , columnNumbers = columns.map (column => readNumber column.init) }

def Operator.parse: Char -> Option Operator
  | '+' => Some Add
  | '*' => Some Multiply
  | _   => None

-- The number written with these digits; spaces (and anything else) are skipped.
def readNumber (cells: List Char): Nat := Nat.fromDigits (cells.filterMap .digitValue)

def Operator.apply: Operator -> List Nat -> Nat
  | Add,      numbers => numbers.sum
  | Multiply, numbers => numbers.product

-- A problem without an operator has no answer; count it as 0.
def evaluate (operator: Option Operator) (numbers: List Nat): Nat :=
  match operator with
    | None => 0
    | Some op => op.apply numbers

-- Part 1: the answers of the problems read by rows.
def solvePart1 (problems: List Problem): Nat := problems.sumBy (p => evaluate p.operator p.rowNumbers)

-- Part 2: the answers of the problems read by columns.
def solvePart2 (problems: List Problem): Nat := problems.sumBy (p => evaluate p.operator p.columnNumbers)
