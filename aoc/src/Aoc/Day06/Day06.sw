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
-- wording read cell by cell, in `Aoc.Day06.Spec` (Spec/Spec.sw,
-- Proofs/Correct.sw; the columns' shape in Proofs/Grid.sw), and the tests are
-- in `Aoc.Day06.Tests` (Tests/); `run` checks neither.

namespace Aoc.Day06
import Std (Char, Fail, IO, Nat, Text)

def main(): {IO, Fail} () :=
  let problems := (checkWorksheet IO.readAllLines()).orFail
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
  {
    operator = (columns.filterMap (.last.flatMap Operator.parse)).head,
    rowNumbers = rows.init.map readNumber,
    columnNumbers = columns.map (column => readNumber column.init)
  }

def Operator.parse: Char -> Option Operator
  | '+' => Some Add
  | '*' => Some Multiply
  | _ => None

-- The number written with these digits; spaces (and anything else) are skipped.
def readNumber (cells: List Char): Nat := Nat.fromDigits (cells.filterMap .digitValue)

def Operator.apply: Operator -> List Nat -> Nat
  | Add, numbers => numbers.sum
  | Multiply, numbers => numbers.product

-- A problem without an operator has no answer; count it as 0.
def evaluate (operator: Option Operator) (numbers: List Nat): Nat := operator.fold 0 (op => op.apply numbers)

-- Part 1: the answers of the problems read by rows.
def solvePart1 (problems: List Problem): Nat := problems.sumBy (problem => evaluate problem.operator problem.rowNumbers)

-- Part 2: the answers of the problems read by columns.
def solvePart2 (problems: List Problem): Nat := problems.sumBy (problem => evaluate problem.operator problem.columnNumbers)

-- The strict reader `main` uses. `parseWorksheet` is total and forgiving (it
-- skips a stray character in a number, takes the first operator of a block,
-- counts a block without one as 0); `checkWorksheet` refuses a worksheet that
-- isn't well formed and otherwise gives exactly `parseWorksheet lines`
-- (`Aoc.Day06.Proofs.checkWorksheetParses`), so the proofs about the parser
-- describe what is printed. Well formed means:
--   - at least two lines: number rows, then the operator row;
--   - the number rows hold only digits and spaces, the operator row only + *
--     and spaces (lines and columns count from 1 in the messages);
--   - one operator under each block of columns.
-- Trailing blank lines are rejected, not skipped: the operator row is the last
-- line, so an extra blank line would leave it without operators, and the
-- message says so. Short lines (trailing spaces trimmed) are fine.
def checkWorksheet (lines: List Text): Result (List Problem) Text :=
  match worksheetError lines with
    | Some message => Err message
    | None => Ok (parseWorksheet lines)

-- The first thing wrong with the worksheet, if anything.
def worksheetError (lines: List Text): Option Text :=
  if lines.length < 2 then
    Some "expected number rows followed by an operator row, got ${lines.length} lines"
  else if (lines.last.map .trim) == Some "" then
    Some "line ${lines.length}: expected the operator row, got a blank line"
  else
    (lines.init.withIndex.findMap (((index, row)) => characterError (index + 1) "a digit" isDigit row))
      |> .orElse (lines.last.flatMap (row => characterError lines.length "+ or *" isOperator row))
      |> .orElse (blockError lines)

def isDigit (ch: Char): Bool := ch.digitValue.isSome

def isOperator (ch: Char): Bool := (Operator.parse ch).isSome

-- The first character of the row that is neither a space nor allowed.
def characterError (lineNumber: Nat) (expected: Text) (allowed: Char -> Bool) (row: Text): Option Text :=
  row.toList.withIndex.findMap (((index, ch)) =>
    if ch == ' ' || allowed ch then None
    else Some "line ${lineNumber}, column ${index + 1}: expected ${expected} or a space, got '${ch}'")

-- The first block of columns without exactly one operator, named by the
-- column it starts at. Needs the rows to hold only operators and spaces.
def blockError (lines: List Text): Option Text :=
  (lines.map .toList).transposeFill ' ' |> .withIndex |> .splitBy (indexed => isBlank indexed.snd)
    |> .findMap (block =>
      let operators := block.count (indexed => (indexed.snd.last.flatMap Operator.parse).isSome)
      let start := block.headOr (0, []) |> (indexed => indexed.fst + 1)
      if operators == 1 then None
      else if operators == 0 then Some "the problem starting at column ${start} has no operator"
      else Some "the problem starting at column ${start} has ${operators} operators, expected one")
