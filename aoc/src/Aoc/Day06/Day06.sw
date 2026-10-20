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
-- The puzzle input is not in git (aoc/inputs/ is ignored).
--
-- The lines are padded with spaces to the same length (editors trim the
-- trailing ones), turned into columns, and split into blocks at the blank
-- columns. Each block gives a problem its operator and both readings.
--
-- That the grid is padded rectangular and the blocks are the runs of columns
-- that aren't blank is proved in `Aoc.Day06.Proofs` (Proofs/Grid.sw), which
-- `run` does not check.

namespace Aoc.Day06

def main(): {IO} () :=
  let problems := parseWorksheet (IO.readAllLines())
  IO.print "Part 1: ${solvePart1 problems}"
  IO.print "Part 2: ${solvePart2 problems}"

type Operator =
  | Add
  | Multiply

-- A problem's numbers as read by each part, and its operator (none if the
-- block has no + or *).
type Problem = { operator: Maybe Operator, rowNumbers: List Nat, columnNumbers: List Nat }

def example: List Text :=
  [ "123 328  51 64 ", " 45 64  387 23 ", "  6 98  215 314", "*   +   *   +  " ]

def parseWorksheet (lines: List Text): List Problem := (blocks lines).map parseProblem

def isBlank (column: List Char): Bool := column.all Char.isSpace

test "blank column" := isBlank [' ', ' '] && not (isBlank [' ', '7'])

-- The blocks of columns that make the problems: the runs of columns that
-- aren't blank.
def blocks (lines: List Text): List (List (List Char)) := (paddedGrid lines).transpose.splitBy isBlank

-- Every line, padded with spaces on the right to the longest line's length.
def paddedGrid (lines: List Text): List (List Char) :=
  lines.map (line => line.toList.padRight (gridWidth lines) ' ')

def gridWidth (lines: List Text): Nat := lines.foldLeft widen 0

def widen (width: Nat) (line: Text): Nat := Nat.max width line.length

test "grid width" := gridWidth ["ab", "abcd", "a"] == 4
test "padded grid" := paddedGrid ["ab", "a"] == [['a', 'b'], ['a', ' ']]

-- One block of columns, the last character of each being the operator row.
def parseProblem (columns: List (List Char)): Problem :=
  let rows := columns.transpose
  { operator = (columns.mapMaybe (column => column.last.andThen Operator.parse)).get 0
  , rowNumbers = (rows.take (rows.length - 1)).map readNumber
  , columnNumbers = columns.map (column => readNumber (column.take (column.length - 1))) }

test "example problems" :=
  (parseWorksheet example).map (p => (p.rowNumbers, p.columnNumbers))
    == [ ([123, 45, 6], [1, 24, 356]), ([328, 64, 98], [369, 248, 8])
       , ([51, 387, 215], [32, 581, 175]), ([64, 23, 314], [623, 431, 4]) ]
test "example operators" :=
  (parseWorksheet example).map (p => p.operator) == [Just Multiply, Just Add, Just Multiply, Just Add]
test "no operator" := (parseWorksheet ["1", "2", " "]).map (p => p.operator) == [Nothing]

def Operator.parse: Char -> Maybe Operator
  | '+' => Just Add
  | '*' => Just Multiply
  | _   => Nothing

-- The number written with these digits; spaces (and anything else) are skipped.
def readNumber (cells: List Char): Nat := Nat.fromDigits (cells.mapMaybe Char.digitValue)

test "read number" := (readNumber [' ', '4', '5'], readNumber ['3', ' ', ' '], readNumber [' ']) == (45, 3, 0)

def Operator.apply: Operator -> List Nat -> Nat
  | Add,      numbers => numbers.sum
  | Multiply, numbers => numbers.product

-- A problem without an operator has no answer; count it as 0.
def evaluate (operator: Maybe Operator) (numbers: List Nat): Nat :=
  match operator with
    | Nothing => 0
    | Just op => op.apply numbers

-- Part 1: the answers of the problems read by rows.
def solvePart1 (problems: List Problem): Nat := problems.sumBy (p => evaluate p.operator p.rowNumbers)

test "example part 1" := solvePart1 (parseWorksheet example) == 4277556

-- Part 2: the answers of the problems read by columns.
def solvePart2 (problems: List Problem): Nat := problems.sumBy (p => evaluate p.operator p.columnNumbers)

test "example part 2" := solvePart2 (parseWorksheet example) == 3263827
test "no problems" := (solvePart1 [], solvePart2 []) == (0, 0)
