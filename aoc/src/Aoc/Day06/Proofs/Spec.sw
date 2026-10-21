-- Day 6 as the puzzle states it, cell by cell, for the end-to-end proofs in
-- Proofs/Correct.sw. Nothing here transposes or splits: a problem is found by
-- the column numbers where it starts and stops, and its numbers are read from
-- the cells at those positions.
--
-- In plain words:
--   - The worksheet is the input's lines. Column c of a line is its c-th
--     character, or a space past its end (editors trim trailing spaces, and
--     the real input's last line is one short).
--   - The last line holds the operators; the others hold the numbers.
--   - "Problems are separated by a full column of only spaces": columns
--     lo .. hi - 1 are one problem when column lo - 1 is blank (or lo is the
--     left edge), there is at least one column, none of them is blank, and
--     column hi is blank. Past the widest line every column is blank, so that
--     covers the right edge too.
--   - The problem's operator is the + or * in the last line under it.
--   - Part 1: each number line, read across the problem's columns, is one
--     number ("the left/right alignment of numbers within each problem can be
--     ignored": spaces are skipped).
--   - Part 2: "cephalopod math is written right-to-left in columns": each
--     column, from the rightmost, is one number, its digits read from the
--     top line down.
--   - The grand total adds up every problem's answer.
--
-- Shared with the program: `readNumber` (the digits of some cells, spaces
-- skipped, as a number; `readNumberWritten` below shows a number written with
-- spaces around it reads back as itself), `evaluate` (+ adds, * multiplies; a
-- problem with no operator, which the puzzle never has, counts 0),
-- `Operator.parse` and `gridWidth` (the widest line's length: only a bound on
-- where problems can be).

namespace Aoc.Day06.Proofs
import Aoc.Day06 (..)

-- Column c of a line; a space past its end.
def charAt (line: Text) (c: Nat): Char := line.toList.getOr ' ' c

-- Column c of the worksheet, top to bottom.
def column (lines: List Text) (c: Nat): List Char := lines.map (line => charAt line c)

-- A full column of only spaces.
def blank (lines: List Text) (c: Nat): Bool := (column lines c).all Char.isSpace

-- Columns lo .. hi - 1 hold one problem.
def isProblem (lines: List Text) (lo: Nat) (hi: Nat): Bool :=
  (lo == 0 || blank lines (lo - 1)) && (lo < hi && ((List.rangeFrom (hi - lo) lo).all (c => not (blank lines c)) && blank lines hi))

-- The lines with numbers in them: all but the last.
def numberLines (lines: List Text): List Text := lines.init

-- The + or * under the problem in the last line (the first, if there are several).
def operatorOf (lines: List Text) (lo: Nat) (hi: Nat): Option Operator :=
  (List.rangeFrom (hi - lo) lo).filterMap (c => lines.last.flatMap (bottom => Operator.parse (charAt bottom c))) |> .head

-- Part 1: each number line, read across the problem's columns.
def rowNumbers (lines: List Text) (lo: Nat) (hi: Nat): List Nat :=
  (numberLines lines).map (line => readNumber ((List.rangeFrom (hi - lo) lo).map (c => charAt line c)))

-- Part 2: each of the problem's columns, right to left, read top to bottom.
def columnNumbers (lines: List Text) (lo: Nat) (hi: Nat): List Nat :=
  (List.rangeFrom (hi - lo) lo).reverse.map (c => readNumber ((numberLines lines).map (line => charAt line c)))

-- The answers of all the problems, added up.
def grandTotal (lines: List Text) (answer: Nat -> Nat -> Nat): Nat :=
  List.range (gridWidth lines) |> .sumBy (lo =>
    List.range (gridWidth lines + 1) |> .sumBy (hi => if isProblem lines lo hi then answer lo hi else 0))

def part1Spec (lines: List Text): Nat := grandTotal lines (lo hi => evaluate (operatorOf lines lo hi) (rowNumbers lines lo hi))

def part2Spec (lines: List Text): Nat := grandTotal lines (lo hi => evaluate (operatorOf lines lo hi) (columnNumbers lines lo hi))

test "spec on the example" := (part1Spec example, part2Spec example) == (4277556, 3263827)
test "spec problem columns" := isProblem example 0 3 && isProblem example 12 15 && not (isProblem example 0 2) && not (isProblem example 1 3)
test "spec numbers" := (rowNumbers example 4 7, columnNumbers example 4 7, operatorOf example 4 7) == ([328, 64, 98], [8, 248, 369], Some Add)

-- Why `readNumber` is the right reading: a number written in decimal, with
-- any spaces before and after it (its alignment in the problem), reads back
-- as itself.
theorem spacesNoDigits: (k: Nat) -> List.filterMap Char.digitValue (List.replicate k ' ') = Nil
  | Zero   => rfl
  | Succ k => spacesNoDigits k

theorem readNumberWritten (n: Nat) (before: Nat) (after: Nat):
    readNumber (List.append (List.replicate before ' ') (List.append (Text.toList (Nat.toText n)) (List.replicate after ' '))) = n :=
  rewrite List.filterMapAppend Char.digitValue (List.replicate before ' ') (List.append (Text.toList (Nat.toText n)) (List.replicate after ' ')),
    List.filterMapAppend Char.digitValue (Text.toList (Nat.toText n)) (List.replicate after ' '),
    spacesNoDigits before, spacesNoDigits after, Char.toTextDigits n, List.appendNil (Nat.digits n) in
      Nat.fromDigitsDigits n
