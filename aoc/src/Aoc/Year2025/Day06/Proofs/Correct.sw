-- Day 6, proved end to end: for every input, both printed answers are the
-- puzzle's grand totals as Spec/Spec.sw states them (`part1Correct`,
-- `part2Correct`, at the bottom). The argument:
--   1. The program's columns are the worksheet's columns cell by cell
--      (`columnsAre`: the library's `List.transposeFill` reads line l,
--      column c as `charAt l c`).
--   2. Splitting the columns at the blank ones gives exactly the problems the
--      spec finds by their column numbers (`blocksTotal`, from the library's
--      `List.splitByRuns`; column `gridWidth` is blank, which closes the last).
--   3. Each block, transposed again, reads the same numbers and operator as
--      the spec reads from the cells (`blockRows`, `blockColumns`,
--      `blockOperator`); part 2's right-to-left order doesn't change a sum or
--      a product (`evaluateReverse`).
-- No precondition: the spec says what happens on any input.

namespace Aoc.Year2025.Day06.Proofs
import Aoc.Year2025.Day06 (..)
import Aoc.Year2025.Day06.Spec (..)
import Std (Bool, Eq, List, Nat, Option, Text)

-- The spec's problem test is the library's maximal run of non-blank columns.
theorem isProblemRun (lines: List Text) (lo: Nat) (hi: Nat): isProblem lines lo hi = Nat.isRun (c => blank lines c) lo hi := rfl

-- The program's columns are the worksheet's columns, cell by cell.
theorem columnsAre (lines: List Text):
    List.transposeFill (List.map lines Text.toList) ' ' = (List.range (gridWidth lines)).map (column lines) :=
  rewrite List.transposeFillColumns (List.map lines Text.toList) ' ', List.mapMap lines (.getOr _ ' ') Text.toList

-- Past a bound on every line's length, every column is blank.
theorem blankPast (w: Nat): (lines: List Text) → ((r: Nat) → List.length (List.getOr (List.map lines Text.toList) r Nil) ≤ w) → blank lines w = True
  | Nil, h => rfl
  | Cons l rest, h => rewrite List.getOrPast (Text.toList l) w ' ' (h 0) in blankPast w rest (r => h (Succ r))

-- One problem's block of columns, as the program reads it, against the
-- spec's reading of the same cells. `Cons c cs` are the problem's columns.
theorem blockRows (lines: List Text) (c: Nat) (cs: List Nat):
    (parseProblem ((Cons c cs).map (column lines))).rowNumbers = lines.init.map (line => parseNumber ((Cons c cs).map (charAt line))) :=
  rewrite List.transposeGrid cs c lines (x line => charAt line x), List.initMap lines (line => (Cons c cs).map (charAt line)) in
    List.mapMap lines.init parseNumber (line => (Cons c cs).map (charAt line))

theorem blockColumns (lines: List Text) (cs: List Nat):
    (parseProblem (cs.map (column lines))).columnNumbers = cs.map (c => parseNumber (column lines.init c)) :=
  rewrite List.mapMap cs (column => parseNumber column.init) (column lines), List.initMap lines (line => charAt line _)

-- The operator under column c.
theorem columnOperator (lines: List Text) (c: Nat):
    (column lines c).last.flatMap Operator.parse = lines.last.flatMap (bottom => Operator.parse (charAt bottom c)) :=
  rewrite List.lastMap lines (line => charAt line c) in Option.flatMapMap lines.last Operator.parse (line => charAt line c)

theorem blockOperator (lines: List Text) (cs: List Nat):
    (parseProblem (cs.map (column lines))).operator = (cs.filterMap (c => lines.last.flatMap (bottom => Operator.parse (charAt bottom c)))).head :=
  rewrite List.findMapIsHeadFilterMap (cs.map (column lines)) (column => column.last.flatMap Operator.parse),
    List.filterMapMap cs (column => column.last.flatMap Operator.parse) (column lines),
    columnOperator lines _

-- Adding and multiplying don't mind the order.
theorem evaluateReverse: (op: Option Operator) → (xs: List Nat) → evaluate op (List.reverse xs) = evaluate op xs
  | None, xs => rfl
  | Some Add, xs => List.sumReverse xs
  | Some Multiply, xs => List.productReverse xs

-- A problem has at least one column.
theorem problemWide (lines: List Text) (lo: Nat) (hi: Nat) (h: isProblem lines lo hi = True): lo < hi :=
  omega

-- The columns of a problem start with its first.
theorem problemColumns (lo: Nat) (hi: Nat) (h: lo < hi): List.rangeFrom (hi - lo) lo = Cons lo (List.rangeFrom (hi - Succ lo) (Succ lo)) :=
  rewrite (omega: hi - lo = Succ (hi - Succ lo))

-- What the program adds up for one block, part 1 and part 2.
def blockAnswer1 (b: List (List Char)): Nat := evaluate (parseProblem b).operator (parseProblem b).rowNumbers

def blockAnswer2 (b: List (List Char)): Nat := evaluate (parseProblem b).operator (parseProblem b).columnNumbers

-- The block of a problem in columns lo .. hi - 1.
def blockOf (lines: List Text) (lo: Nat) (hi: Nat): List (List Char) :=
  (List.rangeFrom (hi - lo) lo).map (column lines)

theorem answer1 (lines: List Text) (lo: Nat) (hi: Nat):
    (b: Bool) → isProblem lines lo hi = b →
    Nat.keepIf (blockAnswer1 (blockOf lines lo hi)) b = Nat.keepIf (evaluate (operatorOf lines lo hi) (rowNumbers lines lo hi)) b
  | False, h => rfl
  | True, h =>
    rewrite problemColumns lo hi (problemWide lines lo hi h),
      blockOperator lines (Cons lo (List.rangeFrom (hi - Succ lo) (Succ lo))),
      blockRows lines lo (List.rangeFrom (hi - Succ lo) (Succ lo))

theorem answer2 (lines: List Text) (lo: Nat) (hi: Nat):
    (b: Bool) → isProblem lines lo hi = b →
    Nat.keepIf (blockAnswer2 (blockOf lines lo hi)) b = Nat.keepIf (evaluate (operatorOf lines lo hi) (columnNumbers lines lo hi)) b
  | False, h => rfl
  | True, h =>
    rewrite blockOperator lines (List.rangeFrom (hi - lo) lo),
      blockColumns lines (List.rangeFrom (hi - lo) lo),
      List.mapReverse (List.rangeFrom (hi - lo) lo) (c => parseNumber (column lines.init c)),
      evaluateReverse (operatorOf lines lo hi) ((List.rangeFrom (hi - lo) lo).map (c => parseNumber (column lines.init c)))

-- The program's total over the blocks is the total over the problems the
-- spec finds, for any way `answer` scores a block.
theorem blocksTotal (lines: List Text) (answer: List (List Char) → Nat):
    List.sumBy (blocks lines) answer
      = List.sumBy (List.range (gridWidth lines))
        (lo => List.sumBy (List.range (gridWidth lines + 1)) (hi => Nat.keepIf (answer (blockOf lines lo hi)) (isProblem lines lo hi))) :=
  rewrite Nat.addOne (gridWidth lines), columnsAre lines in
    List.splitByRuns isBlank (column lines) (blank lines) (c => rfl) answer (gridWidth lines)
      (blankPast (gridWidth lines) lines (r => List.lengthLeMaxLength (List.map lines Text.toList) r))

theorem term1 (lines: List Text) (lo: Nat) (hi: Nat):
    Nat.keepIf (blockAnswer1 (blockOf lines lo hi)) (isProblem lines lo hi)
      = (if isProblem lines lo hi then evaluate (operatorOf lines lo hi) (rowNumbers lines lo hi) else 0) :=
  rewrite Nat.ifKeep (evaluate (operatorOf lines lo hi) (rowNumbers lines lo hi)) (isProblem lines lo hi) in
    answer1 lines lo hi (isProblem lines lo hi) rfl

theorem term2 (lines: List Text) (lo: Nat) (hi: Nat):
    Nat.keepIf (blockAnswer2 (blockOf lines lo hi)) (isProblem lines lo hi)
      = (if isProblem lines lo hi then evaluate (operatorOf lines lo hi) (columnNumbers lines lo hi) else 0) :=
  rewrite Nat.ifKeep (evaluate (operatorOf lines lo hi) (columnNumbers lines lo hi)) (isProblem lines lo hi) in
    answer2 lines lo hi (isProblem lines lo hi) rfl

-- Part 1 is right: for every input, the printed answer is the puzzle's grand
-- total with the numbers read along the rows.
theorem part1Correct (lines: List Text): solvePart1 (parseWorksheet lines) = part1Spec lines :=
  calc solvePart1 (parseWorksheet lines)
    _ = _ := List.sumByMap (blocks lines) ((p: Problem) => evaluate p.operator p.rowNumbers) parseProblem
    _ = _ := blocksTotal lines blockAnswer1
    _ = part1Spec lines := rewrite term1 lines _ _

-- Part 2 is right: the same, with the numbers read down the columns, right
-- to left.
theorem part2Correct (lines: List Text): solvePart2 (parseWorksheet lines) = part2Spec lines :=
  calc solvePart2 (parseWorksheet lines)
    _ = _ := List.sumByMap (blocks lines) ((p: Problem) => evaluate p.operator p.columnNumbers) parseProblem
    _ = _ := blocksTotal lines blockAnswer2
    _ = part2Spec lines := rewrite term2 lines _ _
