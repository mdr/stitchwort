-- Day 6, proved end to end: for every input, both printed answers are the
-- puzzle's grand totals as Proofs/Spec.sw states them (`part1Correct`,
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

namespace Aoc.Day06.Proofs
import Aoc.Day06 (..)
import Std (Bool, Eq, List, Nat, Option, Text)

-- The spec's problem test is the library's maximal run of non-blank columns.
theorem isProblemRun (lines: List Text) (lo: Nat) (hi: Nat): isProblem lines lo hi = Nat.isRun (c => blank lines c) lo hi := rfl

-- The program's columns are the worksheet's columns, cell by cell.
theorem columnsAre (lines: List Text):
    List.transposeFill ' ' (List.map Text.toList lines) = List.map (c => List.map (line => charAt line c) lines) (List.range (gridWidth lines)) :=
  Eq.trans (List.transposeFillColumns ' ' (List.map Text.toList lines))
    (List.mapCong _ _ (List.range (gridWidth lines)) (c => List.mapMap (List.getOr ' ' c) Text.toList lines))

-- Past a bound on every line's length, every column is blank.
theorem blankPast (w: Nat): (lines: List Text) -> ((r: Nat) -> List.length (List.getOr Nil r (List.map Text.toList lines)) <= w) -> blank lines w = True
  | Nil,         h => rfl
  | Cons l rest, h => rewrite List.getOrPast ' ' w (Text.toList l) (h 0) in blankPast w rest (r => h (Succ r))

-- One problem's block of columns, as the program reads it, against the
-- spec's reading of the same cells. `Cons c cs` are the problem's columns.
theorem blockRows (lines: List Text) (c: Nat) (cs: List Nat):
    (parseProblem (List.map (x => List.map (line => charAt line x) lines) (Cons c cs))).rowNumbers
      = List.map (line => readNumber (List.map (x => charAt line x) (Cons c cs))) (List.init lines) :=
  calc List.map readNumber (List.init (List.transpose (List.map (x => List.map (line => charAt line x) lines) (Cons c cs))))
    _ = List.map readNumber (List.init (List.map (line => List.map (x => charAt line x) (Cons c cs)) lines))
        := rewrite List.transposeGrid (x line => charAt line x) c cs lines
    _ = List.map (line => readNumber (List.map (x => charAt line x) (Cons c cs))) (List.init lines)
        := rewrite List.initMap (line => List.map (x => charAt line x) (Cons c cs)) lines,
             List.mapMap readNumber (line => List.map (x => charAt line x) (Cons c cs)) (List.init lines)

theorem blockColumns (lines: List Text) (cs: List Nat):
    (parseProblem (List.map (x => List.map (line => charAt line x) lines) cs)).columnNumbers
      = List.map (x => readNumber (List.map (line => charAt line x) (List.init lines))) cs :=
  calc List.map (column => readNumber (List.init column)) (List.map (x => List.map (line => charAt line x) lines) cs)
    _ = List.map (x => readNumber (List.init (List.map (line => charAt line x) lines))) cs
        := List.mapMap (column => readNumber (List.init column)) (x => List.map (line => charAt line x) lines) cs
    _ = List.map (x => readNumber (List.map (line => charAt line x) (List.init lines))) cs
        := List.mapCong (x => readNumber (List.init (List.map (line => charAt line x) lines))) (x => readNumber (List.map (line => charAt line x) (List.init lines)))
             cs (x => rewrite List.initMap (line => charAt line x) lines)

theorem blockOperator (lines: List Text) (cs: List Nat):
    (parseProblem (List.map (x => List.map (line => charAt line x) lines) cs)).operator
      = List.head (List.filterMap (x => Option.flatMap (bottom => Operator.parse (charAt bottom x)) (List.last lines)) cs) :=
  calc List.head (List.filterMap (column => Option.flatMap Operator.parse (List.last column)) (List.map (x => List.map (line => charAt line x) lines) cs))
    _ = List.head (List.filterMap (x => Option.flatMap Operator.parse (List.last (List.map (line => charAt line x) lines))) cs)
        := rewrite List.filterMapMap (column => Option.flatMap Operator.parse (List.last column)) (x => List.map (line => charAt line x) lines) cs
    _ = List.head (List.filterMap (x => Option.flatMap (bottom => Operator.parse (charAt bottom x)) (List.last lines)) cs)
        := rewrite List.filterMapCong (x => Option.flatMap Operator.parse (List.last (List.map (line => charAt line x) lines)))
                     (x => Option.flatMap (bottom => Operator.parse (charAt bottom x)) (List.last lines))
                     cs
                     (x => rewrite List.lastMap (line => charAt line x) lines, Option.flatMapMap Operator.parse (line => charAt line x) (List.last lines))

-- Adding and multiplying don't mind the order.
theorem evaluateReverse: (op: Option Operator) -> (xs: List Nat) -> evaluate op (List.reverse xs) = evaluate op xs
  | None,       xs => rfl
  | Some Add,      xs => List.sumReverse xs
  | Some Multiply, xs => List.productReverse xs

-- A problem has at least one column.
theorem problemWide (lines: List Text) (lo: Nat) (hi: Nat) (h: isProblem lines lo hi = True): lo < hi :=
  rewrite <- Bool.decTrueToBool (Nat.leq (Succ lo) hi) in
    Bool.andLeft (lo < hi) (List.all (c => not (blank lines c)) (List.rangeFrom (hi - lo) lo) && blank lines hi)
      (Bool.andRight (lo == 0 || blank lines (lo - 1)) (lo < hi && (List.all (c => not (blank lines c)) (List.rangeFrom (hi - lo) lo) && blank lines hi)) h)

-- The columns of a problem start with its first.
theorem problemColumns (lo: Nat) (hi: Nat) (h: lo < hi): List.rangeFrom (hi - lo) lo = Cons lo (List.rangeFrom (hi - Succ lo) (Succ lo)) :=
  rewrite Nat.subSuccRight lo hi h

-- What the program adds up for one block, part 1 and part 2.
def blockAnswer1 (b: List (List Char)): Nat := evaluate (parseProblem b).operator (parseProblem b).rowNumbers

def blockAnswer2 (b: List (List Char)): Nat := evaluate (parseProblem b).operator (parseProblem b).columnNumbers

-- The block of a problem in columns lo .. hi - 1.
def blockOf (lines: List Text) (lo: Nat) (hi: Nat): List (List Char) :=
  List.map (c => List.map (line => charAt line c) lines) (List.rangeFrom (hi - lo) lo)

theorem answer1 (lines: List Text) (lo: Nat) (hi: Nat):
    (b: Bool) -> isProblem lines lo hi = b ->
    Nat.keepIf (blockAnswer1 (blockOf lines lo hi)) b = Nat.keepIf (evaluate (operatorOf lines lo hi) (rowNumbers lines lo hi)) b
  | False, h => rfl
  | True,  h =>
    rewrite problemColumns lo hi (problemWide lines lo hi h),
      blockOperator lines (Cons lo (List.rangeFrom (hi - Succ lo) (Succ lo))),
      blockRows lines lo (List.rangeFrom (hi - Succ lo) (Succ lo))

theorem answer2 (lines: List Text) (lo: Nat) (hi: Nat):
    (b: Bool) -> isProblem lines lo hi = b ->
    Nat.keepIf (blockAnswer2 (blockOf lines lo hi)) b = Nat.keepIf (evaluate (operatorOf lines lo hi) (columnNumbers lines lo hi)) b
  | False, h => rfl
  | True,  h =>
    rewrite blockOperator lines (List.rangeFrom (hi - lo) lo),
      blockColumns lines (List.rangeFrom (hi - lo) lo),
      List.mapReverse (x => readNumber (List.map (line => charAt line x) (List.init lines))) (List.rangeFrom (hi - lo) lo),
      evaluateReverse (List.head (List.filterMap (x => Option.flatMap (bottom => Operator.parse (charAt bottom x)) (List.last lines)) (List.rangeFrom (hi - lo) lo)))
        (List.map (x => readNumber (List.map (line => charAt line x) (List.init lines))) (List.rangeFrom (hi - lo) lo))

-- The program's total over the blocks is the total over the problems the
-- spec finds, for any way `answer` scores a block.
theorem blocksTotal (lines: List Text) (answer: List (List Char) -> Nat):
    List.sumBy answer (blocks lines)
      = List.sumBy (lo => List.sumBy (hi => Nat.keepIf (answer (blockOf lines lo hi)) (isProblem lines lo hi)) (List.range (gridWidth lines + 1)))
          (List.range (gridWidth lines)) :=
  rewrite Nat.addOne (gridWidth lines), columnsAre lines in
    List.splitByRuns isBlank (c => List.map (line => charAt line c) lines) (c => blank lines c) (c => rfl) answer (gridWidth lines)
      (blankPast (gridWidth lines) lines (r => List.lengthLeMaxLength r (List.map Text.toList lines)))


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
    _ = _ := List.sumByMap ((p: Problem) => evaluate p.operator p.rowNumbers) parseProblem (blocks lines)
    _ = _ := blocksTotal lines blockAnswer1
    _ = part1Spec lines := List.sumByCong _ _ (List.range (gridWidth lines)) (lo => List.sumByCong _ _ (List.range (gridWidth lines + 1)) (hi => term1 lines lo hi))

-- Part 2 is right: the same, with the numbers read down the columns, right
-- to left.
theorem part2Correct (lines: List Text): solvePart2 (parseWorksheet lines) = part2Spec lines :=
  calc solvePart2 (parseWorksheet lines)
    _ = _ := List.sumByMap ((p: Problem) => evaluate p.operator p.columnNumbers) parseProblem (blocks lines)
    _ = _ := blocksTotal lines blockAnswer2
    _ = part2Spec lines := List.sumByCong _ _ (List.range (gridWidth lines)) (lo => List.sumByCong _ _ (List.range (gridWidth lines + 1)) (hi => term2 lines lo hi))
