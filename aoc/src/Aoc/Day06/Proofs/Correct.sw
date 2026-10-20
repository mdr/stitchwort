namespace Aoc.Day06.Proofs
import Aoc.Day06 (..)
import Std (Eq)

theorem isProblemRun (lines: List Text) (lo: Nat) (hi: Nat): isProblem lines lo hi = PNat.isRun (\c => blank lines c) lo hi := rfl

-- Padded to width w, each line is its first w columns.
theorem paddedCells (w: Nat): (lines: List Text) -> Fits w lines ->
    List.map (\line => List.padRight w ' ' (Text.toList line)) lines = List.map (\line => List.map (charAt line) (List.range w)) lines
  | Nil,         fits          => rfl
  | Cons l rest, Both fit fits =>
    calc Cons (List.padRight w ' ' (Text.toList l)) (List.map (\line => List.padRight w ' ' (Text.toList line)) rest)
      _ = Cons (List.map (\c => List.getOr ' ' c (List.padRight w ' ' (Text.toList l))) (List.range (List.length (List.padRight w ' ' (Text.toList l)))))
               (List.map (\line => List.map (charAt line) (List.range w)) rest)
          := rewrite PList.mapGetOr ' ' (List.padRight w ' ' (Text.toList l)), paddedCells w rest fits
      _ = Cons (List.map (charAt l) (List.range w)) (List.map (\line => List.map (charAt line) (List.range w)) rest)
          := rewrite List.padRightLength w ' ' (Text.toList l) fit,
               List.mapCongr (\c => List.getOr ' ' c (List.padRight w ' ' (Text.toList l))) (charAt l)
                 (\c => PList.getOrPadRight ' ' w c (Text.toList l)) (List.range w)

-- The program's columns are the worksheet's columns, cell by cell.
theorem columnsAre: (lines: List Text) ->
    List.transpose (paddedGrid lines) = List.map (\c => List.map (\line => charAt line c) lines) (List.range (gridWidth lines))
  | Nil         => rfl
  | Cons l rest =>
    calc List.transpose (paddedGrid (Cons l rest))
      _ = List.transpose (List.map (\line => List.map (charAt line) (List.range (gridWidth (Cons l rest)))) (Cons l rest))
          := Eq.cong List.transpose (paddedCells (gridWidth (Cons l rest)) (Cons l rest) (foldWidenFits 0 (Cons l rest)))
      _ = List.map (\c => List.map (\line => charAt line c) (Cons l rest)) (List.range (gridWidth (Cons l rest)))
          := PList.transposeGrid charAt l rest (List.range (gridWidth (Cons l rest)))

-- Past the widest line, every column is blank.
theorem blankPast (w: Nat): (lines: List Text) -> Fits w lines -> blank lines w = True
  | Nil,         fits          => rfl
  | Cons l rest, Both fit fits => rewrite PList.getOrPast ' ' w (Text.toList l) fit in blankPast w rest fits

-- One problem's block of columns, as the program reads it, against the
-- spec's reading of the same cells. `Cons c cs` are the problem's columns.
theorem blockRows (lines: List Text) (c: Nat) (cs: List Nat):
    (parseProblem (List.map (\x => List.map (\line => charAt line x) lines) (Cons c cs))).rowNumbers
      = List.map (\line => readNumber (List.map (\x => charAt line x) (Cons c cs))) (List.init lines) :=
  calc List.map readNumber (List.init (List.transpose (List.map (\x => List.map (\line => charAt line x) lines) (Cons c cs))))
    _ = List.map readNumber (List.init (List.map (\line => List.map (\x => charAt line x) (Cons c cs)) lines))
        := rewrite PList.transposeGrid (\x line => charAt line x) c cs lines
    _ = List.map (\line => readNumber (List.map (\x => charAt line x) (Cons c cs))) (List.init lines)
        := rewrite PList.initMap (\line => List.map (\x => charAt line x) (Cons c cs)) lines,
             PList.mapMap readNumber (\line => List.map (\x => charAt line x) (Cons c cs)) (List.init lines)

theorem blockColumns (lines: List Text) (cs: List Nat):
    (parseProblem (List.map (\x => List.map (\line => charAt line x) lines) cs)).columnNumbers
      = List.map (\x => readNumber (List.map (\line => charAt line x) (List.init lines))) cs :=
  calc List.map (\column => readNumber (List.init column)) (List.map (\x => List.map (\line => charAt line x) lines) cs)
    _ = List.map (\x => readNumber (List.init (List.map (\line => charAt line x) lines))) cs
        := PList.mapMap (\column => readNumber (List.init column)) (\x => List.map (\line => charAt line x) lines) cs
    _ = List.map (\x => readNumber (List.map (\line => charAt line x) (List.init lines))) cs
        := List.mapCongr (\x => readNumber (List.init (List.map (\line => charAt line x) lines))) (\x => readNumber (List.map (\line => charAt line x) (List.init lines)))
             (\x => rewrite PList.initMap (\line => charAt line x) lines) cs

theorem blockOperator (lines: List Text) (cs: List Nat):
    (parseProblem (List.map (\x => List.map (\line => charAt line x) lines) cs)).operator
      = List.head (List.mapMaybe (\x => Maybe.andThen (\bottom => Operator.parse (charAt bottom x)) (List.last lines)) cs) :=
  calc List.head (List.mapMaybe (\column => Maybe.andThen Operator.parse (List.last column)) (List.map (\x => List.map (\line => charAt line x) lines) cs))
    _ = List.head (List.mapMaybe (\x => Maybe.andThen Operator.parse (List.last (List.map (\line => charAt line x) lines))) cs)
        := rewrite PList.mapMaybeMap (\column => Maybe.andThen Operator.parse (List.last column)) (\x => List.map (\line => charAt line x) lines) cs
    _ = List.head (List.mapMaybe (\x => Maybe.andThen (\bottom => Operator.parse (charAt bottom x)) (List.last lines)) cs)
        := rewrite PList.mapMaybeCongr (\x => Maybe.andThen Operator.parse (List.last (List.map (\line => charAt line x) lines)))
                     (\x => Maybe.andThen (\bottom => Operator.parse (charAt bottom x)) (List.last lines))
                     (\x => rewrite PList.lastMap (\line => charAt line x) lines, PMaybe.andThenMap Operator.parse (\line => charAt line x) (List.last lines))
                     cs

-- Adding and multiplying don't mind the order.
theorem evaluateReverse: (op: Maybe Operator) -> (xs: List Nat) -> evaluate op (List.reverse xs) = evaluate op xs
  | Nothing,       xs => rfl
  | Just Add,      xs => PList.sumReverse xs
  | Just Multiply, xs => PList.productReverse xs

-- A problem has at least one column.
theorem problemWide (lines: List Text) (lo: Nat) (hi: Nat) (h: isProblem lines lo hi = True): lo < hi :=
  rewrite <- Bool.decTrueToBool (Nat.leq (Succ lo) hi) in
    Bool.andLeft (lo < hi) (List.all (\c => not (blank lines c)) (List.rangeFrom (hi - lo) lo) && blank lines hi)
      (Bool.andRight (lo == 0 || blank lines (lo - 1)) (lo < hi && (List.all (\c => not (blank lines c)) (List.rangeFrom (hi - lo) lo) && blank lines hi)) h)

-- The columns of a problem start with its first.
theorem problemColumns (lo: Nat) (hi: Nat) (h: lo < hi): List.rangeFrom (hi - lo) lo = Cons lo (List.rangeFrom (hi - Succ lo) (Succ lo)) :=
  rewrite Nat.subSuccRight lo hi h

-- What the program adds up for one block, part 1 and part 2.
def blockAnswer1 (b: List (List Char)): Nat := evaluate (parseProblem b).operator (parseProblem b).rowNumbers

def blockAnswer2 (b: List (List Char)): Nat := evaluate (parseProblem b).operator (parseProblem b).columnNumbers

-- The block of a problem in columns lo .. hi - 1.
def blockOf (lines: List Text) (lo: Nat) (hi: Nat): List (List Char) :=
  List.map (\c => List.map (\line => charAt line c) lines) (List.rangeFrom (hi - lo) lo)

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
      PList.mapReverse (\x => readNumber (List.map (\line => charAt line x) (List.init lines))) (List.rangeFrom (hi - lo) lo),
      evaluateReverse (List.head (List.mapMaybe (\x => Maybe.andThen (\bottom => Operator.parse (charAt bottom x)) (List.last lines)) (List.rangeFrom (hi - lo) lo)))
        (List.map (\x => readNumber (List.map (\line => charAt line x) (List.init lines))) (List.rangeFrom (hi - lo) lo))

-- The program's total over the blocks is the total over the problems the
-- spec finds, for any way `answer` scores a block.
theorem blocksTotal (lines: List Text) (answer: List (List Char) -> Nat):
    List.sumBy answer (blocks lines)
      = List.sumBy (\lo => List.sumBy (\hi => Nat.keepIf (answer (blockOf lines lo hi)) (isProblem lines lo hi)) (List.range (gridWidth lines + 1)))
          (List.range (gridWidth lines)) :=
  rewrite Nat.addOne (gridWidth lines), columnsAre lines in
    PList.splitByRuns isBlank (\c => List.map (\line => charAt line c) lines) (\c => blank lines c) (\c => rfl) answer (gridWidth lines)
      (blankPast (gridWidth lines) lines (foldWidenFits 0 lines))


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
    _ = List.sumBy blockAnswer1 (blocks lines) := List.sumByMap (\(p: Problem) => evaluate p.operator p.rowNumbers) parseProblem (blocks lines)
    _ = List.sumBy (\lo => List.sumBy (\hi => Nat.keepIf (blockAnswer1 (blockOf lines lo hi)) (isProblem lines lo hi)) (List.range (gridWidth lines + 1)))
          (List.range (gridWidth lines)) := blocksTotal lines blockAnswer1
    _ = List.sumBy (\lo => List.sumBy (\hi => if isProblem lines lo hi then evaluate (operatorOf lines lo hi) (rowNumbers lines lo hi) else 0)
          (List.range (gridWidth lines + 1))) (List.range (gridWidth lines)) :=
        List.sumByCongr
          (\lo => List.sumBy (\hi => Nat.keepIf (blockAnswer1 (blockOf lines lo hi)) (isProblem lines lo hi)) (List.range (gridWidth lines + 1)))
          (\lo => List.sumBy (\hi => if isProblem lines lo hi then evaluate (operatorOf lines lo hi) (rowNumbers lines lo hi) else 0) (List.range (gridWidth lines + 1)))
          (\lo => List.sumByCongr
             (\hi => Nat.keepIf (blockAnswer1 (blockOf lines lo hi)) (isProblem lines lo hi))
             (\hi => if isProblem lines lo hi then evaluate (operatorOf lines lo hi) (rowNumbers lines lo hi) else 0)
             (\hi => term1 lines lo hi) (List.range (gridWidth lines + 1)))
          (List.range (gridWidth lines))

-- Part 2 is right: the same, with the numbers read down the columns, right
-- to left.
theorem part2Correct (lines: List Text): solvePart2 (parseWorksheet lines) = part2Spec lines :=
  calc solvePart2 (parseWorksheet lines)
    _ = List.sumBy blockAnswer2 (blocks lines) := List.sumByMap (\(p: Problem) => evaluate p.operator p.columnNumbers) parseProblem (blocks lines)
    _ = List.sumBy (\lo => List.sumBy (\hi => Nat.keepIf (blockAnswer2 (blockOf lines lo hi)) (isProblem lines lo hi)) (List.range (gridWidth lines + 1)))
          (List.range (gridWidth lines)) := blocksTotal lines blockAnswer2
    _ = List.sumBy (\lo => List.sumBy (\hi => if isProblem lines lo hi then evaluate (operatorOf lines lo hi) (columnNumbers lines lo hi) else 0)
          (List.range (gridWidth lines + 1))) (List.range (gridWidth lines)) :=
        List.sumByCongr
          (\lo => List.sumBy (\hi => Nat.keepIf (blockAnswer2 (blockOf lines lo hi)) (isProblem lines lo hi)) (List.range (gridWidth lines + 1)))
          (\lo => List.sumBy (\hi => if isProblem lines lo hi then evaluate (operatorOf lines lo hi) (columnNumbers lines lo hi) else 0) (List.range (gridWidth lines + 1)))
          (\lo => List.sumByCongr
             (\hi => Nat.keepIf (blockAnswer2 (blockOf lines lo hi)) (isProblem lines lo hi))
             (\hi => if isProblem lines lo hi then evaluate (operatorOf lines lo hi) (columnNumbers lines lo hi) else 0)
             (\hi => term2 lines lo hi) (List.range (gridWidth lines + 1)))
          (List.range (gridWidth lines))
