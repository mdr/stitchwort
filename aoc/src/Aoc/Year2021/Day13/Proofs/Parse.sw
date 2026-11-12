--| The parser keeps the promise the answers' theorems need: in a
--| successful parse, no dot is on a fold's line, or further beyond it
--| than the line is from the near edge, when that fold is made.
-- (D2108)

namespace Aoc.Year2021.Day13.Proofs
import Aoc.Common (Point)
import Aoc.Year2021.Day13 (..)
import Aoc.Year2021.Day13.Spec (..)
import Std (Bool, Eq, Fail, Iff, List, Option, Result, Void)

--| The program's test, `clears`, is the puzzle's promise for one dot.
theorem clearsClear (fold: Fold) (dot: Point) (h: clears fold dot = True): Clear fold dot :=
  cases

--| A list in which `find` found no dot failing the test: each dot passes.
theorem clearOfFind (fold: Fold) (dots: List Point) (none: dots.find (dot => not (clears fold dot)) = None) (dot: Point) (member: dot ∈ dots): Clear fold dot :=
  match e: clears fold dot with
    | True => clearsClear fold dot e
    | False => Void.exfalso (List.findNoneNotMem dots (dot => not (clears fold dot)) dot (rewrite e in rfl) member none)

--| If no fold is blocked, folding a list that holds the dots, the promise
--| is kept for every fold.
theorem unblockedPromise (folds: List Fold) (index: Nat) (dots: List Point) (marked: Point → Prop) (holds: Holds dots marked)
    (none: firstBlockedFrom index dots folds = None): Promise folds marked :=
  match folds with
    | [] => Trivial
    | [fold, ..rest] =>
      match e: dots.find (dot => not (clears fold dot)) with
        | None =>
          let clear := (dot: Point) (isMarked: marked dot) => clearOfFind fold dots e dot ((holds dot).backward isMarked)
          Both clear (unblockedPromise rest (index + 1) (foldOnce dots fold) (AfterFold fold marked) (foldOnceHolds dots marked fold holds clear) none)

--| `checkPaper` gives the paper back, and only if no fold is blocked...
theorem checkPaperOk (paper: Paper) (result: Paper) (h: Fail.toResult (() => checkPaper paper) = Ok result):
    result = paper ∧ firstBlocked paper.dots paper.folds = None :=
  match e: firstBlocked paper.dots paper.folds with
    | Some (index, dot) => Void.exfalso (Result.errNotOk h)
    | None => Both (Eq.sym (Result.okInjective h)) rfl

--| ...whatever reads it.
theorem parsedUnblocked (read: () → {Fail} Paper) (paper: Paper) (parsed: Fail.toResult (() => checkPaper (read ())) = Ok paper):
    firstBlocked paper.dots paper.folds = None :=
  let split := rewrite Fail.toResultThen read checkPaper at parsed
  Result.flatMapEqOk (Fail.toResult read) (x => Fail.toResult (() => checkPaper x)) paper split
    (found _ checked =>
      let (Both same none) := checkPaperOk found paper checked
      rewrite same in none)

--| If `parsePaper` reads `input` as `paper`, the puzzle's promise holds for
--| every fold.
theorem parsePromise (input: Text) (paper: Paper) (parsed: Fail.toResult (() => parsePaper input) = Ok paper): Promise paper.folds (Listed paper.dots) :=
  unblockedPromise paper.folds 0 paper.dots (Listed paper.dots) (spot => Iff.refl (spot ∈ paper.dots)) (parsedUnblocked _ paper parsed)

--| The answers from the input, with no hypothesis but the successful parse.
theorem part1FromInput (input: Text) (paper: Paper) (parsed: Fail.toResult (() => parsePaper input) = Ok paper):
    DotCount (AfterFolds (paper.folds.take 1) (Listed paper.dots)) (solvePart1 paper) :=
  part1Correct paper (promiseFirst paper.folds (Listed paper.dots) (parsePromise input paper parsed))

theorem part2FromInput (input: Text) (paper: Paper) (parsed: Fail.toResult (() => parsePaper input) = Ok paper):
    Shows (solvePart2 paper) (AfterFolds paper.folds (Listed paper.dots)) :=
  part2Correct paper (parsePromise input paper parsed)
