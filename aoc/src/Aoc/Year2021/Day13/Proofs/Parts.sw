--| Every fold, and the two answers: part 1 is the number of dots after the
--| first fold, and part 2's picture shows the dots after all of them.

namespace Aoc.Year2021.Day13.Proofs
import Aoc.Common (Point)
import Aoc.Year2021.Day13 (..)
import Aoc.Year2021.Day13.Spec (..)
import Std (Exists, List)

--| Folding a list that holds the dots, fold after fold, holds the dots
--| after the folds, if the promise is kept...
theorem foldsHold (folds: List Fold) (dots: List Point) (marked: Point → Prop) (holds: Holds dots marked) (promise: Promise folds marked):
    Holds (folds.foldLeft dots foldOnce) (AfterFolds folds marked) := match folds with
      | [] => spot => holds spot
      | [fold, ..rest] => spot =>
        foldsHold rest (foldOnce dots fold) (AfterFold fold marked) (foldOnceHolds dots marked fold holds promise.left) promise.right spot

--| ...and lists each dot once, as every fold drops repeats.
theorem foldsDistinct (folds: List Fold) (dots: List Point) (distinct: List.Distinct dots): List.Distinct (folds.foldLeft dots foldOnce) :=
  match folds with
    | [] => distinct
    | [fold, ..rest] => foldsDistinct rest (foldOnce dots fold) (List.distinctUnique (dots.map (foldDot fold)))

--| `foldAll` holds the dots after the folds, each once.
theorem foldAllHolds (folds: List Fold) (dots: List Point) (promise: Promise folds (Listed dots)): Holds (foldAll folds dots) (AfterFolds folds (Listed dots)) :=
  foldsHold folds dots.unique (Listed dots) (spot => List.memUnique spot dots) promise

theorem foldAllDistinct (folds: List Fold) (dots: List Point): List.Distinct (foldAll folds dots) :=
  foldsDistinct folds dots.unique (List.distinctUnique dots)

--| The promise for every fold is the promise for the first.
theorem promiseFirst (folds: List Fold) (marked: Point → Prop) (promise: Promise folds marked): Promise (folds.take 1) marked :=
  match folds with
    | [] => Trivial
    | [fold, ..rest] => Both promise.left Trivial

--| Part 1: the answer is the number of dots after the first fold (if there
--| is no fold, of the dots listed).
theorem part1Correct (paper: Paper) (promise: Promise (paper.folds.take 1) (Listed paper.dots)):
    DotCount (AfterFolds (paper.folds.take 1) (Listed paper.dots)) (solvePart1 paper) :=
  Witness (foldAll (paper.folds.take 1) paper.dots)
    (Both (foldAllDistinct (paper.folds.take 1) paper.dots) (Both (foldAllHolds (paper.folds.take 1) paper.dots promise) rfl))

--| Part 2: the picture shows the dots after every fold.
theorem part2Correct (paper: Paper) (promise: Promise paper.folds (Listed paper.dots)): Shows (solvePart2 paper) (AfterFolds paper.folds (Listed paper.dots)) :=
  renderShows (foldAll paper.folds paper.dots) (AfterFolds paper.folds (Listed paper.dots)) (foldAllHolds paper.folds paper.dots promise)
