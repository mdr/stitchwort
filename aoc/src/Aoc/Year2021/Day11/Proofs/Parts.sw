--| Both answers are the spec's. Part 1: the program's run of 100 steps is
--| a `Run`, and every `Run` is the program's, so the answer is the only
--| one. Part 2: if the program answers `n`, every octopus flashes in step
--| n and in no earlier step; if it answers nothing, no step up to
--| `syncLimit` has every octopus flash.

namespace Aoc.Year2021.Day11.Proofs
import Aoc.Year2021.Day11 (..)
import Aoc.Year2021.Day11.Spec (..)
import Aoc.Common (Position)
import Std (Bool, Eq, Exists, List, Nat, Option, Stream, Void)

--| The cavern at position `k` of `afterSteps` is the one after step k + 1.
theorem afterStepsAt ∀ (cavern: Cavern) (k: Nat): cavern.afterSteps.at k = (Nat.iterate k Cavern.step cavern).step :=
  Nat.iterateSuccLast Cavern.step k cavern

--| The flashes in one step more: the first step's, then the rest's.
theorem flashesInSucc ∀ (cavern: Cavern) (steps: Nat):
    cavern.flashesIn (Succ steps) = cavern.step.zeros + cavern.step.flashesIn steps :=
  calc cavern.flashesIn (Succ steps)
    _ = [cavern.step, ..cavern.step.afterSteps.take steps].sumBy Cavern.zeros :=
      Eq.cong (xs => xs.sumBy Cavern.zeros) (Stream.iterateTakeSucc Cavern.step cavern.step steps)
    _ = cavern.step.zeros + cavern.step.flashesIn steps :=
      List.sumByCons (cavern.step.afterSteps.take steps) cavern.step Cavern.zeros

--| The program's steps are a run...
theorem programRun ∀ (steps: Nat) (cavern: Cavern):
    Run cavern steps (Nat.iterate steps Cavern.step cavern) (cavern.flashesIn steps) :=
  match steps with
    | Zero => Start cavern
    | Succ steps =>
      let flashed := cavern.flashers.has
      let spec := flashersCorrect cavern
      let rest: Run
        (after cavern flashed)
        steps
        (Nat.iterate steps Cavern.step cavern.step)
        (cavern.step.flashesIn steps) :=
        Eq.subst
          (start => Run start steps (Nat.iterate steps Cavern.step cavern.step) (cavern.step.flashesIn steps))
          (stepCorrect cavern flashed spec)
          (programRun steps cavern.step)
      Eq.subst
        (total => Run cavern (Succ steps) (Nat.iterate steps Cavern.step cavern.step) total)
        (totalOfStep cavern flashed spec steps _
          (Eq.cong (next => next.flashesIn steps) (stepCorrect cavern flashed spec)))
        (Step flashed spec rest)

--| A run's flashes, one step from `cavern` and then the rest's `total`,
--| are the program's when the rest's are.
theorem totalOfStep ∀ (cavern: Cavern) (flashed: Position → Bool)
    (spec: Flashers cavern flashed) (steps total: Nat)
    (rest: total = (after cavern flashed).flashesIn steps):
    flashCount cavern flashed + total = cavern.flashesIn (Succ steps) :=
  calc flashCount cavern flashed + total
    _ = cavern.step.zeros + cavern.step.flashesIn steps :=
      Eq.cong2
        (x y => x + y)
        (zerosCorrect cavern flashed spec).flipped
        (rest.trans (Eq.cong (next => next.flashesIn steps) (stepCorrect cavern flashed spec).flipped))
    _ = cavern.flashesIn (Succ steps) := (flashesInSucc cavern steps).flipped

--| ...and every run is the program's.
theorem runIsProgram ∀ [cavern: Cavern] [steps: Nat] [final: Cavern] [total: Nat]
    (run: Run cavern steps final total):
    final = Nat.iterate steps Cavern.step cavern ∧ total = cavern.flashesIn steps :=
  match run with
    | Start _ => Both byComputing byComputing
    | Step flashed spec rest =>
      let (Both finalSame totalSame) := runIsProgram rest
      let same: after cavern flashed = cavern.step := (stepCorrect cavern flashed spec).flipped
      Both (rewrite finalSame, same) (totalOfStep cavern flashed spec _ _ totalSame)

--| Part 1: the program's answer is the spec's...
theorem part1Correct ∀ (cavern: Cavern): Part1Answer cavern cavern.solvePart1 :=
  Witness (Nat.iterate 100 Cavern.step cavern) (programRun 100 cavern)

--| ...and the spec has no other.
theorem part1Unique ∀ (cavern: Cavern) (answer: Nat) (spec: Part1Answer cavern answer): answer = cavern.solvePart1 :=
  Exists.elim spec (final run => (runIsProgram run).right)

--| Every octopus flashes in step k + 1 exactly when the program's cavern
--| after it is all 0.
theorem allFlashOfZeros ∀ (cavern: Cavern) (k: Nat)
    (zeros: (Nat.iterate k Cavern.step cavern).step.allZero = True):
    AllFlashIn cavern (Succ k) :=
  let before := Nat.iterate k Cavern.step cavern
  let spec := flashersCorrect before
  let all := rewrite allZeroCorrect before (before.flashers.has) spec at zeros then zeros
  let each := List.allToAll (cell => before.flashers.has cell.fst) before.grid.cells all
  Both
    (arithmetic)
    (Witness before
      (Witness
        (cavern.flashesIn k)
        (Both
          (programRun k cavern)
          (Witness
            (before.flashers.has)
            (Both spec (at level member =>
              List.allMem (cell => before.flashers.has cell.fst = True) (at, level) before.grid.cells each member))))))

theorem zerosOfAllFlash ∀ (cavern: Cavern) (k: Nat)
    (spec: AllFlashIn cavern (Succ k)):
    (Nat.iterate k Cavern.step cavern).step.allZero = True :=
  let (Both _ found) := spec
  Exists.elim found (before rest =>
    Exists.elim rest (total both =>
      let (Both run flashedAll) := both
      let same: before = Nat.iterate k Cavern.step cavern := (runIsProgram run).left
      Exists.elim flashedAll (flashed both =>
        let (Both flashers each) := both
        rewrite <- same, allZeroCorrect before flashed flashers then
          List.allOfAll
            (cell => flashed cell.fst)
            before.grid.cells
            (List.allOfMem (cell => flashed cell.fst = True) before.grid.cells (cell member =>
              match cell with | (at, level) => each at level member)))))

--| Not every octopus flashes in step `number` when, if it is step k + 1,
--| the program's cavern after it is not all 0 (step 0 never counts).
theorem notAllFlash ∀ (cavern: Cavern) (number: Nat)
    (notZero: ∀ (k: Nat) => number = Succ k → cavern.afterSteps.at k |> .allZero = False):
    ¬(AllFlashIn cavern number) :=
  flashes =>
    match number with
      | Zero => arithmetic [flashes.left]
      | Succ k =>
        Bool.falseNotTrue
          (Eq.trans
            (notZero k byComputing).flipped
            (rewrite afterStepsAt cavern k then zerosOfAllFlash cavern k flashes))

--| Part 2: if the program answers, its answer is the first step in which
--| every octopus flashes...
theorem part2Correct ∀ (cavern: Cavern) (answer: Nat)
    (found: cavern.solvePart2 = Some answer):
    Part2Answer cavern answer :=
  Option.mapEqSome (cavern.afterSteps.findIndex syncLimit .allZero) (index => index + 1) answer found (k e same =>
    let (Both _ (Both zeros before)) := Stream.findIndexSome cavern.afterSteps syncLimit k .allZero e
    rewrite <- same then
      Both (allFlashOfZeros cavern k (rewrite <- afterStepsAt cavern k then zeros)) (earlier below =>
        notAllFlash cavern earlier (j sameJ => before j (arithmetic [sameJ, below]))))

--| ...and if it answers nothing, no step up to `syncLimit` is one.
theorem part2None ∀ (cavern: Cavern)
    (none: cavern.solvePart2 = None) (number: Nat)
    (high: number ≤ syncLimit):
    ¬(AllFlashIn cavern number) :=
  let e := (Option.mapEqNone (cavern.afterSteps.findIndex syncLimit .allZero) (index => index + 1)).forward none
  notAllFlash cavern number (j sameJ =>
    Stream.findIndexNone cavern.afterSteps syncLimit .allZero e j (arithmetic [sameJ, high]))
