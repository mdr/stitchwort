--| Both answers are the spec's. Part 1: the program's run of 100 steps is
--| a `Run`, and every `Run` is the program's, so the answer is the only
--| one. Part 2: if the program answers `n`, every octopus flashes in step
--| n and in no earlier step; if it answers nothing, no step up to
--| `syncLimit` has every octopus flash.

namespace Aoc.Year2021.Day11.Proofs
import Aoc.Year2021.Day11 (..)
import Aoc.Year2021.Day11.Spec (..)
import Aoc.Common (Position)
import Std (Bool, Eq, Exists, List, Nat, Option, Void)

--| The program's cavern after `steps` steps.
def stepsFrom (cavern: Cavern): (steps: Nat) → Cavern
  | Zero => cavern
  | Succ more => stepsFrom cavern.step more

theorem stepsFromSucc (steps: Nat) (cavern: Cavern): stepsFrom cavern (Succ steps) = (stepsFrom cavern steps).step :=
  match steps with
    | Zero => rfl
    | Succ steps => stepsFromSucc steps cavern.step

--| The program's steps are a run...
theorem programRun (steps: Nat) (cavern: Cavern): Run cavern steps (stepsFrom cavern steps) (cavern.flashesIn steps) :=
  match steps with
    | Zero => Start cavern
    | Succ steps =>
      let flashed := cavern.flashers.has
      let spec := flashersCorrect cavern
      let rest: Run (after cavern flashed) steps (stepsFrom cavern.step steps) (cavern.step.flashesIn steps) :=
        rewrite <- stepCorrect cavern flashed spec in programRun steps cavern.step
      rewrite zerosCorrect cavern flashed spec in Step flashed spec rest

--| ...and every run is the program's.
theorem runIsProgram [cavern: Cavern] [steps: Nat] [final: Cavern] [total: Nat] (run: Run cavern steps final total):
    final = stepsFrom cavern steps ∧ total = cavern.flashesIn steps :=
  match run with
    | Start _ => Both rfl rfl
    | Step flashed spec rest =>
      let (Both finalSame totalSame) := runIsProgram rest
      let same: after cavern flashed = cavern.step := Eq.sym (stepCorrect cavern flashed spec)
      Both (rewrite finalSame, same in rfl) (rewrite totalSame, same, <- zerosCorrect cavern flashed spec in rfl)

--| Part 1: the program's answer is the spec's...
theorem part1Correct (cavern: Cavern): Part1Answer cavern cavern.solvePart1 :=
  Witness (stepsFrom cavern 100) (programRun 100 cavern)

--| ...and the spec has no other.
theorem part1Unique (cavern: Cavern) (answer: Nat) (spec: Part1Answer cavern answer): answer = cavern.solvePart1 :=
  Exists.elim spec (final run => And.right (runIsProgram run))

--| Every octopus flashes in step k + 1 exactly when the program's cavern
--| after it is all 0.
theorem allFlashOfZeros (cavern: Cavern) (k: Nat)
    (zeros: (stepsFrom cavern k).step.allZero = True): AllFlashIn cavern (Succ k) :=
  let before := stepsFrom cavern k
  let spec := flashersCorrect before
  let all := rewrite allZeroCorrect before (before.flashers.has) spec at zeros in zeros
  let each := List.allToAll (cell => before.flashers.has cell.fst) before.grid.cells all
  Both (omega)
    (Witness before (Witness (cavern.flashesIn k) (Both (programRun k cavern)
      (Witness (before.flashers.has) (Both spec (at level member =>
        List.allMem (cell => before.flashers.has cell.fst = True) (at, level) before.grid.cells each member))))))

theorem zerosOfAllFlash (cavern: Cavern) (k: Nat) (spec: AllFlashIn cavern (Succ k)):
    (stepsFrom cavern k).step.allZero = True :=
  let (Both _ found) := spec
  Exists.elim found (before rest =>
    Exists.elim rest (total both =>
      let (Both run flashedAll) := both
      let same: before = stepsFrom cavern k := And.left (runIsProgram run)
      Exists.elim flashedAll (flashed both =>
        let (Both flashers each) := both
        rewrite <- same, allZeroCorrect before flashed flashers in
          List.allOfAll (cell => flashed cell.fst) before.grid.cells
            (List.allOfMem (cell => flashed cell.fst = True) before.grid.cells (cell member =>
              match cell with
                | (at, level) => each at level member)))))

--| The search from step k + 1, with no step up to k an all-flash step.
theorem syncFound (cavern: Cavern) (answer: Nat) (m k: Nat)
    (noneBefore: (∀ (earlier: Nat) => earlier < Succ k → ¬(AllFlashIn cavern earlier)))
    (found: (stepsFrom cavern k).firstSync (Succ k) m = Some answer): Part2Answer cavern answer :=
  match m with
    | Succ m =>
      match e: (stepsFrom cavern k).step.allZero with
        | True =>
          let same: Succ k = answer := Option.someInjective found
          rewrite <- same in Both (allFlashOfZeros cavern k e) noneBefore
        | False =>
          syncFound cavern answer m (Succ k)
            (earlier below flashes =>
              if early: Succ earlier ≤ Succ k then noneBefore earlier early flashes
              else
                let same: earlier = Succ k := omega
                Bool.falseNotTrue (Eq.trans (Eq.sym e) (zerosOfAllFlash cavern k (rewrite same at flashes in flashes))))
            (rewrite stepsFromSucc k cavern in found)

--| Part 2: if the program answers, its answer is the first step in which
--| every octopus flashes...
theorem part2Correct (cavern: Cavern) (answer: Nat) (found: cavern.solvePart2 = Some answer): Part2Answer cavern answer :=
  syncFound cavern answer syncLimit 0 (earlier below flashes => Void.exfalso (omega [And.left flashes])) found

--| The search from step k + 1 finding nothing in m steps.
theorem syncNone (cavern: Cavern): ∀ (m k: Nat) => (stepsFrom cavern k).firstSync (Succ k) m = None →
    ∀ (number: Nat) => Succ k ≤ number → number ≤ k + m → ¬(AllFlashIn cavern number)
  | Zero, k, none, number, low, high, flashes => omega
  | Succ m, k, none, number, low, high, flashes =>
    match e: (stepsFrom cavern k).step.allZero with
      | False =>
        if first: number ≤ Succ k then
          let same: number = Succ k := omega
          Bool.falseNotTrue (Eq.trans (Eq.sym e) (zerosOfAllFlash cavern k (rewrite same at flashes in flashes)))
        else syncNone cavern m (Succ k) (rewrite stepsFromSucc k cavern in none) number (omega) (omega) flashes

--| ...and if it answers nothing, no step up to `syncLimit` is one.
theorem part2None (cavern: Cavern) (none: cavern.solvePart2 = None) (number: Nat) (high: number ≤ syncLimit):
    ¬(AllFlashIn cavern number) :=
  flashes => syncNone cavern syncLimit 0 none number (And.left flashes) (omega) flashes
