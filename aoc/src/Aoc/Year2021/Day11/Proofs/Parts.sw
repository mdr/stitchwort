--| Both answers are the spec's. Part 1: the program's run of 100 steps is
--| a `Run`, and every `Run` is the program's, so the answer is the only
--| one. Part 2: if the program answers `n`, every octopus flashes in step
--| n and in no earlier step; if it answers nothing, no step up to
--| `syncLimit` has every octopus flash.

namespace Aoc.Year2021.Day11.Proofs
import Aoc.Year2021.Day11 (..)
import Aoc.Year2021.Day11.Spec (..)
import Aoc.Common (Position, cellAt, cells, mapCells)
import Std (Bool, Eq, Exists, List, Nat, Option, Void)

--| The program's levels after `steps` steps.
def stepsFrom (levels: List (List Nat)): (steps: Nat) → List (List Nat)
  | Zero => levels
  | Succ more => stepsFrom (step levels) more

theorem stepsFromSucc: (steps: Nat) → (levels: List (List Nat)) → stepsFrom levels (Succ steps) = step (stepsFrom levels steps)
  | Zero, levels => rfl
  | Succ steps, levels => stepsFromSucc steps (step levels)

--| The program's steps are a run...
theorem programRun: (steps: Nat) → (levels: List (List Nat)) → Run levels steps (stepsFrom levels steps) (flashesIn levels steps)
  | Zero, levels => Start levels
  | Succ steps, levels =>
    let flashed := flashedAt (flashers levels)
    let spec := flashersCorrect levels
    let rest: Run (after levels flashed) steps (stepsFrom (step levels) steps) (flashesIn (step levels) steps) :=
      rewrite <- stepCorrect levels flashed spec in programRun steps (step levels)
    rewrite zerosCorrect levels flashed spec in Step flashed spec rest

--| ...and every run is the program's.
theorem runIsProgram (levels: List (List Nat)) (steps: Nat) (final: List (List Nat)) (total: Nat) (run: Run levels steps final total):
    final = stepsFrom levels steps ∧ total = flashesIn levels steps :=
  match run with
    | Start _ => Both rfl rfl
    | Step flashed spec rest =>
      let (Both finalSame totalSame) := runIsProgram _ _ _ _ rest
      let same: after levels flashed = step levels := Eq.sym (stepCorrect levels flashed spec)
      Both (rewrite finalSame, same in rfl) (rewrite totalSame, same, <- zerosCorrect levels flashed spec in rfl)

--| Part 1: the program's answer is the spec's...
theorem part1Correct (levels: List (List Nat)): Part1Answer levels (solvePart1 levels) :=
  Witness (stepsFrom levels 100) (programRun 100 levels)

--| ...and the spec has no other.
theorem part1Unique (levels: List (List Nat)) (answer: Nat) (spec: Part1Answer levels answer): answer = solvePart1 levels :=
  Exists.elim spec (final run => And.right (runIsProgram levels 100 final answer run))

--| Every octopus flashes in step k + 1 exactly when the program's levels
--| after it are all 0.
theorem allFlashOfZeros (levels: List (List Nat)) (k: Nat)
    (zeros: (cells (step (stepsFrom levels k))).all (cell => cell.snd == 0) = True): AllFlashIn levels (Succ k) :=
  let before := stepsFrom levels k
  let spec := flashersCorrect before
  let all := rewrite allZeroCorrect before (flashedAt (flashers before)) spec at zeros in zeros
  let each := List.allToAll (cell => flashedAt (flashers before) cell.fst) (cells before) all
  Both (omega)
    (Witness before (Witness (flashesIn levels k) (Both (programRun k levels)
      (Witness (flashedAt (flashers before)) (Both spec (at level member =>
        List.allMem (cell => flashedAt (flashers before) cell.fst = True) (at, level) (cells before) each member))))))

theorem zerosOfAllFlash (levels: List (List Nat)) (k: Nat) (spec: AllFlashIn levels (Succ k)):
    (cells (step (stepsFrom levels k))).all (cell => cell.snd == 0) = True :=
  let (Both _ found) := spec
  Exists.elim found (before rest =>
    Exists.elim rest (total both =>
      let (Both run flashedAll) := both
      let same: before = stepsFrom levels k := And.left (runIsProgram levels k before total run)
      Exists.elim flashedAll (flashed both =>
        let (Both flashers each) := both
        rewrite <- same, allZeroCorrect before flashed flashers in
          List.allOfAll (cell => flashed cell.fst) (cells before)
            (List.allOfMem (cell => flashed cell.fst = True) (cells before) (cell member =>
              match cell with
                | (at, level) => each at level member)))))

--| The search from step k + 1, with no step up to k an all-flash step.
theorem syncFound (levels: List (List Nat)) (answer: Nat): (m: Nat) → (k: Nat) →
    ((earlier: Nat) → earlier < Succ k → ¬(AllFlashIn levels earlier)) →
    firstSync (stepsFrom levels k) (Succ k) m = Some answer → Part2Answer levels answer
  | Zero, k, noneBefore, found => Void.exfalso (Option.noneNotSome answer found)
  | Succ m, k, noneBefore, found =>
    match e: (cells (step (stepsFrom levels k))).all (cell => cell.snd == 0) with
      | True =>
        let same: Succ k = answer := Option.someInjective _ _ found
        rewrite <- same in Both (allFlashOfZeros levels k e) noneBefore
      | False =>
        syncFound levels answer m (Succ k)
          (earlier below flashes =>
            match Nat.decLessEq (Succ earlier) (Succ k) with
              | Yes early => noneBefore earlier early flashes
              | No late =>
                let same: earlier = Succ k := omega
                Bool.falseNotTrue (Eq.trans (Eq.sym e) (zerosOfAllFlash levels k (rewrite same at flashes in flashes))))
          (rewrite stepsFromSucc k levels in found)

--| Part 2: if the program answers, its answer is the first step in which
--| every octopus flashes...
theorem part2Correct (levels: List (List Nat)) (answer: Nat) (found: solvePart2 levels = Some answer): Part2Answer levels answer :=
  syncFound levels answer syncLimit 0 (earlier below flashes => Void.exfalso (omega [And.left flashes])) found

--| The search from step k + 1 finding nothing in m steps.
theorem syncNone (levels: List (List Nat)): (m: Nat) → (k: Nat) → firstSync (stepsFrom levels k) (Succ k) m = None →
    (number: Nat) → Succ k ≤ number → number ≤ k + m → ¬(AllFlashIn levels number)
  | Zero, k, none, number, low, high, flashes => omega
  | Succ m, k, none, number, low, high, flashes =>
    match e: (cells (step (stepsFrom levels k))).all (cell => cell.snd == 0) with
      | True => Option.noneNotSome (Succ k) (Eq.sym none)
      | False =>
        match Nat.decLessEq number (Succ k) with
          | Yes first =>
            let same: number = Succ k := omega
            Bool.falseNotTrue (Eq.trans (Eq.sym e) (zerosOfAllFlash levels k (rewrite same at flashes in flashes)))
          | No later => syncNone levels m (Succ k) (rewrite stepsFromSucc k levels in none) number (omega) (omega) flashes

--| ...and if it answers nothing, no step up to `syncLimit` is one.
theorem part2None (levels: List (List Nat)) (none: solvePart2 levels = None) (number: Nat) (high: number ≤ syncLimit):
    ¬(AllFlashIn levels number) :=
  flashes => syncNone levels syncLimit 0 none number (And.left flashes) (omega) flashes
