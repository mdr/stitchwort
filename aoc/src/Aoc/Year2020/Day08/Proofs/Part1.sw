--| Part 1: the accumulator the program reports is the one just before an
--| instruction would run a second time.

namespace Aoc.Year2020.Day08.Proofs
import Aoc.Year2020.Day08 (..)
import Aoc.Year2020.Day08 (Spec)
import Std (Eq, Fail, Int, List, Map, Nat, Option, Result, Set, Void)

theorem codeHolds (program: Program): Holds program.code program := Both rfl (position => Map.getByPosition program.instructions position)

theorem unvisitedAll (length: Nat): Unvisited length [] (Set.fromList (0 ..< length)) :=
  position => {
    forward = held =>
      let member := (Set.containsFromListIff (0 ..< length) position).forward held
      Both (And.right ((List.memRange position 0 length).forward member)) (m => m),
    backward = (Both below out) =>
      (Set.containsFromListIff (0 ..< length) position).backward ((List.memRange position 0 length).backward (Both (Nat.zeroLe position) below))
  }

--| A run of any code holding `program`, from the start: the spec's run.
theorem runRuns (program: Program) (code: Code) (holds: Holds code program):
    ∃ (positions: List Int) => ∃ (last: State) =>
      Spec.Runs program Spec.start positions last ∧ List.Distinct positions ∧ Ended program positions last code.run :=
  runFromRuns program code holds (Set.fromList (0 ..< code.length)) start [] (unvisitedAll code.length) ()

theorem part1Rules (program: Program) (answer: Int) (solved: Fail.toResult (() => solvePart1 program) = Ok answer): Spec.Part1 program answer :=
  match runRuns program program.code (codeHolds program) with
    | Witness positions (Witness last (Both runs (Both distinct ended))) =>
      match o: program.code.run with
        | Loops accumulator =>
          let (Both seen same) := ended
          Witness positions (Witness last (Both runs (Both distinct (Both seen (rewrite <- Result.okInjective solved in same)))))
