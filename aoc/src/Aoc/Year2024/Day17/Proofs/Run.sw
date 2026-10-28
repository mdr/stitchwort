-- Runs: a run that finishes is a halting run of the puzzle's computer with
-- the same output (`runHalts`, `outcomeHalts`), and more fuel never changes
-- a finished run (`runMoreFuel`).

namespace Aoc.Year2024.Day17.Proofs
import Aoc.Year2024.Day17 (..)
import Aoc.Year2024.Day17.Spec (..)
import Std (And, Bool, Eq, Exists, List, Nat, Option, Void)

-- What a finished run output, and nothing for the others.
def finishedOutput: Outcome → List Nat
  | Finished output => output
  | _ => Nil

def isFinished: Outcome → Bool
  | Finished output => True
  | _ => False

theorem faultedNotFinished (output: List Nat) (same: Faulted = Finished output): Void := Bool.falseNotTrue (Eq.cong isFinished same)

theorem outOfFuelNotFinished (output: List Nat) (same: OutOfFuel = Finished output): Void := Bool.falseNotTrue (Eq.cong isFinished same)

theorem finishedInjective (first: List Nat) (second: List Nat) (same: Finished first = Finished second): first = second := Eq.cong finishedOutput same

-- A run that finishes outputs what was printed before it, then what a
-- halting run of the puzzle's computer outputs.
theorem runHalts (program: List Nat): (fuel: Nat) → (machine: Machine) → (printed: List Nat) → (output: List Nat) →
    machine.run program printed fuel = Finished output → ∃ (rest: List Nat) => output = List.append printed.reverse rest ∧ Halts program machine rest
  | Zero, machine, printed, output, finished => Void.exfalso (outOfFuelNotFinished output finished)
  | Succ fuel, machine, printed, output, finished =>
    let matches := stepMatches program machine
    match moved: machine.step program with
      | Halt =>
        Witness Nil (Both (Eq.trans (Eq.sym (finishedInjective printed.reverse output finished)) (Eq.sym (List.appendNil printed.reverse))) (Stops machine matches))
      | Fault => Void.exfalso (faultedNotFinished output finished)
      | Next after None =>
        match runHalts program fuel after printed output finished with
          | Witness rest (Both same halts) => Witness rest (Both same (Quiet machine after rest matches halts))
      | Next after (Some value) =>
        match runHalts program fuel after (Cons value printed) output finished with
          | Witness rest (Both same halts) =>
            Witness (Cons value rest)
              (Both (rewrite List.reverseCons value printed, List.appendAssoc printed.reverse [value] rest at same) (Prints machine after value rest matches halts))

-- From the start, a finished run's output is a halting run's.
theorem outcomeHalts (registers: Registers) (program: List Nat) (output: List Nat) (finished: outcome registers program = Finished output):
    Halts program (start registers) output :=
  match runHalts program (fuelFor registers program) (start registers) Nil output finished with
    | Witness rest (Both same halts) => rewrite same in halts

-- More fuel finishes the same way.
theorem runMoreFuel (program: List Nat) (extra: Nat): (fuel: Nat) → (machine: Machine) → (printed: List Nat) → (output: List Nat) →
    machine.run program printed fuel = Finished output → machine.run program printed (fuel + extra) = Finished output
  | Zero, machine, printed, output, finished => Void.exfalso (outOfFuelNotFinished output finished)
  | Succ fuel, machine, printed, output, finished =>
    match moved: machine.step program with
      | Halt => finished
      | Fault => finished
      | Next after None => runMoreFuel program extra fuel after printed output finished
      | Next after (Some value) => runMoreFuel program extra fuel after (Cons value printed) output finished
