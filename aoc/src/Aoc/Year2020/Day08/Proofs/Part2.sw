--| Part 2: the accumulator the program reports is that of the boot code
--| with one `jmp` or `nop` repaired, run until it terminates.

namespace Aoc.Year2020.Day08.Proofs
import Aoc.Year2020.Day08 (..)
import Aoc.Year2020.Day08 (Spec)
import Std (Bool, DecEq, Eq, Fail, Int, List, Map, Nat, Option, Result, Void)

def Program.replaceAt (program: Program) (index: Nat) (instruction: Instruction): Program :=
  { instructions = List.set program.instructions index instruction }

theorem repairedHolds ∀ (program: Program) (index: Nat) (instruction: Instruction) (below: index < program.instructions.length):
    Holds ({ program.code | byPosition = program.code.byPosition.insert index instruction }) (program.replaceAt index instruction) :=
  Both (Eq.sym (List.lengthSet program.instructions index instruction))
    (position =>
      match d: position == index with
        | True =>
          rewrite d.read, Map.getInsert index instruction program.code.byPosition in
            Eq.sym (List.getSet program.instructions index instruction below)
        | False =>
          let differ: position ≠ index := same => d.read same
          rewrite Map.getInsertOther index instruction position differ program.code.byPosition, List.getSetOther program.instructions index instruction position differ in
            Map.getByPosition program.instructions position)

theorem repairIs ∀ (program: Program) (index: Nat) (instruction: Instruction) (repaired: Instruction) (listed: program.instructions.get index = Some instruction)
    (swapped: instruction.repaired = Some repaired):
    Spec.Repair program index (program.replaceAt index repaired) :=
  let below := List.getSomeLt program.instructions index instruction listed
  let placed: (program.replaceAt index repaired).instructions.get index = Some repaired := List.getSet program.instructions index repaired below
  Both (List.lengthSet program.instructions index repaired)
    (Both (other differ => List.getSetOther program.instructions index repaired other differ)
      (match instruction with
        | { operation = Jmp, argument } =>
          Witness argument (Inl (Both listed (rewrite Option.someInjective swapped in placed)))
        | { operation = Nop, argument } =>
          Witness argument (Inr (Both listed (rewrite Option.someInjective swapped in placed)))))

--| Repairing `instruction` at `position` makes the program terminate with
--| `answer`, as the spec says.
theorem repairTerminates ∀ (program: Program) (position: Nat) (instruction: Instruction) (answer: Int)
    (listed: program.instructions.get position = Some instruction) (made: program.code.terminatesRepaired position instruction = Some answer):
    ∃ (repaired: Program) => Spec.Repair program position repaired ∧ Spec.Terminates repaired answer :=
  match r: instruction.repaired with
    | Some repaired =>
      let fixed := program.replaceAt position repaired
      let holds := repairedHolds program position repaired (List.getSomeLt program.instructions position instruction listed)
      match runRuns fixed ({ program.code | byPosition = program.code.byPosition.insert position repaired }) holds with
        | Witness positions (Witness last (Both runs (Both distinct ended))) =>
          match o: ({ program.code | byPosition = program.code.byPosition.insert position repaired }).run with
            | Terminates accumulator =>
              let (Both atEnd same) := ended
              let found: accumulator = answer := Option.someInjective made
              Witness fixed (Both (repairIs program position instruction repaired listed r)
                (Witness positions (Witness last (Both runs (Both atEnd (rewrite <- found in same))))))

theorem part2Rules ∀ (program: Program) (answer: Int) (solved: Fail.toResult (() => solvePart2 program) = Ok answer): Spec.Part2 program answer :=
  let ran: Fail.toResult (() => (program.instructions.withIndex.findMap (((position, instruction)) => program.code.terminatesRepaired position instruction)).orFail "no repair of one jmp or nop makes the boot code terminate") = Ok answer :=
    solved
  match f: program.instructions.withIndex.findMap (((position, instruction)) => program.code.terminatesRepaired position instruction) with
    | Some found =>
      match List.memOfFindMap (((position, instruction)) => program.code.terminatesRepaired position instruction) program.instructions.withIndex found f with
        | Witness (position, instruction) (Both member made) =>
          let listed := (List.memWithIndex program.instructions position instruction).forward member
          Witness position (rewrite <- Result.okInjective ran in repairTerminates program position instruction found listed made)
