--| Both parts, on any program: the docking computer and the spec's machine
--| agree after every instruction (the same mask, and the map reads as the
--| spec's memory), so each answer is the spec's sum of memory.

namespace Aoc.Year2020.Day14.Proofs
import Aoc.Year2020.Day14 (..)
import Aoc.Year2020.Day14 (Spec)
import Std (Eq, List, Map, Nat)

def Agrees (computer: Computer) (machine: Spec.Machine): Prop :=
  computer.mask = machine.mask ∧ (∀ (address: Nat) => machine.memory address = computer.memory.getOr address 0)

theorem startAgrees: Agrees Computer.start Spec.start := Both rfl (address => rfl)

--| What a part's write does to the program's memory, the spec's write does
--| to its memory.
def WritesAgree (write: Computer → Nat → Nat → Computer) (specWrite: Mask → Nat → Nat → Spec.Memory → Spec.Memory): Prop :=
  ∀ (computer: Computer) (machine: Spec.Machine) (address value: Nat) => Agrees computer machine →
    (write computer address value).mask = computer.mask
      ∧ (∀ (other: Nat) => specWrite machine.mask address value machine.memory other = (write computer address value).memory.getOr other 0)

theorem stepAgrees ∀ (write: Computer → Nat → Nat → Computer) (specWrite: Mask → Nat → Nat → Spec.Memory → Spec.Memory)
    (writes: WritesAgree write specWrite) (computer: Computer) (machine: Spec.Machine) (agrees: Agrees computer machine)
    (instruction: Instruction): Agrees (computer.run instruction write) (Spec.step specWrite machine instruction) :=
  match instruction with
    | SetMask mask => Both rfl (And.right agrees)
    | Write address value =>
      match writes computer machine address value agrees with
        | Both keeps written => Both (Eq.trans keeps (And.left agrees)) written

theorem foldAgrees ∀ (write: Computer → Nat → Nat → Computer) (specWrite: Mask → Nat → Nat → Spec.Memory → Spec.Memory)
    (writes: WritesAgree write specWrite) (instructions: List Instruction) (computer: Computer) (machine: Spec.Machine)
    (agrees: Agrees computer machine):
    Agrees (instructions.foldLeft computer (computer instruction => computer.run instruction write)) (instructions.foldLeft machine (Spec.step specWrite)) :=
  match instructions with
    | [] => agrees
    | [instruction, ..rest] =>
      foldAgrees write specWrite writes rest (computer.run instruction write) (Spec.step specWrite machine instruction)
        (stepAgrees write specWrite writes computer machine agrees instruction)

theorem writeValueAgrees: WritesAgree Computer.writeValue Spec.writeMasked :=
  computer machine address value agrees =>
    Both rfl
      (other =>
        rewrite Map.getOrInsert computer.memory address (computer.mask.applyTo value) other 0, applyToMasked computer.mask value, And.left agrees,
          And.right agrees other in rfl)

theorem writeDecodedAgrees: WritesAgree Computer.writeDecoded Spec.writeDecoded :=
  computer machine address value agrees =>
    Both rfl
      (other =>
        rewrite Map.getOrInsertAll value other 0 (computer.mask.decode address) computer.memory, decodeContains computer.mask address other, And.left agrees,
          And.right agrees other in rfl)

--| Part 1's answer is the spec's sum of memory, for any program.
theorem part1Rules ∀ (program: Program): Spec.Part1 program program.valueSum :=
  let agrees := foldAgrees Computer.writeValue Spec.writeMasked writeValueAgrees program.instructions Computer.start Spec.start startAgrees
  sumOfMap _ (Spec.run Spec.writeMasked program) (And.right agrees)

--| Part 2's answer is the spec's sum of memory, for any program.
theorem part2Rules ∀ (program: Program): Spec.Part2 program program.decodedSum :=
  let agrees := foldAgrees Computer.writeDecoded Spec.writeDecoded writeDecodedAgrees program.instructions Computer.start Spec.start startAgrees
  sumOfMap _ (Spec.run Spec.writeDecoded program) (And.right agrees)
