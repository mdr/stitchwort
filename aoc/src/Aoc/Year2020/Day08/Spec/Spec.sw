--| Day 8 as the puzzle states it: the instructions as the input writes
--| them, what each does, and the two questions about a run of the boot
--| code. The proofs (Proofs/) show the program's answers are these.

namespace Aoc.Year2020.Day08.Spec
import Aoc.Year2020.Day08 (Instruction, Operation, Program, State)
import Std (Char, Int, List, Parse, Text)

-- The format

def OperationWritten (read: List Char) (operation: Operation): Prop := match operation with
  | Acc => read = "acc".toList
  | Jmp => read = "jmp".toList
  | Nop => read = "nop".toList

--| "+3", "-99" or "3": an optional sign, then the size in decimal. The
--| parser accepts a number without a sign too, so the spec does.
def ArgumentWritten (read: List Char) (argument: Int): Prop := Parse.IntRead read argument

--| "acc +3": the operation, a space, and the argument.
def InstructionWritten (read: List Char) (instruction: Instruction): Prop :=
  ∃ (operation: List Char) => ∃ (argument: List Char) =>
    read = operation ++ [' ', ..argument] ∧ OperationWritten operation instruction.operation ∧ ArgumentWritten argument instruction.argument

-- Running the boot code

--| "The first instruction": the console starts there, with the accumulator 0.
def start: State := { next = 0, accumulator = 0 }

--| The instruction at `position`, counting the first as 0, if the boot
--| code has one there.
def instructionAt (program: Program) (position: Int): Option Instruction := match position.toNatChecked with
  | Some index => program.instructions.get index
  | None => None

--| What executing `instruction` does to the console. `acc` "increases or
--| decreases ... the accumulator by the value given in the argument", and
--| "the instruction immediately below it is executed next"; `jmp` "jumps
--| to a new instruction relative to itself"; `nop` "does nothing", and
--| "the instruction immediately below it is executed next".
def Executes (instruction: Instruction) (before: State) (after: State): Prop := match instruction.operation with
  | Acc => after.accumulator = before.accumulator + instruction.argument ∧ after.next = before.next + 1
  | Jmp => after.accumulator = before.accumulator ∧ after.next = before.next + instruction.argument
  | Nop => after.accumulator = before.accumulator ∧ after.next = before.next + 1

--| One step: the console executes the instruction it is at.
def Step (program: Program) (before: State) (after: State): Prop :=
  ∃ (instruction: Instruction) => instructionAt program before.next = Some instruction ∧ Executes instruction before after

--| From `state`, the console executes the instructions at `positions`, in
--| order, and is then at `last`.
def Runs (program: Program) (state: State): (positions: List Int) → (last: State) → Prop
  | [], last => last = state
  | [position, ..rest], last => position = state.next ∧ ∃ (after: State) => Step program state after ∧ Runs program after rest last

-- Part 1

--| "Immediately before any instruction is executed a second time, what
--| value is in the accumulator?" A run from the start has executed no
--| instruction twice, and is at one it has executed: its accumulator is
--| `answer`.
def Part1 (program: Program) (answer: Int): Prop :=
  ∃ (positions: List Int) => ∃ (last: State) =>
    Runs program start positions last ∧ List.Distinct positions ∧ last.next ∈ positions ∧ answer = last.accumulator

-- Part 2

--| "The program is supposed to terminate by attempting to execute an
--| instruction immediately after the last instruction in the file." It
--| does, with `accumulator`.
def Terminates (program: Program) (accumulator: Int): Prop :=
  ∃ (positions: List Int) => ∃ (last: State) =>
    Runs program start positions last ∧ last.next = program.instructions.length.toInt ∧ accumulator = last.accumulator

--| "Exactly one instruction is corrupted": `repaired` is `program` with
--| the instruction at `index` changed from `jmp` to `nop` or from `nop` to
--| `jmp`, its argument kept, and every other instruction the same.
def Repair (program: Program) (index: Nat) (repaired: Program): Prop :=
  repaired.instructions.length = program.instructions.length
    ∧ (∀ (other: Nat) => other ≠ index → repaired.instructions.get other = program.instructions.get other)
    ∧ (∃ (argument: Int) =>
      (program.instructions.get index = Some { operation = Jmp, argument } ∧ repaired.instructions.get index = Some { operation = Nop, argument })
        ∨ (program.instructions.get index = Some { operation = Nop, argument } ∧ repaired.instructions.get index = Some { operation = Jmp, argument }))

--| "What is the value of the accumulator after the program terminates?"
--| Repairing one instruction makes it terminate, with `answer`.
def Part2 (program: Program) (answer: Int): Prop :=
  ∃ (index: Nat) => ∃ (repaired: Program) => Repair program index repaired ∧ Terminates repaired answer
