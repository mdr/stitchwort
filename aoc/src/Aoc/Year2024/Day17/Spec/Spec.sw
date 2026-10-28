-- Day 17 as the puzzle states it, over the program's `Registers`,
-- `Machine` and `Step`. The proofs (Proofs/) show the program's step does
-- what these say for every program and machine, that its runs are halting
-- runs, and what part 2's search finds.

namespace Aoc.Year2024.Day17.Spec
import Aoc.Year2024.Day17 (..)
import Std (Bool, Exists, List, Nat, Option)

-- "Combo operands 0 through 3 represent literal values 0 through 3. Combo
-- operand 4 represents the value of register A. Combo operand 5 represents
-- the value of register B. Combo operand 6 represents the value of register
-- C. Combo operand 7 is reserved and will not appear in valid programs."
def comboValue (registers: Registers) (operand: Nat): Option Nat :=
  if operand ≤ 3 then Some operand
  else
    match operand with
      | 4 => Some registers.a
      | 5 => Some registers.b
      | 6 => Some registers.c
      | _ => None

-- Whether bit `i` of `n` is 1: the bit worth 2 to the power `i`.
def bitSet (n: Nat) (i: Nat): Bool := n / Nat.pow 2 i % 2 == 1

-- "The bitwise XOR of" `x` and `y` is `result`: each bit of it is 1 when
-- exactly one of `x` and `y` has that bit 1.
def BitwiseXor (x: Nat) (y: Nat) (result: Nat): Prop := (i: Nat) → bitSet result i = Bool.xor (bitSet x i) (bitSet y i)

-- The machine at the next instruction, "the instruction pointer increases
-- by 2 after each instruction", with `registers`.
def advanced (machine: Machine) (registers: Registers): Machine := { registers, pointer = machine.pointer + 2 }

-- An instruction that reads a combo operand: `happens` of its value, or, for
-- the reserved operand, a fault.
def WithCombo (registers: Registers) (operand: Nat) (step: Step) (happens: Nat → Prop): Prop :=
  match comboValue registers operand with
    | Some value => happens value
    | None => step = Fault

-- What the instruction with `opcode` and `operand` does to `machine`, as
-- the step it takes. Opcodes above 7 aren't instructions: a fault.
def Executes (opcode: Nat) (operand: Nat) (machine: Machine) (step: Step): Prop :=
  let registers := machine.registers
  match opcode with
    -- "The adv instruction (opcode 0) performs division. The numerator is
    -- the value in the A register. The denominator is found by raising 2 to
    -- the power of the instruction's combo operand. ... The result of the
    -- division operation is truncated to an integer and then written to the
    -- A register."
    | 0 => WithCombo registers operand step (value => step = Next (advanced machine { registers | a = registers.a / Nat.pow 2 value }) None)
    -- "The bxl instruction (opcode 1) calculates the bitwise XOR of register
    -- B and the instruction's literal operand, then stores the result in
    -- register B."
    | 1 => ∃ (result: Nat) => BitwiseXor registers.b operand result ∧ step = Next (advanced machine { registers | b = result }) None
    -- "The bst instruction (opcode 2) calculates the value of its combo
    -- operand modulo 8 (thereby keeping only its lowest 3 bits), then
    -- writes that value to the B register."
    | 2 => WithCombo registers operand step (value => step = Next (advanced machine { registers | b = value % 8 }) None)
    -- "The jnz instruction (opcode 3) does nothing if the A register is 0.
    -- However, if the A register is not zero, it jumps by setting the
    -- instruction pointer to the value of its literal operand; if this
    -- instruction jumps, the instruction pointer is not increased by 2."
    | 3 =>
      if registers.a == 0 then step = Next (advanced machine registers) None
      else step = Next ({ registers, pointer = operand }) None
    -- "The bxc instruction (opcode 4) calculates the bitwise XOR of register
    -- B and register C, then stores the result in register B. (For legacy
    -- reasons, this instruction reads an operand but ignores it.)"
    | 4 => ∃ (result: Nat) => BitwiseXor registers.b registers.c result ∧ step = Next (advanced machine { registers | b = result }) None
    -- "The out instruction (opcode 5) calculates the value of its combo
    -- operand modulo 8, then outputs that value."
    | 5 => WithCombo registers operand step (value => step = Next (advanced machine registers) (Some (value % 8)))
    -- "The bdv instruction (opcode 6) works exactly like the adv
    -- instruction except that the result is stored in the B register. (The
    -- numerator is still read from the A register.)"
    | 6 => WithCombo registers operand step (value => step = Next (advanced machine { registers | b = registers.a / Nat.pow 2 value }) None)
    -- "The cdv instruction (opcode 7) works exactly like the adv
    -- instruction except that the result is stored in the C register."
    | 7 => WithCombo registers operand step (value => step = Next (advanced machine { registers | c = registers.a / Nat.pow 2 value }) None)
    | _ => step = Fault

-- What the computer does at `machine`: "If the computer tries to read an
-- opcode past the end of the program, it instead halts." Otherwise it runs
-- the instruction "whose opcode is" the number at the pointer, with "the
-- 3-bit number after it" as the operand. An opcode with no number after it
-- is not a valid instruction: a fault.
def StepMatches (program: List Nat) (machine: Machine) (step: Step): Prop :=
  match program.get machine.pointer with
    | None => step = Halt
    | Some opcode =>
      match program.get (machine.pointer + 1) with
        | None => step = Fault
        | Some operand => Executes opcode operand machine step

-- From `machine`, the program runs until it halts, outputting `output`,
-- every step as the puzzle says.
type Halts (program: List Nat): Machine → List Nat → Prop =
  | Stops (machine: Machine) (stop: StepMatches program machine Halt): Halts program machine Nil
  | Quiet (machine: Machine) (after: Machine) (output: List Nat) (move: StepMatches program machine (Next after None)) (rest: Halts program after output):
    Halts program machine output
  | Prints (machine: Machine) (after: Machine) (value: Nat) (output: List Nat) (move: StepMatches program machine (Next after (Some value)))
    (rest: Halts program after output): Halts program machine (Cons value output)

-- "Initialize the registers to the given values, then run the given
-- program": the instruction pointer "starts at 0".
def start (registers: Registers): Machine := { registers, pointer = 0 }

-- Part 2: with register A initialized to `a`, "the program outputs a copy
-- of itself".
def OutputsItself (debugger: Debugger) (a: Nat): Prop := Halts debugger.program (start { debugger.registers | a }) debugger.program

-- The shape part 2's search relies on, which the puzzle doesn't state but
-- the programs it gives have: each pass of a loop outputs one number, shifts
-- A right by 3 bits and starts again unless A is 0, so what A outputs is a
-- number, then what A / 8 outputs if A / 8 isn't 0. Assumed, not checked.
def LoopShape (output: Nat → List Nat): Prop := (a: Nat) → ∃ (first: Nat) => output a = Cons first (if a < 8 then Nil else output (a / 8))
