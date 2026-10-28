-- Advent of Code 2024, day 17: a 3-bit computer with registers A, B and C
-- and eight instructions, each an opcode and an operand. Part 1 runs the
-- program and joins what it outputs with commas; part 2 finds the lowest
-- positive initial A for which the program outputs a copy of itself.
--
--   $ cd aoc && stitchwort run Aoc.Year2024.Day17.main < examples/2024/day17.txt
--
-- The proofs are in `Aoc.Year2024.Day17.Proofs` (Proofs/) and the tests in
-- `Aoc.Year2024.Day17.Tests` (Tests/); `run` checks neither.

namespace Aoc.Year2024.Day17
import Std (Fail, IO, List, Nat, Option, Parse, Text)
import Std.Parse (blankLine, char, natDigits, newline, nat, sepBy1, text)

def main(): {IO, Fail} () :=
  let debugger := parseDebugger IO.readAll()
  IO.print "Part 1: ${solvePart1 debugger}"
  let lowest :=
    match solvePart2 debugger with
      | Some a => "${a}"
      | None => "none: no initial value of A outputs the program"
  IO.print "Part 2: ${lowest}"

type Registers = { a: Nat, b: Nat, c: Nat }

-- The registers' initial values and the program, a list of 3-bit numbers.
type Debugger = { registers: Registers, program: List Nat }

-- What a combo operand stands for: 0 to 3 themselves, 4 to 6 a register.
type Combo =
  | Value (value: Nat)
  | RegisterA
  | RegisterB
  | RegisterC

type Instruction =
  | Adv (operand: Combo)
  | Bxl (operand: Nat)
  | Bst (operand: Combo)
  | Jnz (target: Nat)
  | Bxc
  | Out (operand: Combo)
  | Bdv (operand: Combo)
  | Cdv (operand: Combo)

-- Where the program is: the registers and the instruction pointer.
type Machine = { registers: Registers, pointer: Nat }

-- What one instruction does: halt, fail on an invalid instruction, or go on
-- from another machine, having output a value or not.
type Step =
  | Halt
  | Fault
  | Next (machine: Machine) (printed: Option Nat)

-- How a run ends: halted with what it output, on an invalid instruction,
-- or not halted within its steps.
type Outcome =
  | Finished (output: List Nat)
  | Faulted
  | OutOfFuel

-- A digit from 0 to 7.
def threeBit(): {Parse} Nat :=
  let start := Parse.mark()
  let value := natDigits 1 1
  Parse.ensureAt start (value < 8) "expected a 3-bit number (0 to 7)"
  value

-- "Register A: 729", without the line break.
def register (name: Text): {Parse} Nat :=
  text "Register ${name}: "
  nat()

def debugger(): {Parse} Debugger :=
  let a := register "A"
  newline()
  let b := register "B"
  newline()
  let c := register "C"
  blankLine()
  text "Program: "
  let program := sepBy1 threeBit (() => char ',')
  { registers = { a, b, c }, program }

def parseDebugger (input: Text): {Fail} Debugger := Parse.all input debugger

-- The combo operand `operand` stands for; operand 7 is reserved.
def comboOperand (operand: Nat): Option Combo :=
  match operand with
    | 4 => Some RegisterA
    | 5 => Some RegisterB
    | 6 => Some RegisterC
    | _ => if operand < 4 then Some (Value operand) else None

-- The instruction an opcode and its operand make, if they make one.
def decode (opcode: Nat) (operand: Nat): Option Instruction :=
  match opcode with
    | 0 => comboOperand operand |> .map Adv
    | 1 => Some (Bxl operand)
    | 2 => comboOperand operand |> .map Bst
    | 3 => Some (Jnz operand)
    | 4 => Some Bxc
    | 5 => comboOperand operand |> .map Out
    | 6 => comboOperand operand |> .map Bdv
    | 7 => comboOperand operand |> .map Cdv
    | _ => None

def Registers.value (registers: Registers) (operand: Combo): Nat :=
  match operand with
    | Value value => value
    | RegisterA => registers.a
    | RegisterB => registers.b
    | RegisterC => registers.c

-- A divided by 2 to the power of the operand, truncated.
def Registers.divide (registers: Registers) (operand: Combo): Nat := registers.a.shiftRight (registers.value operand)

-- The next instruction, with `registers`.
def Machine.advance (machine: Machine) (registers: Registers): Machine := { registers, pointer = machine.pointer + 2 }

def Machine.execute (machine: Machine) (instruction: Instruction): Step :=
  let registers := machine.registers
  match instruction with
    | Adv operand => Next (machine.advance { registers | a = registers.divide operand }) None
    | Bxl operand => Next (machine.advance { registers | b = registers.b.xor operand }) None
    | Bst operand => Next (machine.advance { registers | b = registers.value operand % 8 }) None
    | Jnz target => if registers.a == 0 then Next (machine.advance registers) None else Next ({ machine | pointer = target }) None
    | Bxc => Next (machine.advance { registers | b = registers.b.xor registers.c }) None
    | Out operand => Next (machine.advance registers) (Some (registers.value operand % 8))
    | Bdv operand => Next (machine.advance { registers | b = registers.divide operand }) None
    | Cdv operand => Next (machine.advance { registers | c = registers.divide operand }) None

-- The instruction at the pointer: halt past the end of the program, and
-- fail on an opcode without an operand or an invalid instruction.
def Machine.step (machine: Machine) (program: List Nat): Step :=
  match program.get machine.pointer with
    | None => Halt
    | Some opcode =>
      match program.get (machine.pointer + 1) |> .flatMap (operand => decode opcode operand) with
        | Some instruction => machine.execute instruction
        | None => Fault

-- At most `fuel` steps; `printed` is what was output so far, newest first.
def Machine.run (machine: Machine) (program: List Nat) (printed: List Nat): (fuel: Nat) → Outcome
  | Zero => OutOfFuel
  | Succ fuel =>
    match machine.step program with
      | Halt => Finished printed.reverse
      | Fault => Faulted
      | Next after None => after.run program printed fuel
      | Next after (Some value) => after.run program (Cons value printed) fuel

-- Steps enough for a loop that shifts A right on each pass to finish.
def fuelFor (registers: Registers) (program: List Nat): Nat := (registers.a + 1) * (program.length + 1)

-- The program run from `registers` at its first instruction.
def outcome (registers: Registers) (program: List Nat): Outcome :=
  ({ registers, pointer = 0 }: Machine).run program [] (fuelFor registers program)

def solvePart1 (debugger: Debugger): {Fail} Text :=
  match outcome debugger.registers debugger.program with
    | Finished output => Text.joinWith (output.map (value => "${value}")) ","
    | Faulted => Fail.fail "the program has an invalid instruction"
    | OutOfFuel => Fail.fail "the program didn't halt"

-- Part 2.

-- What the program outputs when A starts at `a`; nothing if it doesn't halt.
def Debugger.outputFor (debugger: Debugger) (a: Nat): List Nat :=
  match outcome { debugger.registers | a } debugger.program with
    | Finished output => output
    | _ => []

-- Initial values for A that output `target`, built three bits at a time
-- from the end: a value that outputs `value` then `rest` is one that
-- outputs `rest`, times 8, plus a number below 8.
def candidates (output: Nat → List Nat): (target: List Nat) → List Nat
  | Nil => [0]
  | Cons value rest =>
    candidates output rest
      |> .flatMap (high => List.range 8 |> .map (low => high * 8 + low))
      |> .filter (a => output a == Cons value rest)

-- The lowest positive initial A for which `output` is `target`, among the
-- candidates.
def lowestOutputting (output: Nat → List Nat) (target: List Nat): Option Nat :=
  candidates output target
    |> .filter (a => 0 < a ∧ output a == target)
    |> .minimum

def solvePart2 (debugger: Debugger): Option Nat := lowestOutputting debugger.outputFor debugger.program
