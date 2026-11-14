--| Day 14 as the puzzle states it, about the program's data (`MaskBit`,
--| `Mask`, `Instruction`, `Program`): how the program is written, what each
--| instruction does to memory in each part, and each part's answer. Nothing
--| else is shared with the program. Numbers are taken bit by bit, as
--| `Nat.toBits` writes them, the most significant first; memory is a
--| function from address to value. The proofs (Proofs/) show the program
--| computes these.

namespace Aoc.Year2020.Day14.Spec
import Aoc.Year2020.Day14 (Instruction, Mask, MaskBit, Program)
import Std (Char, List, Nat, Parse, Text)

-- The format

def MaskBitWritten (read: List Char) (bit: MaskBit): Prop := match bit with
  | Off => read = ['0']
  | On => read = ['1']
  | X => read = ['X']

def DecimalWritten (read: List Char) (value: Nat): Prop :=
  read ≠ [] ∧ read.all Parse.isDigit = True ∧ value = Parse.digitsValue read

--| "The bitmask is always given as a string of 36 bits, written with the
--| most significant bit (representing 2^35) on the left"; "mem[8] = 11"
--| writes 11 to address 8.
def InstructionWritten (read: List Char) (instruction: Instruction): Prop := match instruction with
  | SetMask mask =>
    ∃ (symbols: List Char) => read = "mask = ".toList ++ symbols
      ∧ Parse.Each MaskBitWritten symbols mask.bits
      ∧ mask.bits.length = 36
  | Write address value =>
    ∃ (addressRead: List Char) => ∃ (valueRead: List Char) => read
      = "mem[".toList ++ addressRead ++ "] = ".toList ++ valueRead
      ∧ DecimalWritten addressRead address
      ∧ DecimalWritten valueRead value

def StartsWithMask: (instructions: List Instruction) → Prop
  | [SetMask mask, ..rest] => Unit
  | _ => Void

--| One instruction a line, the first setting the mask (every program in the
--| puzzle starts so, and a write before any mask would have none to use).
def ProgramWritten (lines: List (List Char)) (program: Program): Prop :=
  List.All2 InstructionWritten lines program.instructions ∧ StartsWithMask program.instructions

-- Memory

--| "The entire 36-bit address space begins initialized to the value 0 at
--| every address."
def Memory: Type := Nat → Nat

def empty: Memory := address => 0

--| "What is the sum of all values left in memory after it completes?": the
--| sum over some addresses, each once, that include every address not
--| holding 0.
def SumOfMemory (memory: Memory) (answer: Nat): Prop :=
  ∃ (addresses: List Nat) => addresses.Distinct
    ∧ (∀ (address: Nat) => memory address ≠ 0 → address ∈ addresses)
    ∧ answer = addresses.sumBy memory

--| The mask last set, and memory. The mask before the first instruction
--| sets one is never used: a written program starts by setting it.
type Machine = { mask: Mask, memory: Memory }

def start: Machine := { mask = { bits = [] }, memory = empty }

--| "The program can either update the bitmask or write a value to memory",
--| with `write` saying what a write does to memory under the current mask.
def step (write: Mask → Nat → Nat → Memory → Memory) (machine: Machine) (instruction: Instruction): Machine :=
  match instruction with
    | SetMask mask => { machine | mask }
    | Write address value => { machine | memory = write machine.mask address value machine.memory }

--| Memory after the whole program.
def run (write: Mask → Nat → Nat → Memory → Memory) (program: Program): Memory :=
  (program.instructions.foldLeft start (step write)).memory

-- Part 1

--| "A 0 or 1 overwrites the corresponding bit in the value, while an X
--| leaves the bit in the value unchanged."
def overwrite (maskBit: MaskBit) (bit: Bool): Bool := match maskBit with
  | Off => False
  | On => True
  | X => bit

--| The value written: its bits beside the mask's, each overwritten.
def masked (mask: Mask) (value: Nat): Nat :=
  Nat.fromBits (List.zipWith mask.bits (Nat.toBits mask.bits.length value) overwrite)

--| "The current bitmask is applied to values immediately before they are
--| written to memory."
def writeMasked (mask: Mask) (address value: Nat) (memory: Memory): Memory := other =>
  if address == other then masked mask value else memory other

def Part1 (program: Program) (answer: Nat): Prop := SumOfMemory (run writeMasked program) answer

-- Part 2

--| "If the bitmask bit is 0, the corresponding memory address bit is
--| unchanged. If the bitmask bit is 1, the corresponding memory address bit
--| is overwritten with 1. If the bitmask bit is X, the corresponding memory
--| address bit is floating": it may be either.
def bitFits (maskBit: MaskBit) (addressBit bit: Bool): Bool := match maskBit with
  | Off => bit == addressBit
  | On => bit
  | X => True

def allFit: (mask: List MaskBit) → (address: List Bool) → (bits: List Bool) → Bool
  | [maskBit, ..mask], [addressBit, ..address], [bit, ..bits] =>
    bitFits maskBit addressBit bit && allFit mask address bits
  | _, _, _ => True

--| Whether the decoder writes to `target` for a write to `address`: "a
--| floating bit is not connected to anything and instead fluctuates
--| unpredictably. In practice, this means the floating bits will take on all
--| possible values, potentially causing many memory addresses to be written
--| all at once!" `target` is an address of the mask's width whose every bit
--| fits.
def Decodes (mask: Mask) (address target: Nat): Bool :=
  target < Nat.pow 2 mask.bits.length
    && allFit mask.bits (Nat.toBits mask.bits.length address) (Nat.toBits mask.bits.length target)

--| "Immediately before a value is written to memory, each bit in the
--| bitmask modifies the corresponding bit of the destination memory
--| address."
def writeDecoded (mask: Mask) (address value: Nat) (memory: Memory): Memory := target =>
  if Decodes mask address target then value else memory target

def Part2 (program: Program) (answer: Nat): Prop := SumOfMemory (run writeDecoded program) answer
