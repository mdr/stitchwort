--| Advent of Code 2020, day 14: the ferry's docking program, one instruction
--| a line. `mask = …` sets a bitmask of 36 `0`s, `1`s and `X`s (the most
--| significant bit first); `mem[8] = 11` writes 11 to address 8. Memory
--| holds 36-bit numbers and starts as all 0s. In part 1 the mask changes
--| each value written: a 0 or 1 in the mask overwrites that bit, an X
--| leaves it. In part 2 it changes the address instead: a 0 leaves the
--| bit, a 1 overwrites it with 1, and an X is floating, taking both values,
--| so the value is written to every address that results. Each answer is
--| the sum of the values left in memory.
--|
--|   $ cd aoc && stitchwort run Aoc.Year2020.Day14.main < inputs/2020/day14.txt
--|
--| Memory is a `Map` from address to value, holding only what was written.
--| Part 1 applies the mask with `Nat.and` and `Nat.or`. Part 2 lists every
--| address a write decodes to, one bit at a time: an X doubles the list, so
--| a mask with `k` Xs gives `2 ^ k` addresses (the input's masks have at
--| most 9). The proofs, that the parser reads the puzzle's format and that
--| both answers are the puzzle's, are in `Aoc.Year2020.Day14.Proofs`
--| (Proofs/), and the tests in `Aoc.Year2020.Day14.Tests` (Tests/); `run`
--| checks neither.

namespace Aoc.Year2020.Day14
import Std (Fail, IO, List, Map, Nat, Parse)

def main(): {IO, Fail} () :=
  let program := parseProgram IO.readAll()
  IO.print "Part 1: ${program.valueSum}"
  IO.print "Part 2: ${program.decodedSum}"

--| One character of a mask.
type MaskBit = | Off | On | X

def MaskBit.symbol: MaskBit → Text
  | Off => "0"
  | On => "1"
  | X => "X"

def MaskBit.isOn: MaskBit → Bool
  | On => True
  | _ => False

def MaskBit.isFloating: MaskBit → Bool
  | X => True
  | _ => False

--| The mask's bits, the most significant first.
type Mask = { bits: List MaskBit }

def Mask.width (mask: Mask): Nat := mask.bits.length

--| The number with a 1 wherever the mask has a 1.
def Mask.ones (mask: Mask): Nat := Nat.fromBits (mask.bits.map .isOn)

--| The number with a 1 wherever the mask has an X.
def Mask.floating (mask: Mask): Nat := Nat.fromBits (mask.bits.map .isFloating)

--| Part 1's rule: the mask's 0s and 1s overwrite the value's bits, its Xs
--| keep them. Bits above the mask's width are cleared, as in a 36-bit
--| memory.
def Mask.applyTo (mask: Mask) (value: Nat): Nat := Nat.or (Nat.and value mask.floating) mask.ones

--| The bits of every address `address` decodes to, for the mask's bits and
--| the address's bits beside them.
def decodeBits: (mask: List MaskBit) → (address: List Bool) → List (List Bool)
  | [Off, ..mask], [bit, ..address] => decodeBits mask address |> .map (Cons bit)
  | [On, ..mask], [bit, ..address] => decodeBits mask address |> .map (Cons True)
  | [X, ..mask], [bit, ..address] =>
    let rest := decodeBits mask address
    rest.map (Cons False) ++ rest.map (Cons True)
  | _, _ => [[]]

--| Part 2's rule: every address that `address` decodes to.
def Mask.decode (mask: Mask) (address: Nat): List Nat :=
  decodeBits mask.bits (Nat.toBits mask.width address) |> .map Nat.fromBits

type Instruction = | SetMask (mask: Mask) | Write (address: Nat) (value: Nat)

type Program = { instructions: List Instruction }

def maskBits: List MaskBit := [Off, On, X]

def maskBit(): {Parse} MaskBit := Parse.pick (maskBits.map (bit => (bit.symbol, bit)))

def instruction(): {Parse} Instruction := match Parse.optional (() => Parse.text "mask = ") with
  | Some _ =>
    let bits := Parse.exactly 36 maskBit
    SetMask { bits }
  | None =>
    Parse.text "mem["
    let address := Parse.nat()
    Parse.text "] = "
    let value := Parse.nat()
    Write address value

def startsWithMask: List Instruction → Bool
  | [SetMask _, .._] => True
  | _ => False

def parseProgram (input: Text): {Fail} Program :=
  let instructions := Parse.eachLine input instruction
  if startsWithMask instructions then { instructions } else Fail.fail "the program has to start with a mask"

--| The docking computer: the mask last set, and what has been written.
type Computer = { mask: Mask, memory: Map Nat Nat }

--| Before the first instruction, which sets a mask in any program
--| `parseProgram` reads.
def Computer.start: Computer := { mask = { bits = [] }, memory = Map.empty }

def Computer.memorySum (computer: Computer): Nat := computer.memory.values.sum

def Computer.setMask (computer: Computer) (mask: Mask): Computer := { computer | mask }

--| Part 1's write: the value, masked, to the address.
def Computer.writeValue (computer: Computer) (address value: Nat): Computer :=
  { computer | memory = computer.memory.insert address (computer.mask.applyTo value) }

--| Part 2's write: the value to every address the mask decodes the address to.
def Computer.writeDecoded (computer: Computer) (address value: Nat): Computer := { computer |
  memory = computer.mask.decode address |> .foldLeft computer.memory (memory target => memory.insert target value)
}

def Computer.run (computer: Computer) (instruction: Instruction) (write: Computer → Nat → Nat → Computer): Computer :=
  match instruction with
    | SetMask mask => computer.setMask mask
    | Write address value => write computer address value

--| Part 1: the sum of memory after the program, writing masked values.
def Program.valueSum (program: Program): Nat :=
  program.instructions.foldLeft Computer.start (computer instruction => computer.run instruction .writeValue)
    |> .memorySum

--| Part 2: the sum of memory after the program, writing to decoded addresses.
def Program.decodedSum (program: Program): Nat :=
  program.instructions.foldLeft Computer.start (computer instruction => computer.run instruction .writeDecoded)
    |> .memorySum
