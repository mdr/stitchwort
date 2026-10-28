-- Day 24's tests: the puzzle's examples, and ripple-carry adders built
-- here, whole and with outputs swapped. Kept apart from the program, so
-- `stitchwort run Aoc.Year2024.Day24.main` doesn't check them.

namespace Aoc.Year2024.Day24.Tests
import Aoc.Year2024.Day24 (..)
import Std (Bool, Fail, List, Map, Nat, Option, Result, Text)

def parsed (input: Text): Result Device Text := Fail.toResult (() => parseDevice input)

def deviceOf (input: Text): Device := Fail.orElse { initial = [], gates = [] } (() => parseDevice input)

def smallText: Text := "x00: 1\nx01: 1\nx02: 1\ny00: 0\ny01: 1\ny02: 0\n\nx00 AND y00 -> z00\nx01 XOR y01 -> z01\nx02 OR y02 -> z02\n"

def larger: Device := deviceOf (include "../../../../../examples/2024/day24.txt")

def valueOf (device: Device) (name: Text): Option Bool := device.settled.get (Wire.ofName name)

test "small example, part 1" := solvePart1 (deviceOf smallText) == Some 4
test "small example, the z wires" := ["z00", "z01", "z02"].map (valueOf (deviceOf smallText)) == [Some False, Some False, Some True]
test "larger example, part 1" := solvePart1 larger == Some 2024

-- "bfw: 1 bqk: 1 djm: 1 ffh: 0 ...": every wire's value as the puzzle lists it.
test "larger example, every wire" :=
  let listed := [
    ("bfw", True),
    ("bqk", True),
    ("djm", True),
    ("ffh", False),
    ("fgs", True),
    ("frj", True),
    ("fst", True),
    ("gnj", True),
    ("hwm", True),
    ("kjc", False),
    ("kpj", True),
    ("kwq", False),
    ("mjb", True),
    ("nrd", True),
    ("ntg", False),
    ("pbm", True),
    ("psh", True),
    ("qhw", True),
    ("rvg", False),
    ("tgd", False),
    ("tnw", True),
    ("vdt", True),
    ("wpb", False),
    ("z00", False),
    ("z01", False),
    ("z02", False),
    ("z03", True),
    ("z04", False),
    ("z05", True),
    ("z06", True),
    ("z07", True),
    ("z08", True),
    ("z09", True),
    ("z10", True),
    ("z11", False),
    ("z12", False)
  ]
  listed.all (((name, value)) => valueOf larger name == Some value)

test "larger example, part 2 finds no adder" := solvePart2 larger == None

test "wire names" :=
  ["x00", "y07", "z45", "abc", "xab", "x7", "x123", "z0a"].map Wire.ofName
    == [X 0, Y 7, Z 45, Other "abc", Other "xab", Other "x7", Other "x123", Other "z0a"]

test "wire names back" := [X 0, Y 7, Z 45, Other "abc"].map (.name) == ["x00", "y07", "z45", "abc"]

test "parse a gate" := (deviceOf smallText).gates.headOr { left = X 9, operation = Or, right = X 9, output = X 9 } == { left = X 0, operation = And, right = Y 0, output = Z 0 }

test "parse without a final line break" := parsed "x00: 1\n\nx00 OR x00 -> z00" == Ok ({ initial = [(X 0, True)], gates = [{ left = X 0, operation = Or, right = X 0, output = Z 0 }] })

test "a bad value" := parsed "x00: 2\n\nx00 OR x00 -> z00\n" == Err "line 1, column 6: expected 0 or 1, got '2'"

test "a bad operation" := parsed "x00: 1\n\nx00 NOR x00 -> z00\n" == Err "line 3, column 5: expected AND, OR or XOR, got 'N'"

test "no blank line" := parsed "x00: 1\nx00 OR x00 -> z00\n" == Err "line 2, column 4: expected ': ' or a blank line before this line, got ' OR'"

-- A wire with no value: the gate waits for ever.
test "a gate missing an input never fires" := solvePart1 (deviceOf "x00: 1\n\nx00 AND y00 -> z00\n") == None

-- Two gates feeding each other wait for ever, and the rest still settle.
test "a loop settles nothing in it" :=
  let looped := deviceOf "x00: 1\n\naaa AND x00 -> bbb\nbbb OR x00 -> aaa\nx00 XOR x00 -> z00\n"
  solvePart1 looped == Some 0 && valueOf looped "aaa" == None && valueOf looped "bbb" == None

test "a loop through a z wire" := solvePart1 (deviceOf "x00: 1\n\nz01 AND x00 -> z00\nz00 OR x00 -> z01\n") == None

test "a missing z wire counts as 0" := solvePart1 (deviceOf "x00: 1\n\nx00 OR x00 -> z02\n") == Some 4

test "gates fire in any order" := solvePart1 (deviceOf "x00: 1\ny00: 1\n\nbbb XOR aaa -> z01\naaa AND x00 -> bbb\nx00 XOR y00 -> aaa\nx00 AND y00 -> z00\n") == Some 1

test "bits" := fromBits [True, False, True, True] == 13 && fromBits [] == 0

-- A ripple-carry adder of `bits` bits, as the program expects it, with
-- the other wires named after their part and bit: p03 for x03 XOR y03.
def wireAt (part: Text) (bit: Nat): Wire := Other "${part}${twoDigits bit}"

def gateOf (left: Wire) (operation: Operation) (right: Wire) (output: Wire): Gate := { left, operation, right, output }

def carryOut (bits: Nat) (bit: Nat): Wire := if bit + 1 == bits then Z bits else wireAt "c" bit

def adder (bits: Nat): List Gate :=
  List.range bits
    |> .flatMap (bit =>
      if bit == 0 then [gateOf (X 0) Xor (Y 0) (Z 0), gateOf (X 0) And (Y 0) (carryOut bits 0)]
      else [
        gateOf (X bit) Xor (Y bit) (wireAt "p" bit),
        gateOf (Y bit) And (X bit) (wireAt "g" bit),
        gateOf (carryOut bits (bit - 1)) Xor (wireAt "p" bit) (Z bit),
        gateOf (wireAt "p" bit) And (carryOut bits (bit - 1)) (wireAt "t" bit),
        gateOf (wireAt "g" bit) Or (wireAt "t" bit) (carryOut bits bit)
      ])

def inputs (bits: Nat) (x: Nat) (y: Nat): List (Wire, Bool) :=
  List.append (List.range bits |> .map (bit => (X bit, Nat.testBit x bit))) (List.range bits |> .map (bit => (Y bit, Nat.testBit y bit)))

def sumOf (bits: Nat) (gates: List Gate) (x: Nat) (y: Nat): Option Nat := solvePart1 { initial = inputs bits x y, gates }

def withSwaps (bits: Nat) (swaps: List (Text, Text)): Device :=
  { initial = inputs bits 0 0, gates = applySwaps (adder bits) (swaps.map (((first, second)) => (Wire.ofName first, Wire.ofName second))) }

test "the adder adds" :=
  [(0, 0), (1, 1), (13, 11), (255, 1), (170, 85), (255, 255)].all (((x, y)) => sumOf 8 (adder 8) x y == Some (x + y))

test "a 45-bit adder adds" := sumOf 45 (adder 45) 35184372088831 12345678901 == Some (35184372088831 + 12345678901)

test "the adder is an adder" := [1, 2, 3, 8, 45].all (bits => isAdder (adder bits) bits)
test "a one-bit adder" := sumOf 1 (adder 1) 1 1 == Some 2
test "no swaps needed" := solvePart2 (withSwaps 8 []) == Some ""
test "an adder of no bits isn't one" := !(isAdder [] 0)

-- One swap of each kind within a bit, four bits.
test "four swaps within bits" :=
  solvePart2 (withSwaps 45 [("z05", "c05"), ("p10", "g10"), ("z20", "t20"), ("p30", "c30")]) == Some "c05,c30,g10,p10,p30,t20,z05,z20"

test "z swapped with the carry, and the generated with the passed" :=
  solvePart2 (withSwaps 16 [("z03", "g03"), ("p07", "t07"), ("c11", "t11"), ("p13", "z13")]) == Some "c11,g03,p07,p13,t07,t11,z03,z13"

test "swaps across bits" :=
  solvePart2 (withSwaps 16 [("p04", "c09"), ("z12", "t02"), ("g06", "p06"), ("z00", "z15")]) == Some "c09,g06,p04,p06,t02,z00,z12,z15"

-- Swapped outputs that leave the adder adding can't be found.
test "swaps that change nothing" :=
  let swapped := withSwaps 8 [("g03", "t03"), ("p05", "c04")]
  solvePart2 swapped == Some "" && sumOf 8 swapped.gates 200 100 == Some 300

test "a swap that makes a loop" :=
  let looped := withSwaps 8 [("p03", "t03")]
  sumOf 8 looped.gates 200 100 == None && solvePart2 looped == Some "p03,t03"

test "more than four swaps" := solvePart2 (withSwaps 16 [("z01", "c01"), ("z03", "c03"), ("z05", "c05"), ("z07", "c07"), ("z09", "c09")]) == None

test "the repaired adder adds" :=
  let broken := withSwaps 16 [("z03", "g03"), ("p07", "t07"), ("c11", "t11"), ("p13", "z13")]
  let fixed := applySwaps broken.gates (repair 4 16 broken.gates [] |> .getOrElse [])
  sumOf 16 broken.gates 4660 22136 != Some 26796 && sumOf 16 fixed 4660 22136 == Some 26796

-- Three-bit adders where none of the swaps suggested for the first fault
-- leads anywhere, so the swap comes from the wires of the faulty bit.
test "four swaps crowded into three bits" :=
  solvePart2 (withSwaps 3 [("p01", "g01"), ("z00", "c01"), ("z03", "z01"), ("z02", "c00")]) == Some "c00,c01,g01,p01,z00,z01,z02,z03"

test "four swaps crowded into three bits, another" :=
  solvePart2 (withSwaps 3 [("z03", "c00"), ("p01", "g01"), ("t01", "z01"), ("c01", "z00")]) == Some "c00,c01,g01,p01,t01,z00,z01,z03"
