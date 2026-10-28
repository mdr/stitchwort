-- Day 24 as the puzzle states it: a wire carries a value if it starts with
-- one, or if a gate outputs onto it once both its inputs carry values, by
-- the rules for AND, OR and XOR. The device outputs the number whose bits
-- are the values on the z wires. Part 2's device adds if, for any numbers
-- on the x and y wires, it outputs their sum. The proofs (Proofs/) show the
-- program's number is the one the device outputs, and that the swaps part 2
-- returns make the device add.

namespace Aoc.Year2024.Day24.Spec
import Aoc.Year2024.Day24 (..)
import Std (List, Nat)

-- "AND gates output 1 if both inputs are 1 ... OR gates output 1 if one or
-- both inputs is 1 ... XOR gates output 1 if the inputs are different".
def gateOutput (operation: Operation) (left: Bool) (right: Bool): Bool :=
  match operation with
    | And => left == True ∧ right == True
    | Or => left == True ∨ right == True
    | Xor => left != right

-- `Carries device wire value`: the wire ends up carrying the value. "x00:
-- 1 means that the wire named x00 starts with the value 1", and "Gates wait
-- until both inputs are received before producing output".
type Carries (device: Device): Wire → Bool → Prop =
  | Starts [wire: Wire] [value: Bool] (given: (wire, value) ∈ device.initial): Carries device wire value
  | Fires [wire: Wire] [value: Bool] (gate: Gate) (wired: gate ∈ device.gates) (onto: gate.output = wire) (left: Bool) (right: Bool)
    (leftCarries: Carries device gate.left left) (rightCarries: Carries device gate.right right) (output: value = gateOutput gate.operation left right):
    Carries device wire value

-- "the system is trying to produce a number by combining the bits on all
-- wires starting with z. z00 is the least significant bit, then z01, then
-- z02, and so on": bit `bit` of the number is the value on the z wire of
-- that bit, and 0 where there is no such wire.
def Outputs (device: Device) (number: Nat): Prop :=
  ((bit: Nat) → Z bit ∈ device.wires → Carries device (Z bit) (Nat.testBit number bit))
    ∧ ((bit: Nat) → Z bit ∉ device.wires → Nat.testBit number bit = False)

-- "treating the bits on wires starting with x as one binary number,
-- treating the bits on wires starting with y as a second binary number":
-- the wires starting with `x` and `y`, `bits` of each.
def inputsFor (bits: Nat) (x: Nat) (y: Nat): List (Wire, Bool) :=
  List.append (List.range bits |> .map (bit => (X bit, Nat.testBit x bit))) (List.range bits |> .map (bit => (Y bit, Nat.testBit y bit)))

-- "for any combination of bits on wires starting with x and wires starting
-- with y, the sum of the two numbers those bits represent should be
-- produced as a binary number on the wires starting with z".
def Adds (bits: Nat) (gates: List Gate): Prop :=
  (x: Nat) → (y: Nat) → x < Nat.pow 2 bits → y < Nat.pow 2 bits → Outputs ({ initial = inputsFor bits x y, gates }) (x + y)

-- "Each wire is connected to at most one gate output", and the wires that
-- start with a value aren't: they are "inputs to the entire system".
def WellFormed (device: Device): Prop :=
  List.Distinct (device.gates.map (.output))
    ∧ List.Distinct (device.initial.map (.fst))
    ∧ ((gate: Gate) → gate ∈ device.gates → gate.output ∉ device.initial.map (.fst))
