-- Advent of Code 2024, day 24: a device of AND, OR and XOR gates joined by
-- wires, some of which start with values. Part 1 lets the gates settle and
-- reads the wires starting with z as a binary number. Part 2: the device is
-- meant to add the numbers on the x wires and the y wires onto the z wires,
-- but four pairs of gates have their outputs swapped; it names the eight
-- wires, sorted and joined with commas.
--
--   $ cd aoc && stitchwort run Aoc.Year2024.Day24.main < examples/2024/day24.txt
--
-- The proofs are in `Aoc.Year2024.Day24.Proofs` (Proofs/) and the tests in
-- `Aoc.Year2024.Day24.Tests` (Tests/); `run` checks neither.

namespace Aoc.Year2024.Day24
import Std (Bool, Char, Fail, IO, List, Map, Nat, Option, Parse, Text, Void)
import Std.Parse (label, lines, pick, section, takeWhile1, text)

def main(): {IO, Fail} () :=
  let device := parseDevice IO.readAll()
  IO.print "Part 1: ${solvePart1 device |> .fold "none: a wire starting with z gets no value" (number => "${number}")}"
  IO.print "Part 2: ${solvePart2 device |> .getOrElse "no four swaps make an adder"}"

-- A wire: bit `bit` of the first number (x), the second (y) or the result
-- (z), or any other.
type Wire =
  | X (bit: Nat)
  | Y (bit: Nat)
  | Z (bit: Nat)
  | Other (name: Text)

type Operation =
  | And
  | Or
  | Xor

type Gate = { left: Wire, operation: Operation, right: Wire, output: Wire }

-- The wires that start with a value, and the gates.
type Device = { initial: List (Wire, Bool), gates: List Gate }

-- x, y or z and two digits name a bit: `x07` is `X 7`.
def Wire.ofName (name: Text): Wire :=
  match name.toList with
    | [first, tens, units] =>
      match (tens.digitValue, units.digitValue) with
        | (Some high, Some low) =>
          match first with
            | 'x' => X (10 * high + low)
            | 'y' => Y (10 * high + low)
            | 'z' => Z (10 * high + low)
            | _ => Other name
        | _ => Other name
    | _ => Other name

-- At least two digits: `7` is `07`.
def twoDigits (number: Nat): Text := if number < 10 then "0${number}" else "${number}"

def Wire.name (wire: Wire): Text :=
  match wire with
    | X bit => "x${twoDigits bit}"
    | Y bit => "y${twoDigits bit}"
    | Z bit => "z${twoDigits bit}"
    | Other name => name

def wire(): {Parse} Wire := takeWhile1 "a wire name" Char.isAsciiAlphanumeric |> Wire.ofName

-- `x00: 1`.
def initialValue(): {Parse} (Wire, Bool) :=
  let name := wire()
  text ": "
  let value := label "0 or 1" (() => pick [("0", False), ("1", True)])
  (name, value)

-- `x00 AND y00 -> z00`.
def gate(): {Parse} Gate :=
  let left := wire()
  text " "
  let operation := label "AND, OR or XOR" (() => pick [("AND", And), ("OR", Or), ("XOR", Xor)])
  text " "
  let right := wire()
  text " -> "
  let output := wire()
  { left, operation, right, output }

def device(): {Parse} Device :=
  let initial := section initialValue
  let gates := lines gate
  { initial, gates }

def parseDevice (input: Text): {Fail} Device := Parse.all input device

-- What a gate outputs for its two inputs.
def Operation.apply (operation: Operation) (left: Bool) (right: Bool): Bool :=
  match operation with
    | And => left ∧ right
    | Or => left ∨ right
    | Xor => Bool.xor left right

type Values = Map Wire Bool

-- A gate's output once both its inputs have values.
def Gate.fire (gate: Gate) (values: Values): Option Bool :=
  values.get gate.left |> .flatMap (left => values.get gate.right |> .map (right => gate.operation.apply left right))

def Gate.ready (gate: Gate) (values: Values): Bool := (gate.fire values).isSome

-- Each ready gate puts its output on its wire.
def fireAll (values: Values) (ready: List Gate): Values :=
  ready.foldLeft values (settled gate => settled.insert gate.output ((gate.fire values).getOrElse False))

-- Filtering keeps at most what there was.
theorem filterNoLonger: (xs: List a) → (p: a → Bool) → (xs.filter p).length ≤ xs.length
  | Nil, p => rfl
  | Cons x rest, p =>
    match p x with
      | True => filterNoLonger rest p
      | False => omega [filterNoLonger rest p]

-- If some of `xs` pass `p`, fewer than all of them fail it.
theorem filterNotShorter: (xs: List a) → (p: a → Bool) → (first: a) → (rest: List a) → xs.filter p = Cons first rest →
    (xs.filter (x => ¬(p x))).length < xs.length
  | Nil, p, first, rest, passed => Void.exfalso (List.nilNotCons first rest passed)
  | Cons x more, p, first, rest, passed =>
    match passes: p x with
      | True => omega [filterNoLonger more (x => ¬(p x))]
      | False => filterNotShorter more p first rest passed

-- The gates settle a round at a time: every gate whose inputs both have
-- values fires, and the rest wait, until none is ready. Gates in a loop
-- never are, so they wait for ever, and the rounds stop.
def settle (values: Values) (waiting: List Gate): Values
    decreasing waiting.length
:=
  match ready: waiting.filter (gate => gate.ready values) with
    | Nil => values
    | Cons first rest =>
      settle (fireAll values (Cons first rest)) (waiting.filter (gate => ¬(gate.ready values)))
        [decreasing := filterNotShorter waiting (gate => gate.ready values) first rest ready]

def Device.wires (device: Device): List Wire :=
  List.append (device.initial.map (.fst)) (device.gates.flatMap (gate => [gate.left, gate.right, gate.output]))

-- One more than the highest bit `bitOf` finds among the wires.
def bitCount (bitOf: Wire → Option Nat) (wires: List Wire): Nat :=
  wires.foldLeft 0 (count wire => bitOf wire |> .fold count (bit => Nat.max count (bit + 1)))

def Wire.zBit (wire: Wire): Option Nat :=
  match wire with
    | Z bit => Some bit
    | _ => None

def Wire.xBit (wire: Wire): Option Nat :=
  match wire with
    | X bit => Some bit
    | _ => None

-- All the values, if every option has one.
def allSome: List (Option a) → Option (List a)
  | Nil => Some Nil
  | Cons first rest => first.flatMap (value => allSome rest |> .map (Cons value))

-- The number with these bits, lowest first.
def fromBits: List Bool → Nat
  | Nil => 0
  | Cons bit rest => bit.toNat + 2 * fromBits rest

-- The bits on the z wires, lowest first, a missing z wire counting as 0,
-- if every z wire has a value.
def zBits (device: Device) (values: Values): Option (List Bool) :=
  let wires := device.wires
  List.range (bitCount Wire.zBit wires)
    |> .map (bit => if Z bit ∈ wires then values.get (Z bit) else Some False)
    |> allSome

def Device.settled (device: Device): Values := settle (Map.fromList device.initial) device.gates

-- The number on the z wires once the gates settle, unless one of them
-- gets no value.
def solvePart1 (device: Device): Option Nat := zBits device device.settled |> .map fromBits

-- Part 2. The device should be a ripple-carry adder: bit 0 is a half
-- adder, x00 XOR y00 -> z00 and x00 AND y00 -> the carry, and each later
-- bit a full adder of x, y and the carry from below:
--
--   x XOR y -> partial          partial XOR carry -> z
--   x AND y -> generated        partial AND carry -> passed
--   generated OR passed -> the carry to the next bit
--
-- and the last carry is the z wire above the top bit.

-- The output of the gate doing `operation` on `a` and `b`, either way round.
def outputOf (gates: List Gate) (operation: Operation) (a: Wire) (b: Wire): Option Wire :=
  gates.find (gate => gate.operation == operation ∧ (gate.left == a ∧ gate.right == b ∨ gate.left == b ∧ gate.right == a))
    |> .map (.output)

-- The other input of a gate doing `operation` with `input` as one input.
def partnerOf (gates: List Gate) (operation: Operation) (input: Wire): Option Wire :=
  gates
    |> .find (gate => gate.operation == operation ∧ (gate.left == input ∨ gate.right == input))
    |> .map (gate => if gate.left == input then gate.right else gate.left)

-- What checking a bit found: it is right and carries on this wire, or it
-- is faulty, with the swaps that might fix it, most likely first (none if
-- no swap explains the fault).
type BitCheck =
  | Carries (carry: Wire)
  | Faulty (fixes: List (Wire, Wire))

-- The two inputs of a gate doing `operation` should be `trusted` and
-- `suspect`, and no gate has both. The gate with `trusted` names what
-- `suspect` should be, or the gate with `suspect` names what `trusted`
-- should be.
def missingInput (gates: List Gate) (operation: Operation) (trusted: Wire) (suspect: Wire): BitCheck :=
  let fromTrusted := partnerOf gates operation trusted |> .fold [] (other => [(suspect, other)])
  let fromSuspect := partnerOf gates operation suspect |> .fold [] (other => [(trusted, other)])
  Faulty (List.append fromTrusted fromSuspect)

-- Bit 0, the half adder.
def checkHalfAdder (gates: List Gate): BitCheck :=
  match (outputOf gates Xor (X 0) (Y 0), outputOf gates And (X 0) (Y 0)) with
    | (Some sum, Some carry) => if sum == Z 0 then Carries carry else Faulty [(sum, Z 0)]
    | _ => Faulty []

-- A later bit, the full adder, with the carry from below on `carry`.
def checkFullAdder (gates: List Gate) (bit: Nat) (carry: Wire): BitCheck :=
  match (outputOf gates Xor (X bit) (Y bit), outputOf gates And (X bit) (Y bit)) with
    | (Some partial, Some generated) =>
      match (outputOf gates Xor partial carry, outputOf gates And partial carry) with
        | (Some sum, Some passed) =>
          if sum == Z bit then outputOf gates Or generated passed |> .fold (missingInput gates Or generated passed) Carries
          else Faulty [(sum, Z bit)]
        | (Some sum, None) => missingInput gates And carry partial
        | (None, _) => missingInput gates Xor carry partial
    | _ => Faulty []

-- The verdict on the bits from `bit` up, `remaining` of them, with the carry
-- into `bit` on `carry`: an adder, or the first fault found.
def checkFrom (gates: List Gate) (remaining: Nat) (bit: Nat) (carry: Wire): BitCheck :=
  match remaining with
    | Zero => if carry == Z bit then Carries carry else Faulty [(carry, Z bit)]
    | Succ fewer =>
      match checkFullAdder gates bit carry with
        | Carries next => checkFrom gates fewer (bit + 1) next
        | fault => fault

-- The verdict on a `bits`-bit adder: `Carries (Z bits)` if it is one.
def checkAdder (gates: List Gate) (bits: Nat): BitCheck :=
  match bits with
    | Zero => Faulty []
    | Succ higher =>
      match checkHalfAdder gates with
        | Carries carry => checkFrom gates higher 1 carry
        | fault => fault

-- The gates with the outputs `first` and `second` swapped.
def swapOutputs (gates: List Gate) (swap: (Wire, Wire)): List Gate :=
  let (first, second) := swap
  gates.map (gate => { gate | output = if gate.output == first then second else if gate.output == second then first else gate.output })

def applySwaps (gates: List Gate) (swaps: List (Wire, Wire)): List Gate := swaps.foldLeft gates swapOutputs

-- Each wire is the output of at most one gate, and no gate outputs onto an
-- x or y wire.
def wellWired (gates: List Gate): Bool :=
  gates.map (.output) |> .allDistinct && gates.all (gate => (gate.output.xBit.isNone ∧ gate.output.yBit.isNone))

def Wire.yBit (wire: Wire): Option Nat :=
  match wire with
    | Y bit => Some bit
    | _ => None

-- No z wire above `bits`.
def zWithin (gates: List Gate) (bits: Nat): Bool :=
  gates.all (gate => [gate.left, gate.right, gate.output].all (wire => wire.zBit.all (bit => bit ≤ bits)))

-- A `bits`-bit ripple-carry adder, wired once per wire.
def isAdder (gates: List Gate) (bits: Nat): Bool :=
  wellWired gates ∧ zWithin gates bits ∧ checkAdder gates bits == Carries (Z bits)

-- Swaps after `swaps` that make the gates an adder, at most `budget` more:
-- try each fix for the first fault in turn, and go on from there.
def repair (budget: Nat) (bits: Nat) (gates: List Gate) (swaps: List (Wire, Wire)): Option (List (Wire, Wire)) :=
  match checkAdder gates bits with
    | Faulty fixes =>
      match budget with
        | Zero => None
        | Succ fewer => fixes.findMap (fix => repair fewer bits (swapOutputs gates fix) (List.append swaps [fix]))
    | Carries carry => if isAdder gates bits then Some swaps else None

-- The swaps' wires, sorted by name and joined with commas.
def swapNames (swaps: List (Wire, Wire)): Text :=
  swaps.flatMap (((first, second)) => [first.name, second.name]) |> .sort |> .joinWith ","

-- The number of bits in each number added: one more than the highest x wire.
def Device.inputBits (device: Device): Nat := bitCount Wire.xBit device.wires

-- Four swaps that make the device an adder, if there are, as the puzzle
-- asks for them.
def solvePart2 (device: Device): Option Text :=
  repair 4 device.inputBits device.gates [] |> .map swapNames
