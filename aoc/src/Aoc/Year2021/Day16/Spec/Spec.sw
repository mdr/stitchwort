--| Day 16 as the puzzle states it: how a packet is written in bits, and what
--| the two parts ask of the packet. The packet type is the program's: an
--| operator holds one or more sub-packets and a comparison two, as the
--| puzzle says, and a literal keeps its groups and an operator its length
--| type, so that the bits of a packet are fixed. Nothing else is shared
--| with it. The proofs
--| (Proofs/) show the program's decoder reads exactly these encodings, and
--| that its answers are these.

namespace Aoc.Year2021.Day16.Spec
import Aoc.Year2021.Day16 (Comparison, LengthType, Operation, OperatorType, Packet)
import Std (List, Nat, NonEmptyList, Option)

--| The puzzle's hexadecimal digits and their bits.
def hexDigitBits: Char → Option (List Bool) := match some
  | '0' => [False, False, False, False]
  | '1' => [False, False, False, True]
  | '2' => [False, False, True, False]
  | '3' => [False, False, True, True]
  | '4' => [False, True, False, False]
  | '5' => [False, True, False, True]
  | '6' => [False, True, True, False]
  | '7' => [False, True, True, True]
  | '8' => [True, False, False, False]
  | '9' => [True, False, False, True]
  | 'A' => [True, False, True, False]
  | 'B' => [True, False, True, True]
  | 'C' => [True, True, False, False]
  | 'D' => [True, True, False, True]
  | 'E' => [True, True, True, False]
  | 'F' => [True, True, True, True]

--| A transmission's bits: each character a hexadecimal digit, written as
--| its four bits; none if a character isn't one.
def transmissionBits: List Char → Option (List Bool)
  | [] => Some []
  | [char, ..rest] =>
    match hexDigitBits char, transmissionBits rest with
      | Some bits, Some more => Some (bits ++ more)
      | _, _ => None

--| The type id of each operator.
def typeId: OperatorType → Nat
  | Calculation Sum => 0
  | Calculation Product => 1
  | Calculation Minimum => 2
  | Calculation Maximum => 3
  | Comparing GreaterThan => 5
  | Comparing LessThan => 6
  | Comparing EqualTo => 7

--| A literal's groups: each is four bits after a bit that is 1, except the
--| last group's, which is 0.
def groupBits (groups: NonEmptyList Nat): List Bool := groupBitsFrom groups.head groups.tail

--| The bits of a group and the groups after it.
def groupBitsFrom: Nat → List Nat → List Bool
  | group, [] => [False, ..Nat.toBits 4 group]
  | group, [next, ..rest] => [True, ..Nat.toBits 4 group ++ groupBitsFrom next rest]

--| A packet's bits: its version in three bits, its type id in three bits (4
--| for a literal), then a literal's groups; or an operator's length type id
--| (0 or 1), the length of its sub-packets in 15 bits or their number in 11
--| bits, and the sub-packets.
def encode: Packet → List Bool
  | Literal version groups => Nat.toBits 3 version ++ Nat.toBits 3 4 ++ groupBits groups
  | Operator version operation lengthType ({ head = first, tail = rest }) =>
    operatorBits version (typeId (Calculation operation)) lengthType (Succ rest.length) (encode first ++ encodeAll rest)
  | Comparator version comparison lengthType first second =>
    operatorBits version (typeId (Comparing comparison)) lengthType 2 (encode first ++ encode second)

--| Packets one after another.
def encodeAll: List Packet → List Bool
  | [] => []
  | [packet, ..rest] => encode packet ++ encodeAll rest

--| An operator's bits, given the bits of its count sub-packets.
def operatorBits (version code: Nat) (lengthType: LengthType) (count: Nat) (subBits: List Bool): List Bool :=
  Nat.toBits 3 version ++ Nat.toBits 3 code ++ lengthField lengthType count subBits

--| The length type id, then the length of the sub-packets' bits in 15 bits
--| or their number in 11 bits, and the sub-packets' bits.
def lengthField: LengthType → Nat → List Bool → List Bool
  | TotalLength, _, subBits => [False, ..Nat.toBits 15 subBits.length ++ subBits]
  | Count, count, subBits => [True, ..Nat.toBits 11 count ++ subBits]

--| A packet whose numbers fit their fields: the version in three bits, at
--| least one group, each in four bits, and the sub-packets' length or
--| number in its 15 or 11 bits. Only these have the encoding above.
def wellFormed: Packet → Bool
  | Literal version groups => version < 8 && groups.all (group => group < 16)
  | Operator version _ lengthType ({ head = first, tail = rest }) =>
    version < 8
      && fitsLength lengthType (Succ rest.length) (encode first ++ encodeAll rest)
      && wellFormed first
      && allWellFormed rest
  | Comparator version _ lengthType first second =>
    version < 8 && fitsLength lengthType 2 (encode first ++ encode second) && wellFormed first && wellFormed second

def allWellFormed: List Packet → Bool
  | [] => True
  | [packet, ..rest] => wellFormed packet && allWellFormed rest

--| Whether the sub-packets' bits, or their number, fit the 15 or 11 bits
--| that give it.
def fitsLength: LengthType → Nat → List Bool → Bool
  | TotalLength, _, subBits => subBits.length < 32768
  | Count, count, _ => count < 2048

--| A packet and every packet inside it, at any depth.
def packetsIn: Packet → List Packet
  | Literal version groups => [Literal version groups]
  | Operator version operation lengthType ({ head = first, tail = rest }) =>
    [Operator version operation lengthType (NonEmptyList.cons first rest), ..packetsIn first ++ packetsInAll rest]
  | Comparator version comparison lengthType first second =>
    [Comparator version comparison lengthType first second, ..packetsIn first ++ packetsIn second]

def packetsInAll: List Packet → List Packet
  | [] => []
  | [packet, ..rest] => packetsIn packet ++ packetsInAll rest

def versionOf: Packet → Nat
  | Literal version _ => version
  | Operator version _ _ _ => version
  | Comparator version _ _ _ _ => version

--| Part 1: the versions of all the packets, added up.
def versionTotal (packet: Packet): Nat := (packetsIn packet).sumBy versionOf

--| Part 2: a packet's value. A literal's is its groups' bits read as one
--| binary number; an operator's is computed from its sub-packets' values.
type HasValue: Packet → Nat → Prop =
  | LiteralValue
      (version: Nat)
      (groups: NonEmptyList Nat): HasValue
    (Literal version groups)
    (Nat.fromBits (groups.toList.flatMap (Nat.toBits 4)))
  | OperationValue
      (each: Values operands.toList values)
      (computed: Computes operation values value): HasValue (Operator version operation lengthType operands) value
  | ComparisonValue
      (firstValue: HasValue first firstNumber)
      (secondValue: HasValue second secondNumber)
      (compared: Compares comparison firstNumber secondNumber value): HasValue
    (Comparator version comparison lengthType first second)
    value

--| Each packet's value, in order.
type Values: List Packet → List Nat → Prop =
  | NoValues: Values [] []
  | NextValue (first: HasValue packet value) (rest: Values packets values): Values [packet, ..packets] [value, ..values]

--| What each operation makes of its sub-packets' values: their sum, their
--| product, or their minimum or maximum (one of them, and no other below or
--| above it).
type Computes: Operation → List Nat → Nat → Prop =
  | SumOf (values: List Nat): Computes Sum values values.sum
  | ProductOf (values: List Nat): Computes Product values values.product
  | MinimumOf
      (member: value ∈ values)
      (least: ∀ (other: Nat) => other ∈ values → value ≤ other): Computes Minimum values value
  | MaximumOf
      (member: value ∈ values)
      (most: ∀ (other: Nat) => other ∈ values → other ≤ value): Computes Maximum values value

--| What each comparison makes of its two sub-packets' values: 1 if the
--| first is greater than, less than, or equal to the second, and 0 if not.
type Compares: Comparison → Nat → Nat → Nat → Prop =
  | Greater (first: Nat) (second: Nat) (greater: second < first): Compares GreaterThan first second 1
  | NotGreater (first: Nat) (second: Nat) (notGreater: first ≤ second): Compares GreaterThan first second 0
  | Less (first: Nat) (second: Nat) (less: first < second): Compares LessThan first second 1
  | NotLess (first: Nat) (second: Nat) (notLess: second ≤ first): Compares LessThan first second 0
  | Equal (first: Nat): Compares EqualTo first first 1
  | NotEqual (first: Nat) (second: Nat) (different: first ≠ second): Compares EqualTo first second 0
