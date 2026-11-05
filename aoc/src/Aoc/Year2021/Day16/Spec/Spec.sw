--| Day 16 as the puzzle states it: how a packet is written in bits, and what
--| the two parts ask of the packet. The packet type is the program's (a
--| literal keeps its groups, an operator its length type, so that the bits
--| of a packet are fixed); nothing else is shared with it. The proofs
--| (Proofs/) show the program's decoder reads exactly these encodings, and
--| that its answers are these.

namespace Aoc.Year2021.Day16.Spec
import Aoc.Year2021.Day16 (LengthType, Operation, Packet)
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
def typeId: Operation → Nat
  | Sum => 0
  | Product => 1
  | Minimum => 2
  | Maximum => 3
  | GreaterThan => 5
  | LessThan => 6
  | EqualTo => 7

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
  | Operator version operation TotalLength subPackets =>
    Nat.toBits 3 version ++ Nat.toBits 3 (typeId operation) ++ [False, ..Nat.toBits 15 (encodeAll subPackets).length ++ encodeAll subPackets]
  | Operator version operation Count subPackets =>
    Nat.toBits 3 version ++ Nat.toBits 3 (typeId operation) ++ [True, ..Nat.toBits 11 subPackets.length ++ encodeAll subPackets]

--| Packets one after another.
def encodeAll: List Packet → List Bool
  | [] => []
  | [packet, ..rest] => encode packet ++ encodeAll rest

--| A packet whose numbers fit their fields: the version in three bits, at
--| least one group, each in four bits, and the sub-packets' length or
--| number in its 15 or 11 bits. Only these have the encoding above.
def wellFormed: Packet → Bool
  | Literal version groups => version < 8 && groups.all (group => group < 16)
  | Operator version _ TotalLength subPackets => version < 8 && (encodeAll subPackets).length < 32768 && allWellFormed subPackets
  | Operator version _ Count subPackets => version < 8 && subPackets.length < 2048 && allWellFormed subPackets

def allWellFormed: List Packet → Bool
  | [] => True
  | [packet, ..rest] => wellFormed packet && allWellFormed rest

--| A packet and every packet inside it, at any depth.
def packetsIn: Packet → List Packet
  | Literal version groups => [Literal version groups]
  | Operator version operation lengthType subPackets => [Operator version operation lengthType subPackets, ..packetsInAll subPackets]

def packetsInAll: List Packet → List Packet
  | [] => []
  | [packet, ..rest] => packetsIn packet ++ packetsInAll rest

def versionOf: Packet → Nat
  | Literal version _ => version
  | Operator version _ _ _ => version

--| Part 1: the versions of all the packets, added up.
def versionTotal (packet: Packet): Nat := (packetsIn packet).sumBy versionOf

--| What the puzzle promises of the operators it evaluates: a minimum or a
--| maximum has at least one sub-packet, and a comparison exactly two. (A sum
--| or product of none is 0 or 1.)
def promised: Packet → Bool
  | Literal _ _ => True
  | Operator _ operation _ subPackets => fitsOperation operation subPackets.length && allPromised subPackets

def allPromised: List Packet → Bool
  | [] => True
  | [packet, ..rest] => promised packet && allPromised rest

def fitsOperation: Operation → Nat → Bool
  | Minimum, count => 0 < count
  | Maximum, count => 0 < count
  | GreaterThan, count => count == 2
  | LessThan, count => count == 2
  | EqualTo, count => count == 2
  | _, _ => True

--| Part 2: a packet's value. A literal's is its groups' bits read as one
--| binary number; an operator's is computed from its sub-packets' values.
type HasValue: Packet → Nat → Prop =
  | LiteralValue (version: Nat) (groups: NonEmptyList Nat): HasValue (Literal version groups) (Nat.fromBits (groups.toList.flatMap (Nat.toBits 4)))
  | OperatorValue (each: Values subPackets values) (computed: Computes operation values value):
    HasValue (Operator version operation lengthType subPackets) value

--| Each packet's value, in order.
type Values: List Packet → List Nat → Prop =
  | NoValues: Values [] []
  | NextValue (first: HasValue packet value) (rest: Values packets values): Values [packet, ..packets] [value, ..values]

--| What each operator makes of its sub-packets' values: their sum, their
--| product, their minimum or maximum (one of them, and no other below or
--| above it), or 1 if the first is greater than, less than, or equal to the
--| second (of exactly two), and 0 if not.
type Computes: Operation → List Nat → Nat → Prop =
  | SumOf (values: List Nat): Computes Sum values values.sum
  | ProductOf (values: List Nat): Computes Product values values.product
  | MinimumOf (member: value ∈ values) (least: (other: Nat) → other ∈ values → value ≤ other): Computes Minimum values value
  | MaximumOf (member: value ∈ values) (most: (other: Nat) → other ∈ values → other ≤ value): Computes Maximum values value
  | Greater (first: Nat) (second: Nat) (greater: second < first): Computes GreaterThan [first, second] 1
  | NotGreater (first: Nat) (second: Nat) (notGreater: first ≤ second): Computes GreaterThan [first, second] 0
  | Less (first: Nat) (second: Nat) (less: first < second): Computes LessThan [first, second] 1
  | NotLess (first: Nat) (second: Nat) (notLess: second ≤ first): Computes LessThan [first, second] 0
  | Equal (first: Nat): Computes EqualTo [first, first] 1
  | NotEqual (first: Nat) (second: Nat) (different: first ≠ second): Computes EqualTo [first, second] 0
