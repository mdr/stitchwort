--| Advent of Code 2021, day 16: a transmission, one line of hexadecimal,
--| holds one packet in binary (four bits a digit). A packet starts with a
--| three-bit version and a three-bit type id. Type 4 is a literal number,
--| written in groups of four bits, each after a bit saying whether another
--| group follows. Any other type is an operator holding sub-packets: either
--| their total length in bits (15 bits) or their number (11 bits) comes
--| first, after a bit saying which. Part 1 adds up the version of every
--| packet; part 2 evaluates the outermost one, each operator type a
--| different operation (sum, product, minimum, maximum, and three
--| comparisons giving 1 or 0).
--|
--|   $ cd aoc && stitchwort run Aoc.Year2021.Day16.main < inputs/2021/day16.txt
--|
--| The puzzle input is committed in aoc/inputs/2021/.
--|
--| The decoder reads the bits into a tree of packets, and both parts are
--| folds over the tree. The spec (Spec/Spec.sw) writes a tree out as bits,
--| as the puzzle describes, and the proofs (Proofs/) show the decoder is
--| the encoding's inverse: what it reads is a well-formed tree whose bits
--| start the input, and it reads every well-formed tree back from its bits.
--| The tests are in `Aoc.Year2021.Day16.Tests` (Tests/). `run` checks
--| neither.

namespace Aoc.Year2021.Day16
import Std (Fail, IO, List, Nat, Option, Parse, Text)

def main(): {IO, Fail} () :=
  let packet := parsePacket IO.readAll()
  IO.print "Part 1: ${solvePart1 packet}"
  IO.print "Part 2: ${solvePart2 packet}"

--| The operator types, by type id: 0, 1, 2, 3, then 5, 6 and 7.
type Operation = | Sum | Product | Minimum | Maximum | GreaterThan | LessThan | EqualTo

--| How an operator says where its sub-packets end: length type id 0 gives
--| their total length in bits, 1 their number.
type LengthType = | TotalLength | Count

--| A packet as written: a literal keeps its groups of four bits (each a
--| number below 16), an operator its length type, so that a packet's bits
--| are fixed by the tree.
type Packet =
  | Literal (version: Nat) (groups: List Nat)
  | Operator (version: Nat) (operation: Operation) (lengthType: LengthType) (subPackets: List Packet)

--| The operation for a type id other than 4.
def operationOf: Nat → Option Operation := match some
  | 0 => Sum
  | 1 => Product
  | 2 => Minimum
  | 3 => Maximum
  | 5 => GreaterThan
  | 6 => LessThan
  | 7 => EqualTo

--| A hexadecimal digit's value.
def hexValue: Char → Option Nat := match some
  | '0' => 0
  | '1' => 1
  | '2' => 2
  | '3' => 3
  | '4' => 4
  | '5' => 5
  | '6' => 6
  | '7' => 7
  | '8' => 8
  | '9' => 9
  | 'A' => 10
  | 'B' => 11
  | 'C' => 12
  | 'D' => 13
  | 'E' => 14
  | 'F' => 15

--| A digit's four bits, the most significant first.
def digitBits (value: Nat): List Bool := [Nat.testBit value 3, Nat.testBit value 2, Nat.testBit value 1, Nat.testBit value 0]

--| The transmission's bits.
def readBits (input: Text): {Fail} List Bool := bitsOfDigits (readDigits input)

--| The value of each hexadecimal digit of the (trimmed) input.
def readDigits (input: Text): {Fail} List Nat := Parse.line input.trim (() => Parse.many hexDigit)

--| One hexadecimal digit's value.
def hexDigit(): {Parse} Nat :=
  let char := Parse.satisfy "a hexadecimal digit" (char => (hexValue char).isSome)
  Parse.need (hexValue char) "expected a hexadecimal digit"

def bitsOfDigits (digits: List Nat): List Bool := digits.flatMap digitBits

--| The first `count` bits, and the bits after them; none if there are
--| fewer.
def splitField (count: Nat) (bits: List Bool): Option (List Bool, List Bool) :=
  let field := bits.take count
  if field.length == count then Some (field, bits.drop count) else None

--| The first `count` bits as a number, and the bits after them.
def readNumber (count: Nat) (bits: List Bool): Option (Nat, List Bool) :=
  match splitField count bits with
    | Some (field, rest) => Some (Nat.fromBits field, rest)
    | None => None

--| A literal's groups: each is a bit saying whether another follows, then
--| four bits.
def readGroups: List Bool → Option (List Nat, List Bool)
  | [more, a, b, c, d, ..rest] =>
    let group := Nat.fromBits [a, b, c, d]
    if more then
      match readGroups rest with
        | Some (groups, after) => Some ([group, ..groups], after)
        | None => None
    else Some ([group], rest)
  | _ => None

--| How many packets are still to read: a number of them, or as many as fill
--| the bits.
type Wanted = | Packets (count: Nat) | Filling

--| Whether there is another packet to read, and then what is wanted after
--| it.
def nextWanted: Wanted → List Bool → Option Wanted
  | Packets 0, _ => None
  | Packets (Succ count), _ => Some (Packets count)
  | Filling, [] => None
  | Filling, [_, .._] => Some Filling

--| Puts a packet in front of the ones read after it.
def andThen (packet: Packet): Option (List Packet, List Bool) → Option (List Packet, List Bool) :=
  match some | Some (packets, rest) => ([packet, ..packets], rest)

--| Reads the packets wanted from the bits, and gives back the bits after
--| them; none if the bits don't hold them. Every call reads from fewer bits,
--| checked as it goes.
def readPackets (wanted: Wanted) (bits: List Bool): Option (List Packet, List Bool)
    decreasing bits.length
:=
  match nextWanted wanted bits with
    | None => Some ([], bits)
    | Some later =>
      match bits with
        | [v1, v2, v3, t1, t2, t3, ..rest] =>
          let version := Nat.fromBits [v1, v2, v3]
          match operationOf (Nat.fromBits [t1, t2, t3]) with
            | None =>
              match readGroups rest with
                | None => None
                | Some (groups, after) =>
                  if shorter: after.length < bits.length then andThen (Literal version groups) (readPackets later after) else None
            | Some operation =>
              match rest with
                | [False, ..fields] =>
                  match readNumber 15 fields with
                    | None => None
                    | Some (length, after) =>
                      match splitField length after with
                        | None => None
                        | Some (inside, following) =>
                          if shorter: inside.length < bits.length then
                            match readPackets Filling inside with
                              | None => None
                              | Some (subPackets, _) =>
                                if shorterAfter: following.length < bits.length then
                                  andThen (Operator version operation TotalLength subPackets) (readPackets later following)
                                else None
                          else None
                | [True, ..fields] =>
                  match readNumber 11 fields with
                    | None => None
                    | Some (count, after) =>
                      if shorter: after.length < bits.length then
                        match readPackets (Packets count) after with
                          | None => None
                          | Some (subPackets, following) =>
                            if shorterAfter: following.length < bits.length then
                              andThen (Operator version operation Count subPackets) (readPackets later following)
                            else None
                      else None
                | [] => None
        | _ => None

--| One packet, and the bits after it.
def readPacket (bits: List Bool): Option (Packet, List Bool) :=
  readPackets (Packets 1) bits |> match some | Some ([packet], rest) => (packet, rest)

--| The outermost packet of the transmission. Only zero bits may follow it
--| (the padding), and it checks the puzzle's promise about the operators it
--| evaluates.
def parsePacket (input: Text): {Fail} Packet := decodeTransmission (readBits input)

--| The bits are all zero.
def zeroBits (bits: List Bool): Bool := bits.all not

def decodeTransmission (bits: List Bool): {Fail} Packet :=
  match readPacket bits with
    | Some ((packet, rest)) =>
      match zeroBits rest with
        | True => checkOperators packet
        | False => Fail.fail "the bits after the packet aren't all zero padding"
    | None => Fail.fail "the transmission isn't a packet"

--| How many sub-packets an operation takes: none if any number does.
def arity: Operation → Option Arity := match some
  | Minimum => AtLeastOne
  | Maximum => AtLeastOne
  | GreaterThan => Two
  | LessThan => Two
  | EqualTo => Two

type Arity = | AtLeastOne | Two

def fitsArity (count: Nat): Option Arity → Bool
  | Some AtLeastOne => count != 0
  | Some Two => count == 2
  | None => True

--| The first operator, outermost first, with a number of sub-packets its
--| operation can't take: its operation and that number.
def badOperator: Packet → Option (Operation, Nat)
  | Literal _ _ => None
  | Operator _ operation _ subPackets =>
    if fitsArity subPackets.length (arity operation) then badOperatorIn subPackets else Some (operation, subPackets.length)

def badOperatorIn: List Packet → Option (Operation, Nat)
  | [] => None
  | [packet, ..rest] =>
    match badOperator packet with
      | None => badOperatorIn rest
      | found => found

def operationId: Operation → Nat
  | Sum => 0
  | Product => 1
  | Minimum => 2
  | Maximum => 3
  | GreaterThan => 5
  | LessThan => 6
  | EqualTo => 7

--| A minimum or maximum takes at least one sub-packet, a comparison two.
def checkOperators (packet: Packet): {Fail} Packet :=
  match badOperator packet with
    | None => packet
    | Some ((operation, count)) => Fail.fail "an operator of type ${operationId operation} has ${count} sub-packets"

--| The sum of the versions of a packet and every packet inside it.
def versionSum: Packet → Nat
  | Literal version _ => version
  | Operator version _ _ subPackets => version + versionSums subPackets

def versionSums: List Packet → Nat
  | [] => 0
  | [packet, ..rest] => versionSum packet + versionSums rest

def solvePart1 (packet: Packet): Nat := versionSum packet

--| A packet's value.
def evaluate: Packet → Nat
  | Literal _ groups => groups.foldLeft 0 (value group => value * 16 + group)
  | Operator _ operation _ subPackets => apply operation (evaluateAll subPackets)

def evaluateAll: List Packet → List Nat
  | [] => []
  | [packet, ..rest] => [evaluate packet, ..evaluateAll rest]

--| An operation on its sub-packets' values. A comparison looks at the first
--| two.
def apply (operation: Operation) (values: List Nat): Nat :=
  match operation, values with
    | Sum, values => values.sum
    | Product, values => values.product
    | Minimum, values => values.minimum.getOrElse 0
    | Maximum, values => values.maximum.getOrElse 0
    | GreaterThan, [a, b, .._] => if a > b then 1 else 0
    | LessThan, [a, b, .._] => if a < b then 1 else 0
    | EqualTo, [a, b, .._] => if a == b then 1 else 0
    | _, _ => 0

def solvePart2 (packet: Packet): Nat := evaluate packet
