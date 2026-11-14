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
--| The decoder reads the bits through a `BitReader` (Aoc.Common), a field at
--| a time, into a tree of packets, and both parts are
--| folds over the tree. The spec (Spec/Spec.sw) writes a tree out as bits,
--| as the puzzle describes, and the proofs (Proofs/) show the decoder is
--| the encoding's inverse: what it reads is a well-formed tree whose bits
--| start the input, and it reads every well-formed tree back from its bits.
--| The tests are in `Aoc.Year2021.Day16.Tests` (Tests/). `run` checks
--| neither.

namespace Aoc.Year2021.Day16
import Aoc.Common (BitReader)
import Std (Fail, IO, List, Nat, NonEmptyList, Option, Parse, Text)

def main(): {IO, Fail} () :=
  let packet := parsePacket IO.readAll()
  IO.print "Part 1: ${solvePart1 packet}"
  IO.print "Part 2: ${solvePart2 packet}"

--| What an operator does with any number (one or more) of sub-packets' values.
type Operation = | Sum | Product | Minimum | Maximum

--| What an operator does with the values of exactly two sub-packets: gives
--| 1 if the first is greater than, less than or equal to the second, else 0.
type Comparison = | GreaterThan | LessThan | EqualTo

--| The operator types, by type id: 0, 1, 2, 3, then 5, 6 and 7.
type OperatorType = | Calculation (operation: Operation) | Comparing (comparison: Comparison)

--| How an operator says where its sub-packets end: length type id 0 gives
--| their total length in bits, 1 their number.
type LengthType = | TotalLength | Count

--| A packet as written: a literal keeps its groups of four bits (each a
--| number below 16), an operator its length type, so that a packet's bits
--| are fixed by the tree. An operator holds the sub-packets its operation
--| takes: one or more, or for a comparison exactly two.
type Packet =
  | Literal (version: Nat) (groups: NonEmptyList Nat)
  | Operator (version: Nat) (operation: Operation) (lengthType: LengthType) (operands: NonEmptyList Packet)
  | Comparator (version: Nat) (comparison: Comparison) (lengthType: LengthType) (first: Packet) (second: Packet)

--| The operator type for a type id other than 4.
def operatorTypeOf: Nat → Option OperatorType := match some
  | 0 => Calculation Sum
  | 1 => Calculation Product
  | 2 => Calculation Minimum
  | 3 => Calculation Maximum
  | 5 => Comparing GreaterThan
  | 6 => Comparing LessThan
  | 7 => Comparing EqualTo

--| The operator of a type, holding the sub-packets read; none if there
--| aren't as many as the type takes.
def operatorOf (version: Nat) (operatorType: OperatorType) (lengthType: LengthType) (subPackets: List Packet):
    Option Packet :=
  match operatorType, subPackets with
    | Calculation operation, [first, ..rest] =>
      Some (Operator version operation lengthType (NonEmptyList.cons first rest))
    | Comparing comparison, [first, second] => Some (Comparator version comparison lengthType first second)
    | _, _ => None

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
def digitBits (value: Nat): List Bool := [value.testBit 3, value.testBit 2, value.testBit 1, value.testBit 0]

--| The transmission's bits.
def readBits (input: Text): {Fail} List Bool := bitsOfDigits (readDigits input)

--| The value of each hexadecimal digit of the (trimmed) input.
def readDigits (input: Text): {Fail} List Nat := Parse.line input.trim (() => Parse.many hexDigit)

--| One hexadecimal digit's value.
def hexDigit(): {Parse} Nat :=
  let char := Parse.satisfy "a hexadecimal digit" (char => (hexValue char).isSome)
  Parse.need (hexValue char) "expected a hexadecimal digit"

def bitsOfDigits (digits: List Nat): List Bool := digits.flatMap digitBits

--| A literal's groups: each is a bit saying whether another follows, then
--| four bits.
def readGroups (reader: BitReader): Option (NonEmptyList Nat, BitReader)
    decreasing reader.length
:=
  match reader.readBit with
    | None => None
    | Some (more, afterMore) =>
      match afterMore.readNumber 4 with
        | None => None
        | Some (group, after) =>
          if more then
            if shorter: after.length < reader.length then
              match readGroups after with
                | None => None
                | Some (groups, rest) => Some (NonEmptyList.cons group groups.toList, rest)
            else None
          else Some (NonEmptyList.singleton group, after)

--| How many packets are still to read: a number of them, or as many as fill
--| the bits.
type Wanted = | Packets (count: Nat) | Filling

--| Whether there is another packet to read, and then what is wanted after
--| it.
def nextWanted: Wanted → BitReader → Option Wanted
  | Packets 0, _ => None
  | Packets (Succ count), _ => Some (Packets count)
  | Filling, { unread = [] } => None
  | Filling, { unread = [_, .._] } => Some Filling

--| Puts a packet in front of the ones read after it.
def andThen (packet: Packet): Option (List Packet, BitReader) → Option (List Packet, BitReader) := match some
  | Some (packets, rest) => ([packet, ..packets], rest)

--| Reads the packets wanted from the bits, and gives back the reader after
--| them; none if the bits don't hold them. Every call reads from fewer bits,
--| checked as it goes.
def readPackets (wanted: Wanted) (reader: BitReader): Option (List Packet, BitReader)
    decreasing reader.length
:=
  match nextWanted wanted reader with
    | None => Some ([], reader)
    | Some later =>
      match reader.readNumber 3 with
        | None => None
        | Some (version, afterVersion) =>
          match afterVersion.readNumber 3 with
            | None => None
            | Some (typeId, afterType) =>
              match operatorTypeOf typeId with
                | None =>
                  match readGroups afterType with
                    | None => None
                    | Some (groups, after) =>
                      if shorter: after.length < reader.length then
                        andThen (Literal version groups) (readPackets later after)
                      else None
                | Some operatorType =>
                  match afterType.readBit with
                    | None => None
                    | Some (False, afterLengthType) =>
                      match afterLengthType.read 15 with
                        | None => None
                        | Some (length, afterLength) =>
                          match afterLength.read length.value with
                            | None => None
                            | Some (inside, following) =>
                              if shorter: (BitReader.of inside).length < reader.length then
                                match readPackets Filling (BitReader.of inside) with
                                  | None => None
                                  | Some (subPackets, _) =>
                                    match operatorOf version operatorType TotalLength subPackets with
                                      | None => None
                                      | Some packet =>
                                        if shorterAfter: following.length < reader.length then
                                          andThen packet (readPackets later following)
                                        else None
                              else None
                    | Some (True, afterLengthType) =>
                      match afterLengthType.read 11 with
                        | None => None
                        | Some (count, after) =>
                          if shorter: after.length < reader.length then
                            match readPackets (Packets count.value) after with
                              | None => None
                              | Some (subPackets, following) =>
                                match operatorOf version operatorType Count subPackets with
                                  | None => None
                                  | Some packet =>
                                    if shorterAfter: following.length < reader.length then
                                      andThen packet (readPackets later following)
                                    else None
                          else None

--| One packet, and the reader after it.
def readPacket (reader: BitReader): Option (Packet, BitReader) :=
  readPackets (Packets 1) reader |> match some | Some ([packet], rest) => (packet, rest)

--| The outermost packet of the transmission. Only zero bits may follow it
--| (the padding).
def parsePacket (input: Text): {Fail} Packet := decodeTransmission (readBits input)

--| The bits are all zero.
def zeroBits (bits: List Bool): Bool := bits.all not

--| An operator with no sub-packets, or a comparison without exactly two,
--| isn't a packet: it fails to decode.
def decodeTransmission (bits: List Bool): {Fail} Packet := match readPacket { unread = bits } with
  | Some ((packet, rest)) =>
    match zeroBits rest.unread with
      | True => packet
      | False => Fail.fail "the bits after the packet aren't all zero padding"
  | None =>
    Fail.fail
        "the transmission isn't a packet (or an operator in it has no sub-packets, or a comparison doesn't have exactly two)"

--| The sum of the versions of a packet and every packet inside it.
def versionSum: Packet → Nat
  | Literal version _ => version
  | Operator version _ _ ({ head = first, tail = rest }) => version + versionSum first + versionSums rest
  | Comparator version _ _ first second => version + versionSum first + versionSum second

def versionSums: List Packet → Nat
  | [] => 0
  | [packet, ..rest] => versionSum packet + versionSums rest

def solvePart1 (packet: Packet): Nat := versionSum packet

--| A packet's value.
def evaluate: Packet → Nat
  | Literal _ groups => groups.foldLeft 0 (value group => value * 16 + group)
  | Operator _ operation _ ({ head = first, tail = rest }) =>
    operation.apply { head = evaluate first, tail = evaluateAll rest }
  | Comparator _ comparison _ first second => comparison.apply (evaluate first) (evaluate second)

def evaluateAll: List Packet → List Nat
  | [] => []
  | [packet, ..rest] => [evaluate packet, ..evaluateAll rest]

--| An operation on its sub-packets' values.
def Operation.apply (operation: Operation) (values: NonEmptyList Nat): Nat := match operation with
  | Sum => values.toList.sum
  | Product => values.toList.product
  | Minimum => values.minimum
  | Maximum => values.maximum

--| 1 if the comparison holds between the first value and the second, else 0.
def Comparison.apply (comparison: Comparison) (first second: Nat): Nat := match comparison with
  | GreaterThan => if first > second then 1 else 0
  | LessThan => if first < second then 1 else 0
  | EqualTo => if first == second then 1 else 0

def solvePart2 (packet: Packet): Nat := evaluate packet
