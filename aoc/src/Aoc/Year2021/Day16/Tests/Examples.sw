--| Day 16's tests: the puzzle's examples, through the program and the
--| spec, and the parser.
-- Kept apart from the program, so `stitchwort run Aoc.Year2021.Day16.main`
-- doesn't check them.

namespace Aoc.Year2021.Day16.Tests
import Aoc.Year2021.Day16 (..)
import Aoc.Year2021.Day16.Spec (encode, hexDigitBits, versionTotal, wellFormed)
import Std (Fail, List, Option, Result, Text)

def parsed (input: Text): Result Packet Text := Fail.toResult (() => parsePacket input)

--| The error a transmission fails to parse with, if it does.
def errorOf (input: Text): Option Text := match parsed input with
  | Err message => Some message
  | Ok _ => None

--| The error for bits that aren't a packet, as the puzzle's operators are:
--| an operator needs one or more sub-packets, a comparison exactly two.
def notAPacket: Text :=
  "the transmission isn't a packet (or an operator in it has no sub-packets, or a comparison doesn't have exactly two)"

def packetOf (input: Text): Packet := Fail.orElse (Literal 0 [0]) (() => parsePacket input)

def bitsOf (input: Text): List Bool := Fail.orElse [] (() => readBits input)

--| Both parts, and the spec's part 1.
def part1 (input: Text): Nat := solvePart1 (packetOf input)

def part2 (input: Text): Nat := solvePart2 (packetOf input)

def specPart1 (input: Text): Nat := versionTotal (packetOf input)

--| Bits written as the puzzle writes them.
def bitText (bits: List Bool): Text := Text.fromList (bits.map (bit => if bit then '1' else '0'))

theorem literalBits: bitText (bitsOf "D2FE28") = "110100101111111000101000" := rfl

--| The literal 2021, version 6, in three groups.
theorem literalPacket: parsed "D2FE28" = Ok (Literal 6 [7, 14, 5]) := rfl

test "literal value" := part2 "D2FE28" == 2021

--| An operator (version 1, type 6) with the total length of two literals,
--| 10 and 20.
theorem lengthOperator: parsed "38006F45291200"
      = Ok (Comparator 1 LessThan TotalLength (Literal 6 [10]) (Literal 2 [1, 4])) :=
  rfl

--| An operator (version 7, type 3) with three literals, 1, 2 and 3, by
--| number.
theorem countOperator: parsed "EE00D40C823060"
      = Ok (Operator 7 Maximum Count [Literal 2 [1], Literal 4 [2], Literal 1 [3]]) :=
  rfl

test "part 1, examples" :=
  part1 "8A004A801A8002F478" == 16
    && part1 "620080001611562C8802118E34" == 12
    && part1 "C0015000016115A2E0802F182340" == 23
    && part1 "A0016C880162017C3686B18A3D4780" == 31

test "part 1 by the spec, examples" :=
  specPart1 "8A004A801A8002F478" == 16
    && specPart1 "620080001611562C8802118E34" == 12
    && specPart1 "C0015000016115A2E0802F182340" == 23
    && specPart1 "A0016C880162017C3686B18A3D4780" == 31

test "part 2, examples" :=
  part2 "C200B40A82" == 3
    && part2 "04005AC33890" == 54
    && part2 "880086C3E88112" == 7
    && part2 "CE00C43D881120" == 9
    && part2 "D8005AC2A8F0" == 1
    && part2 "F600BC2D8F" == 0
    && part2 "9C005AC2F8F0" == 0
    && part2 "9C0141080250320F1802104A08" == 1

--| The spec's encoding of what was read is the bits read, up to the
--| padding.
test "encodings, examples" :=
  let check := (input: Text) =>
    let packet := packetOf input
    let bits := bitsOf input
    let written := encode packet
    wellFormed packet && bits.take written.length == written && bits.drop written.length |> .all (bit => not bit)
  check "D2FE28"
    && check "38006F45291200"
    && check "EE00D40C823060"
    && check "8A004A801A8002F478"
    && check "620080001611562C8802118E34"
    && check "C0015000016115A2E0802F182340"
    && check "A0016C880162017C3686B18A3D4780"
    && check "9C0141080250320F1802104A08"

--| The program's digits are the puzzle's.
test "hexadecimal digits" := "0123456789ABCDEF".toList.all (char => (hexValue char).map digitBits == hexDigitBits char)

--| The parser's errors.
test "not hexadecimal" :=
  errorOf "D2FG28\n" == Some "column 4: expected a hexadecimal digit or the end of the line, got 'G'"

--| Only zero bits may follow the packet: the literal 2021 ends after 21
--| bits, so `D2FE28` has 3 padding bits and `D2FE2800` 11, while the last
--| bit of `D2FE29` is a 1.
theorem zeroPadding: parsed "D2FE2800" = Ok (Literal 6 [7, 14, 5]) := rfl

test "a bad trailer" := errorOf "D2FE29" == Some "the bits after the packet aren't all zero padding"

test "too short" := errorOf "D2FE" == Some notAPacket

--| Sub-packets exactly filling a total length of 22 bits, and the same
--| with a length of 100 that the transmission ends before.
theorem aTotalLength: parsed "38005B4528B" = Ok (Comparator 1 LessThan TotalLength (Literal 6 [10]) (Literal 2 [11])) :=
  rfl

test "a total length past the end" := errorOf "3801934528B" == Some notAPacket

--| An operator needs sub-packets, and a comparison exactly two: a sum of
--| none (by total length 0, and by count 0) and a comparison of three
--| aren't packets.
test "a sum of none, by total length" := errorOf "000000" == Some notAPacket

test "a sum of none, by count" := errorOf "020000" == Some notAPacket

test "a comparison of three" := errorOf "3A00C40881102" == Some notAPacket

--| The hypothesis of the parser's theorems can hold.
-- (the audit's random texts never parse)
theorem smallParses: parsed "D2FE28\n" = Ok (Literal 6 [7, 14, 5]) := rfl
