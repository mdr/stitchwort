--| The decoder is the encoding's inverse, for one packet: what it reads is
--| a well-formed packet whose bits start the input, and it reads every
--| well-formed packet back from its bits, whatever follows. So bits hold at
--| most one packet, and the parser's packet is the transmission's.

namespace Aoc.Year2021.Day16.Proofs
import Aoc.Year2021.Day16 (..)
import Aoc.Year2021.Day16.Spec (allWellFormed, encode, encodeAll, promised, transmissionBits, wellFormed)
import Std (Bool, Eq, Exists, Fail, List, Option, Result, Text, Void)

--| Soundness: a packet read is well formed, and its bits start the input.
theorem readPacketSound (bits: List Bool) (packet: Packet) (rest: List Bool) (read: readPacket bits = Some (packet, rest)):
    bits = encode packet ++ rest ∧ wellFormed packet = True :=
  match e: readPackets (Packets 1) bits with
    | None => cases
    | Some ([], _) => cases
    | Some ([_, _, .._], _) => cases
    | Some ([first], after) =>
      let parts := somePairInjective _ _ _ _ read
      let sound := readPacketsSound (Packets 1) bits [first] after e
      rewrite <- parts.left, <- parts.right in
        Both (rewrite List.appendNil (encode first) at (sound.left)) (Bool.andLeft _ _ sound.right.left)

--| Completeness: a well-formed packet is read back from its bits, whatever
--| follows them.
theorem readPacketComplete (packet: Packet) (formed: wellFormed packet = True) (rest: List Bool): readPacket (encode packet ++ rest) = Some (packet, rest) :=
  let read := countComplete [packet] (Bool.andIntro _ _ formed rfl) rest
  rewrite List.appendNil (encode packet) at read in rewrite read in rfl

--| So bits start with at most one well-formed packet: the transmission
--| fixes the packet.
theorem encodingUnique (first: Packet) (second: Packet) (rest1: List Bool) (rest2: List Bool) (formed1: wellFormed first = True)
    (formed2: wellFormed second = True) (same: encode first ++ rest1 = encode second ++ rest2): first = second ∧ rest1 = rest2 :=
  let read1 := readPacketComplete first formed1 rest1
  let read2 := readPacketComplete second formed2 rest2
  rewrite same at read1 in somePairInjective _ _ _ _ (Eq.trans (Eq.sym read1) read2)

--| The parser's guarantee: the input is hexadecimal digits, and the packet
--| it reads is well formed, its encoding starts the transmission's bits and
--| only zero bits (the padding) follow it, and it keeps the puzzle's promise
--| about the operators.
theorem parsePacketReads (input: Text) (packet: Packet) (parsed: Fail.toResult (() => parsePacket input) = Ok packet):
    ∃ (bits: List Bool) => ∃ (rest: List Bool) =>
      transmissionBits input.trim.toList = Some bits ∧ bits = encode packet ++ rest ∧ rest.all (bit => not bit) = True ∧ wellFormed packet = True ∧ promised packet = True :=
  let split := rewrite Fail.toResultThen (() => readBits input) decodeTransmission at parsed in parsed
  Result.flatMapEqOk (Fail.toResult (() => readBits input)) (bits => Fail.toResult (() => decodeTransmission bits)) packet split
    (bits got decoded =>
      match e: readPacket bits with
        | None => cases
        | Some (found, rest) =>
          match z: zeroBits rest with
            | False => cases
            | True =>
              match b: badOperator found with
                | Some (operation, count) => cases
                | None =>
                  let sound := readPacketSound bits found rest e
                  rewrite <- Result.okInjective found packet decoded in
                    Witness bits (Witness rest (Both (readBitsHex input bits got) (Both sound.left (Both z (Both sound.right (badOperatorNone found b)))))))
