--| The decoder is the encoding's inverse, for one packet: what it reads is
--| a well-formed packet whose bits start the input, and it reads every
--| well-formed packet back from its bits, whatever follows. So bits hold at
--| most one packet, and the parser's packet is the transmission's.

namespace Aoc.Year2021.Day16.Proofs
import Aoc.Year2021.Day16 (..)
import Aoc.Year2021.Day16.Spec (encode, transmissionBits, wellFormed)
import Aoc.Common (BitReader)
import Aoc.Common.Proofs (..)
import Std (Bool, Eq, Exists, Fail, List, Option, Result, Text, Void)

--| Soundness: a packet read is well formed, and its bits start the input.
theorem readPacketSound (reader: BitReader) (packet: Packet) (rest: BitReader) (read: readPacket reader = Some (packet, rest)):
    reader.unread = encode packet ++ rest.unread ∧ wellFormed packet = True :=
  match e: readPackets (Packets 1) reader with
    | Some ([first], after) =>
      let parts := somePairInjective read
      let sound := readPacketsSound (Packets 1) reader [first] after e
      rewrite <- parts.left, <- parts.right in
        Both (rewrite List.appendNil (encode first) at (sound.left)) (Bool.andLeft sound.right.left)

--| Completeness: a well-formed packet is read back from its bits, whatever
--| follows them.
theorem readPacketComplete (packet: Packet) (formed: wellFormed packet = True) (rest: List Bool):
    readPacket { unread = encode packet ++ rest } = Some (packet, { unread = rest }) :=
  let read := countComplete [packet] (Bool.andIntro formed rfl) rest
  rewrite List.appendNil (encode packet) at read in rewrite read in rfl

--| So bits start with at most one well-formed packet: the transmission
--| fixes the packet.
theorem encodingUnique (first: Packet) (second: Packet) (rest1: List Bool) (rest2: List Bool) (formed1: wellFormed first = True)
    (formed2: wellFormed second = True) (same: encode first ++ rest1 = encode second ++ rest2): first = second ∧ rest1 = rest2 :=
  let read1 := readPacketComplete first formed1 rest1
  let read2 := readPacketComplete second formed2 rest2
  let both := rewrite same at read1 in somePairInjective (Eq.trans (Eq.sym read1) read2)
  Both both.left (Eq.cong (reader => reader.unread) both.right)

--| The parser's guarantee: the input is hexadecimal digits, and the packet
--| it reads is well formed, and its encoding starts the transmission's bits
--| with only zero bits (the padding) after it.
theorem parsePacketReads (input: Text) (packet: Packet) (parsed: Fail.toResult (() => parsePacket input) = Ok packet):
    ∃ (bits: List Bool) => ∃ (rest: List Bool) =>
      transmissionBits input.trim.toList = Some bits ∧ bits = encode packet ++ rest ∧ rest.all (bit => not bit) = True ∧ wellFormed packet = True :=
  let split := rewrite Fail.toResultThen (() => readBits input) decodeTransmission at parsed in parsed
  Result.flatMapEqOk (Fail.toResult (() => readBits input)) (bits => Fail.toResult (() => decodeTransmission bits)) packet split
    (bits got decoded =>
      match e: readPacket { unread = bits } with
        | Some (found, rest) =>
          match z: zeroBits rest.unread with
            | True =>
              let sound := readPacketSound { unread = bits } found rest e
              rewrite <- Result.okInjective decoded in
                Witness bits (Witness rest.unread (Both (readBitsHex input bits got) (Both sound.left (Both z sound.right)))))
