--| Completeness: the decoder reads every well-formed packet back from its
--| encoding, whatever follows it.

namespace Aoc.Year2021.Day16.Proofs
import Aoc.Common (BitReader, Bits)
import Aoc.Common.Proofs (..)
import Aoc.Year2021.Day16 (..)
import Aoc.Year2021.Day16.Spec (allWellFormed, encode, encodeAll, fitsLength, groupBits, lengthField, operatorBits, typeId, wellFormed)
import Std (Bool, Decidable, Eq, List, Nat, NonEmptyList, Option, Void)

--| One step of the decoder on a literal, its fields read.
theorem literalStep (wanted: Wanted) (later: Wanted) (reader: BitReader) (afterVersion: BitReader) (afterType: BitReader) (after: BitReader) (version: Nat)
    (groups: NonEmptyList Nat) (next: nextWanted wanted reader = Some later) (versionRead: reader.readNumber 3 = Some (version, afterVersion))
    (typeRead: afterVersion.readNumber 3 = Some (4, afterType)) (groupsRead: readGroups afterType = Some (groups, after)) (shorter: after.length < reader.length):
    readPackets wanted reader = andThen (Literal version groups) (readPackets later after) :=
  rewrite readPackets.unfold wanted reader, next, versionRead, typeRead, groupsRead in
    match h: (after.length < reader.length: Bool) with
      | True => rfl

--| One step on an operator with a total length, its fields read.
theorem totalStep (wanted: Wanted) (later: Wanted) (reader: BitReader) (afterVersion: BitReader) (afterType: BitReader) (afterBit: BitReader)
    (afterLength: BitReader) (inside: Bits) (following: BitReader) (version: Nat) (typeCode: Nat) (operatorType: OperatorType) (length: Bits) (total: Nat)
    (subPackets: List Packet) (packet: Packet) (emptied: BitReader) (next: nextWanted wanted reader = Some later)
    (versionRead: reader.readNumber 3 = Some (version, afterVersion)) (typeRead: afterVersion.readNumber 3 = Some (typeCode, afterType))
    (operatorRead: operatorTypeOf typeCode = Some operatorType) (lengthType: afterType.readBit = Some (False, afterBit))
    (lengthRead: afterBit.read 15 = Some (length, afterLength)) (lengthValue: length.value = total)
    (split: afterLength.read total = Some (inside, following)) (shorter: (BitReader.of inside).length < reader.length)
    (insideRead: readPackets Filling (BitReader.of inside) = Some (subPackets, emptied))
    (made: operatorOf version operatorType TotalLength subPackets = Some packet) (shorterAfter: following.length < reader.length):
    readPackets wanted reader = andThen packet (readPackets later following) :=
  rewrite readPackets.unfold wanted reader, next, versionRead, typeRead, operatorRead, lengthType, lengthRead, lengthValue, split in
    match h: ((BitReader.of inside).length < reader.length: Bool) with
      | True =>
        rewrite insideRead, made in
          match h: (following.length < reader.length: Bool) with
            | True => rfl

--| One step on an operator with a number of sub-packets, its fields read.
theorem countStep (wanted: Wanted) (later: Wanted) (reader: BitReader) (afterVersion: BitReader) (afterType: BitReader) (afterBit: BitReader)
    (after: BitReader) (following: BitReader) (version: Nat) (typeCode: Nat) (operatorType: OperatorType) (count: Bits) (total: Nat) (subPackets: List Packet) (packet: Packet)
    (next: nextWanted wanted reader = Some later) (versionRead: reader.readNumber 3 = Some (version, afterVersion))
    (typeRead: afterVersion.readNumber 3 = Some (typeCode, afterType)) (operatorRead: operatorTypeOf typeCode = Some operatorType)
    (lengthType: afterType.readBit = Some (True, afterBit)) (countRead: afterBit.read 11 = Some (count, after)) (countValue: count.value = total)
    (shorter: after.length < reader.length) (subPacketsRead: readPackets (Packets total) after = Some (subPackets, following))
    (made: operatorOf version operatorType Count subPackets = Some packet) (shorterAfter: following.length < reader.length):
    readPackets wanted reader = andThen packet (readPackets later following) :=
  rewrite readPackets.unfold wanted reader, next, versionRead, typeRead, operatorRead, lengthType, countRead, countValue in
    match h: (after.length < reader.length: Bool) with
      | True =>
        rewrite subPacketsRead, made in
          match h: (following.length < reader.length: Bool) with
            | True => rfl

theorem typeIdSmall (operatorType: OperatorType): typeId operatorType < 8 := cases

--| A packet's bits aren't empty, so when filling bits, another is wanted.
theorem fillingNext (rest: List Bool) (packet: Packet): nextWanted Filling { unread = encode packet ++ rest } = Some Filling :=
  match packet with
    | Literal _ _ => rfl
    | Operator _ _ _ ({ head = _, tail = _ }) => rfl
    | Comparator _ _ _ _ _ => rfl

--| The decoder reads an operator back from its bits, given the sub-packets
--| they hold (as a list, with their number and bits however they are
--| written), whatever follows.
theorem operatorStepComplete (wanted: Wanted) (later: Wanted) (more: List Bool) (version: Nat) (operatorType: OperatorType) (lengthType: LengthType)
    (subPackets: List Packet) (packet: Packet)
    (made: operatorOf version operatorType lengthType subPackets = Some packet) (small: version < 8)
    (fits: fitsLength lengthType subPackets.length (encodeAll subPackets) = True)
    (filled: readPackets Filling { unread = encodeAll subPackets } = Some (subPackets, { unread = [] }))
    (counted: readPackets (Packets subPackets.length) { unread = encodeAll subPackets ++ more } = Some (subPackets, { unread = more }))
    (next: nextWanted wanted { unread = operatorBits version (typeId operatorType) lengthType subPackets.length (encodeAll subPackets) ++ more } = Some later):
    readPackets wanted { unread = operatorBits version (typeId operatorType) lengthType subPackets.length (encodeAll subPackets) ++ more } =
      andThen packet (readPackets later { unread = more }) :=
  match lengthType with
    | TotalLength =>
      let smallVersion: version < Nat.pow 2 3 := omega [small]
      let total := (encodeAll subPackets).length
      let fitsTotal: total < Nat.pow 2 15 := omega [fits]
      let length := List.lengthAppend (encodeAll subPackets) more
      let id := typeId operatorType
      let sub := encodeAll subPackets ++ more
      let afterVersion := Nat.toBits 3 id ++ [False, ..Nat.toBits 15 total ++ sub]
      totalStep wanted later { unread = operatorBits version id TotalLength subPackets.length (encodeAll subPackets) ++ more } { unread = afterVersion }
        { unread = [False, ..Nat.toBits 15 total ++ sub] } { unread = Nat.toBits 15 total ++ sub } { unread = sub } { bits = encodeAll subPackets } { unread = more }
        version id operatorType { bits = Nat.toBits 15 total } total subPackets packet { unread = [] } next
        (BitReader.readNumberAppend 3 version afterVersion smallVersion) (BitReader.readNumberAppend 3 id ([False, ..Nat.toBits 15 total ++ sub]) (omega [typeIdSmall operatorType]))
        (operatorTypeOfTypeId operatorType) rfl (BitReader.readAppend (Nat.toBits 15 total) sub 15 (Nat.toBitsLength 15 total)) (Nat.fromBitsToBits 15 total fitsTotal)
        (BitReader.readAppend (encodeAll subPackets) more total rfl) (omega [length]) filled made (omega [length])
    | Count =>
      let smallVersion: version < Nat.pow 2 3 := omega [small]
      let number := subPackets.length
      let fitsCount: number < Nat.pow 2 11 := omega [fits]
      let length := List.lengthAppend (encodeAll subPackets) more
      let id := typeId operatorType
      let sub := encodeAll subPackets ++ more
      let afterVersion := Nat.toBits 3 id ++ [True, ..Nat.toBits 11 number ++ sub]
      countStep wanted later { unread = operatorBits version id Count subPackets.length (encodeAll subPackets) ++ more } { unread = afterVersion }
        { unread = [True, ..Nat.toBits 11 number ++ sub] } { unread = Nat.toBits 11 number ++ sub } { unread = sub } { unread = more }
        version id operatorType { bits = Nat.toBits 11 number } number subPackets packet next
        (BitReader.readNumberAppend 3 version afterVersion smallVersion) (BitReader.readNumberAppend 3 id ([True, ..Nat.toBits 11 number ++ sub]) (omega [typeIdSmall operatorType]))
        (operatorTypeOfTypeId operatorType) rfl (BitReader.readAppend (Nat.toBits 11 number) sub 11 (Nat.toBitsLength 11 number)) (Nat.fromBitsToBits 11 number fitsCount)
        (omega [length]) counted made (omega [length])

--| Reading what was wanted after a well-formed packet's bits reads the
--| packet, then goes on.
theorem stepComplete (wanted: Wanted) (later: Wanted) (more: List Bool) (packet: Packet) (formed: wellFormed packet = True)
    (next: nextWanted wanted { unread = encode packet ++ more } = Some later):
    readPackets wanted { unread = encode packet ++ more } = andThen packet (readPackets later { unread = more }) :=
  match packet with
    | Literal version groups =>
      let Both smallVersion others := formed
      let small: version < Nat.pow 2 3 := omega [smallVersion]
      let length := List.lengthAppend (groupBits groups) more
      let afterVersion := Nat.toBits 3 4 ++ (groupBits groups ++ more)
      literalStep wanted later { unread = encode (Literal version groups) ++ more } { unread = afterVersion } { unread = groupBits groups ++ more } { unread = more }
        version groups next (BitReader.readNumberAppend 3 version afterVersion small) (BitReader.readNumberAppend 3 4 (groupBits groups ++ more) (omega))
        (readGroupsBits more groups others) (omega [length])
    | Operator version operation lengthType ({ head = first, tail = rest }) =>
      let Both smallVersion (Both fits others) := formed
      operatorStepComplete wanted later more version (Calculation operation) lengthType [first, ..rest] (Operator version operation lengthType (NonEmptyList.cons first rest))
        rfl (omega [smallVersion]) fits
        (fillCons first rest others) (countCons first rest others more) next
    | Comparator version comparison lengthType first second =>
      let Both smallVersion (Both fits (Both firstOk secondOk)) := formed
      let sameBits: encode first ++ encode second = encodeAll [first, second] := Eq.sym (Eq.cong (bits => encode first ++ bits) (List.appendNil (encode second)))
      let sameReader: operatorBits version (typeId (Comparing comparison)) lengthType 2 (encode first ++ encode second) ++ more =
          operatorBits version (typeId (Comparing comparison)) lengthType 2 (encodeAll [first, second]) ++ more :=
        Eq.cong (bits => operatorBits version (typeId (Comparing comparison)) lengthType 2 bits ++ more) sameBits
      let read := operatorStepComplete wanted later more version (Comparing comparison) lengthType [first, second] (Comparator version comparison lengthType first second)
        rfl (omega [smallVersion]) (rewrite List.appendNil (encode second) in fits)
        (fillPair first second firstOk secondOk)
        (countPair first second firstOk secondOk more)
        (Eq.trans (Eq.cong (bits => nextWanted wanted { unread = bits }) (Eq.sym sameReader)) next)
      Eq.trans (Eq.cong (bits => readPackets wanted { unread = bits }) sameReader) read

--| Reading as many packets as there are reads them all back.
theorem countComplete: ∀ (packets: List Packet) => allWellFormed packets = True → ∀ (more: List Bool) =>
    readPackets (Packets packets.length) { unread = encodeAll packets ++ more } = Some (packets, { unread = more })
  | [], formed, more => rewrite readPackets.unfold (Packets 0) { unread = more } in rfl
  | [packet, ..rest], formed, more => countCons packet rest formed more

--| The same for a first packet and the rest.
theorem countCons (packet: Packet) (rest: List Packet) (formed: allWellFormed [packet, ..rest] = True) (more: List Bool):
    readPackets (Packets (Succ rest.length)) { unread = encodeAll [packet, ..rest] ++ more } = Some ([packet, ..rest], { unread = more }) :=
  let Both packetOk restOk := formed
  let step := stepComplete (Packets (Succ rest.length)) (Packets rest.length) (encodeAll rest ++ more) packet packetOk rfl
  rewrite List.appendAssoc (encode packet) (encodeAll rest) more, step, countComplete rest restOk more in rfl

--| Reading two packets by number. (Spelled out, not through `countCons`:
--| the termination check needs each packet to come from the one being read.)
theorem countPair (first: Packet) (second: Packet) (formedFirst: wellFormed first = True) (formedSecond: wellFormed second = True) (more: List Bool):
    readPackets (Packets 2) { unread = encodeAll [first, second] ++ more } = Some ([first, second], { unread = more }) :=
  let step1 := stepComplete (Packets 2) (Packets 1) (encodeAll [second] ++ more) first formedFirst rfl
  let step2 := stepComplete (Packets 1) (Packets 0) more second formedSecond rfl
  rewrite List.appendAssoc (encode first) (encodeAll [second]) more, step1, List.appendAssoc (encode second) [] more, step2 in rfl

--| Filling packets' bits reads them all back.
theorem fillComplete (packets: List Packet) (formed: allWellFormed packets = True): readPackets Filling { unread = encodeAll packets } = Some (packets, { unread = [] }) :=
  match packets with
    | [] => rewrite readPackets.unfold Filling { unread = [] } in rfl
    | [packet, ..rest] => fillCons packet rest formed

--| The same for a first packet and the rest.
theorem fillCons (packet: Packet) (rest: List Packet) (formed: allWellFormed [packet, ..rest] = True):
    readPackets Filling { unread = encodeAll [packet, ..rest] } = Some ([packet, ..rest], { unread = [] }) :=
  let Both packetOk restOk := formed
  let step := stepComplete Filling Filling (encodeAll rest) packet packetOk (fillingNext (encodeAll rest) packet)
  rewrite step, fillComplete rest restOk in rfl

--| The same for two packets, spelled out for the same reason.
theorem fillPair (first: Packet) (second: Packet) (formedFirst: wellFormed first = True) (formedSecond: wellFormed second = True):
    readPackets Filling { unread = encodeAll [first, second] } = Some ([first, second], { unread = [] }) :=
  let step1 := stepComplete Filling Filling (encodeAll [second]) first formedFirst (fillingNext (encodeAll [second]) first)
  let step2 := stepComplete Filling Filling [] second formedSecond (fillingNext [] second)
  rewrite step1, step2 in rfl
