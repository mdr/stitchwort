--| Completeness: the decoder reads every well-formed packet back from its
--| encoding, whatever follows it.

namespace Aoc.Year2021.Day16.Proofs
import Aoc.Common (BitReader, Bits)
import Aoc.Common.Proofs (..)
import Aoc.Year2021.Day16 (..)
import Aoc.Year2021.Day16.Spec (allWellFormed, encode, encodeAll, groupBits, typeId, wellFormed)
import Std (Bool, Decidable, Eq, List, Nat, Option, Void)

--| One step of the decoder on a literal, its fields read.
theorem literalStep (wanted: Wanted) (later: Wanted) (reader: BitReader) (afterVersion: BitReader) (afterType: BitReader) (after: BitReader) (version: Nat)
    (groups: List Nat) (next: nextWanted wanted reader = Some later) (versionRead: reader.readNumber 3 = Some (version, afterVersion))
    (typeRead: afterVersion.readNumber 3 = Some (4, afterType)) (groupsRead: readGroups afterType = Some (groups, after)) (shorter: after.length < reader.length):
    readPackets wanted reader = andThen (Literal version groups) (readPackets later after) :=
  rewrite readPackets.unfold wanted reader, next, versionRead, typeRead, groupsRead in
    match Nat.decLessThan after.length reader.length with
      | Yes _ => rfl
      | No longer => Void.exfalso (longer shorter)

--| One step on an operator with a total length, its fields read.
theorem totalStep (wanted: Wanted) (later: Wanted) (reader: BitReader) (afterVersion: BitReader) (afterType: BitReader) (afterBit: BitReader)
    (afterLength: BitReader) (inside: Bits) (following: BitReader) (version: Nat) (typeCode: Nat) (operation: Operation) (length: Bits) (total: Nat)
    (subPackets: List Packet) (emptied: BitReader) (next: nextWanted wanted reader = Some later)
    (versionRead: reader.readNumber 3 = Some (version, afterVersion)) (typeRead: afterVersion.readNumber 3 = Some (typeCode, afterType))
    (operationRead: operationOf typeCode = Some operation) (lengthType: afterType.readBit = Some (False, afterBit))
    (lengthRead: afterBit.read 15 = Some (length, afterLength)) (lengthValue: length.value = total)
    (split: afterLength.read total = Some (inside, following)) (shorter: (BitReader.of inside).length < reader.length)
    (insideRead: readPackets Filling (BitReader.of inside) = Some (subPackets, emptied)) (shorterAfter: following.length < reader.length):
    readPackets wanted reader = andThen (Operator version operation TotalLength subPackets) (readPackets later following) :=
  rewrite readPackets.unfold wanted reader, next, versionRead, typeRead, operationRead, lengthType, lengthRead, lengthValue, split in
    match Nat.decLessThan (BitReader.of inside).length reader.length with
      | No longer => Void.exfalso (longer shorter)
      | Yes _ =>
        rewrite insideRead in
          match Nat.decLessThan following.length reader.length with
            | No longer => Void.exfalso (longer shorterAfter)
            | Yes _ => rfl

--| One step on an operator with a number of sub-packets, its fields read.
theorem countStep (wanted: Wanted) (later: Wanted) (reader: BitReader) (afterVersion: BitReader) (afterType: BitReader) (afterBit: BitReader)
    (after: BitReader) (following: BitReader) (version: Nat) (typeCode: Nat) (operation: Operation) (count: Bits) (total: Nat) (subPackets: List Packet)
    (next: nextWanted wanted reader = Some later) (versionRead: reader.readNumber 3 = Some (version, afterVersion))
    (typeRead: afterVersion.readNumber 3 = Some (typeCode, afterType)) (operationRead: operationOf typeCode = Some operation)
    (lengthType: afterType.readBit = Some (True, afterBit)) (countRead: afterBit.read 11 = Some (count, after)) (countValue: count.value = total)
    (shorter: after.length < reader.length) (subPacketsRead: readPackets (Packets total) after = Some (subPackets, following))
    (shorterAfter: following.length < reader.length):
    readPackets wanted reader = andThen (Operator version operation Count subPackets) (readPackets later following) :=
  rewrite readPackets.unfold wanted reader, next, versionRead, typeRead, operationRead, lengthType, countRead, countValue in
    match Nat.decLessThan after.length reader.length with
      | No longer => Void.exfalso (longer shorter)
      | Yes _ =>
        rewrite subPacketsRead in
          match Nat.decLessThan following.length reader.length with
            | No longer => Void.exfalso (longer shorterAfter)
            | Yes _ => rfl

theorem typeIdSmall (operation: Operation): typeId operation < 8 := cases

--| An operation's type id, in its three bits, is read back as it.
theorem operationReadBack (operation: Operation): operationOf (Nat.fromBits (Nat.toBits 3 (typeId operation))) = Some operation := cases

--| A packet's bits aren't empty, so when filling bits, another is wanted.
theorem fillingNext (rest: List Bool): (packet: Packet) → nextWanted Filling ({ unread = encode packet ++ rest }) = Some Filling
  | Literal _ _ => rfl
  | Operator _ _ TotalLength _ => rfl
  | Operator _ _ Count _ => rfl

--| Reading what was wanted after a well-formed packet's bits reads the
--| packet, then goes on.
theorem stepComplete (wanted: Wanted) (later: Wanted) (more: List Bool): (packet: Packet) → wellFormed packet = True →
    nextWanted wanted { unread = encode packet ++ more } = Some later →
    readPackets wanted { unread = encode packet ++ more } = andThen packet (readPackets later { unread = more })
  | Literal version groups, formed, next =>
    let small: version < Nat.pow 2 3 := omega [Bool.andLeft _ _ formed]
    let others := Bool.andRight _ _ formed
    let some: groups ≠ [] := Decidable.toBoolSound _ (Bool.andLeft _ _ others)
    let length := List.lengthAppend (groupBits groups) more
    let afterVersion := Nat.toBits 3 4 ++ (groupBits groups ++ more)
    literalStep wanted later { unread = encode (Literal version groups) ++ more } { unread = afterVersion } { unread = groupBits groups ++ more } { unread = more }
      version groups next (BitReader.readNumberAppend 3 version afterVersion small) (BitReader.readNumberAppend 3 4 (groupBits groups ++ more) (omega))
      (readGroupsBits more groups some (Bool.andRight _ _ others)) (omega [length])
  | Operator version operation TotalLength subPackets, formed, next =>
    let small: version < Nat.pow 2 3 := omega [Bool.andLeft _ _ formed]
    let others := Bool.andRight _ _ formed
    let total := (encodeAll subPackets).length
    let fits: total < Nat.pow 2 15 := omega [Bool.andLeft _ _ others]
    let length := List.lengthAppend (encodeAll subPackets) more
    let id := typeId operation
    let sub := encodeAll subPackets ++ more
    let afterVersion := Nat.toBits 3 id ++ [False, ..Nat.toBits 15 total ++ sub]
    totalStep wanted later { unread = encode (Operator version operation TotalLength subPackets) ++ more } { unread = afterVersion }
      { unread = [False, ..Nat.toBits 15 total ++ sub] } { unread = Nat.toBits 15 total ++ sub } { unread = sub } { bits = encodeAll subPackets } { unread = more }
      version id operation { bits = Nat.toBits 15 total } total subPackets { unread = [] } next
      (BitReader.readNumberAppend 3 version afterVersion small) (BitReader.readNumberAppend 3 id ([False, ..Nat.toBits 15 total ++ sub]) (omega [typeIdSmall operation]))
      (operationOfTypeId operation) rfl (BitReader.readAppend (Nat.toBits 15 total) sub 15 (Nat.toBitsLength 15 total)) (Nat.fromBitsToBits 15 total fits)
      (BitReader.readAppend (encodeAll subPackets) more total rfl) (omega [length]) (fillComplete subPackets (Bool.andRight _ _ others)) (omega [length])
  | Operator version operation Count subPackets, formed, next =>
    let small: version < Nat.pow 2 3 := omega [Bool.andLeft _ _ formed]
    let others := Bool.andRight _ _ formed
    let count := subPackets.length
    let fits: count < Nat.pow 2 11 := omega [Bool.andLeft _ _ others]
    let length := List.lengthAppend (encodeAll subPackets) more
    let id := typeId operation
    let sub := encodeAll subPackets ++ more
    let afterVersion := Nat.toBits 3 id ++ [True, ..Nat.toBits 11 count ++ sub]
    countStep wanted later { unread = encode (Operator version operation Count subPackets) ++ more } { unread = afterVersion }
      { unread = [True, ..Nat.toBits 11 count ++ sub] } { unread = Nat.toBits 11 count ++ sub } { unread = sub } { unread = more }
      version id operation { bits = Nat.toBits 11 count } count subPackets next
      (BitReader.readNumberAppend 3 version afterVersion small) (BitReader.readNumberAppend 3 id ([True, ..Nat.toBits 11 count ++ sub]) (omega [typeIdSmall operation]))
      (operationOfTypeId operation) rfl (BitReader.readAppend (Nat.toBits 11 count) sub 11 (Nat.toBitsLength 11 count)) (Nat.fromBitsToBits 11 count fits)
      (omega [length]) (countComplete subPackets (Bool.andRight _ _ others) more) (omega [length])

--| Reading as many packets as there are reads them all back.
theorem countComplete: (packets: List Packet) → allWellFormed packets = True → (more: List Bool) →
    readPackets (Packets packets.length) { unread = encodeAll packets ++ more } = Some (packets, { unread = more })
  | [], formed, more => rewrite readPackets.unfold (Packets 0) { unread = more } in rfl
  | [packet, ..rest], formed, more =>
    let step := stepComplete (Packets (Succ rest.length)) (Packets rest.length) (encodeAll rest ++ more) packet (Bool.andLeft _ _ formed) rfl
    rewrite List.appendAssoc (encode packet) (encodeAll rest) more, step, countComplete rest (Bool.andRight _ _ formed) more in rfl

--| Filling packets' bits reads them all back.
theorem fillComplete: (packets: List Packet) → allWellFormed packets = True → readPackets Filling ({ unread = encodeAll packets }) = Some (packets, { unread = [] })
  | [], formed => rewrite readPackets.unfold Filling ({ unread = [] }) in rfl
  | [packet, ..rest], formed =>
    let step := stepComplete Filling Filling (encodeAll rest) packet (Bool.andLeft _ _ formed) (fillingNext (encodeAll rest) packet)
    rewrite step, fillComplete rest (Bool.andRight _ _ formed) in rfl
