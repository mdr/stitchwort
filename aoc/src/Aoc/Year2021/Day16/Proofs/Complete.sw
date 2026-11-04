--| Completeness: the decoder reads every well-formed packet back from its
--| encoding, whatever follows it.

namespace Aoc.Year2021.Day16.Proofs
import Aoc.Year2021.Day16 (..)
import Aoc.Year2021.Day16.Spec (allWellFormed, bitsOf, encode, encodeAll, groupBits, typeId, wellFormed)
import Std (Bool, Decidable, Eq, List, Nat, Option, Void)

--| One step of the decoder on a literal's header, its groups read.
theorem literalStep (wanted: Wanted) (later: Wanted) (a: Bool) (b: Bool) (c: Bool) (rest6: List Bool) (version: Nat) (groups: List Nat) (more: List Bool)
    (next: nextWanted wanted [a, b, c, True, False, False, ..rest6] = Some later) (versionRead: Nat.fromBits [a, b, c] = version)
    (groupsRead: readGroups rest6 = Some (groups, more)) (shorter: more.length < [a, b, c, True, False, False, ..rest6].length):
    readPackets wanted [a, b, c, True, False, False, ..rest6] = andThen (Literal version groups) (readPackets later more) :=
  rewrite readPackets.unfold wanted [a, b, c, True, False, False, ..rest6], next, groupsRead in
    match Nat.decLessThan more.length [a, b, c, True, False, False, ..rest6].length with
      | Yes _ => rewrite versionRead in rfl
      | No longer => Void.exfalso (longer shorter)

--| One step on an operator's header with a total length, its pieces read.
theorem totalStep (wanted: Wanted) (later: Wanted) (a: Bool) (b: Bool) (c: Bool) (d: Bool) (e: Bool) (f: Bool) (fields: List Bool) (version: Nat)
    (operation: Operation) (length: Nat) (after: List Bool) (inside: List Bool) (following: List Bool) (subPackets: List Packet)
    (next: nextWanted wanted [a, b, c, d, e, f, False, ..fields] = Some later) (versionRead: Nat.fromBits [a, b, c] = version)
    (operationRead: operationOf (Nat.fromBits [d, e, f]) = Some operation) (lengthRead: readNumber 15 fields = Some (length, after))
    (split: splitField length after = Some (inside, following)) (shorter: inside.length < [a, b, c, d, e, f, False, ..fields].length)
    (insideRead: readPackets Filling inside = Some (subPackets, [])) (shorterAfter: following.length < [a, b, c, d, e, f, False, ..fields].length):
    readPackets wanted [a, b, c, d, e, f, False, ..fields] = andThen (Operator version operation TotalLength subPackets) (readPackets later following) :=
  rewrite readPackets.unfold wanted [a, b, c, d, e, f, False, ..fields], next, operationRead, lengthRead, split in
    match Nat.decLessThan inside.length [a, b, c, d, e, f, False, ..fields].length with
      | No longer => Void.exfalso (longer shorter)
      | Yes _ =>
        rewrite insideRead in
          match Nat.decLessThan following.length [a, b, c, d, e, f, False, ..fields].length with
            | No longer => Void.exfalso (longer shorterAfter)
            | Yes _ => rewrite versionRead in rfl

--| One step on an operator's header with a number of sub-packets, its
--| pieces read.
theorem countStep (wanted: Wanted) (later: Wanted) (a: Bool) (b: Bool) (c: Bool) (d: Bool) (e: Bool) (f: Bool) (fields: List Bool) (version: Nat)
    (operation: Operation) (count: Nat) (after: List Bool) (following: List Bool) (subPackets: List Packet)
    (next: nextWanted wanted [a, b, c, d, e, f, True, ..fields] = Some later) (versionRead: Nat.fromBits [a, b, c] = version)
    (operationRead: operationOf (Nat.fromBits [d, e, f]) = Some operation) (countRead: readNumber 11 fields = Some (count, after))
    (shorter: after.length < [a, b, c, d, e, f, True, ..fields].length)
    (subPacketsRead: readPackets (Packets count) after = Some (subPackets, following)) (shorterAfter: following.length < [a, b, c, d, e, f, True, ..fields].length):
    readPackets wanted [a, b, c, d, e, f, True, ..fields] = andThen (Operator version operation Count subPackets) (readPackets later following) :=
  rewrite readPackets.unfold wanted [a, b, c, d, e, f, True, ..fields], next, operationRead, countRead in
    match Nat.decLessThan after.length [a, b, c, d, e, f, True, ..fields].length with
      | No longer => Void.exfalso (longer shorter)
      | Yes _ =>
        rewrite subPacketsRead in
          match Nat.decLessThan following.length [a, b, c, d, e, f, True, ..fields].length with
            | No longer => Void.exfalso (longer shorterAfter)
            | Yes _ => rewrite versionRead in rfl

theorem typeIdSmall (operation: Operation): typeId operation < 8 := cases

--| An operation's type id, in its three bits, is read back as it.
theorem operationReadBack (operation: Operation): operationOf (Nat.fromBits (bitsOf 3 (typeId operation))) = Some operation := cases

--| A packet's bits aren't empty, so when filling bits, another is wanted.
theorem fillingNext (rest: List Bool): (packet: Packet) → nextWanted Filling (encode packet ++ rest) = Some Filling
  | Literal _ _ => rfl
  | Operator _ _ TotalLength _ => rfl
  | Operator _ _ Count _ => rfl

--| Reading what was wanted after a well-formed packet's bits reads the
--| packet, then goes on.
theorem stepComplete (wanted: Wanted) (later: Wanted) (more: List Bool): (packet: Packet) → wellFormed packet = True → nextWanted wanted (encode packet ++ more) = Some later →
    readPackets wanted (encode packet ++ more) = andThen packet (readPackets later more)
  | Literal version groups, formed, next =>
    let small: version < Nat.pow 2 3 := omega [Bool.andLeft _ _ formed]
    let others := Bool.andRight _ _ formed
    let some: groups ≠ [] := Decidable.toBoolSound _ (Bool.andLeft _ _ others)
    let length := List.lengthAppend (groupBits groups) more
    literalStep wanted later (version / 2 / 2 % 2 == 1) (version / 2 % 2 == 1) (version % 2 == 1) (groupBits groups ++ more) version groups more next
      (fromBitsOf 3 version small) (readGroupsBits more groups some (Bool.andRight _ _ others)) (omega [length])
  | Operator version operation TotalLength subPackets, formed, next =>
    let small: version < Nat.pow 2 3 := omega [Bool.andLeft _ _ formed]
    let others := Bool.andRight _ _ formed
    let total := (encodeAll subPackets).length
    let fits: total < Nat.pow 2 15 := omega [Bool.andLeft _ _ others]
    let length := List.lengthAppend (encodeAll subPackets) more
    let id := typeId operation
    totalStep wanted later (version / 2 / 2 % 2 == 1) (version / 2 % 2 == 1) (version % 2 == 1) (id / 2 / 2 % 2 == 1) (id / 2 % 2 == 1) (id % 2 == 1)
      (bitsOf 15 total ++ (encodeAll subPackets ++ more)) version operation total (encodeAll subPackets ++ more) (encodeAll subPackets) more subPackets next
      (fromBitsOf 3 version small) (operationReadBack operation) (readNumberBits 15 total (encodeAll subPackets ++ more) fits)
      (splitFieldAppend (encodeAll subPackets) more total rfl) (omega [length]) (fillComplete subPackets (Bool.andRight _ _ others)) (omega [length])
  | Operator version operation Count subPackets, formed, next =>
    let small: version < Nat.pow 2 3 := omega [Bool.andLeft _ _ formed]
    let others := Bool.andRight _ _ formed
    let count := subPackets.length
    let fits: count < Nat.pow 2 11 := omega [Bool.andLeft _ _ others]
    let length := List.lengthAppend (encodeAll subPackets) more
    let id := typeId operation
    countStep wanted later (version / 2 / 2 % 2 == 1) (version / 2 % 2 == 1) (version % 2 == 1) (id / 2 / 2 % 2 == 1) (id / 2 % 2 == 1) (id % 2 == 1)
      (bitsOf 11 count ++ (encodeAll subPackets ++ more)) version operation count (encodeAll subPackets ++ more) more subPackets next
      (fromBitsOf 3 version small) (operationReadBack operation) (readNumberBits 11 count (encodeAll subPackets ++ more) fits)
      (omega [length]) (countComplete subPackets (Bool.andRight _ _ others) more) (omega [length])

--| Reading as many packets as there are reads them all back.
theorem countComplete: (packets: List Packet) → allWellFormed packets = True → (more: List Bool) →
    readPackets (Packets packets.length) (encodeAll packets ++ more) = Some (packets, more)
  | [], formed, more => rewrite readPackets.unfold (Packets 0) more in rfl
  | [packet, ..rest], formed, more =>
    let step := stepComplete (Packets (Succ rest.length)) (Packets rest.length) (encodeAll rest ++ more) packet (Bool.andLeft _ _ formed) rfl
    rewrite List.appendAssoc (encode packet) (encodeAll rest) more, step, countComplete rest (Bool.andRight _ _ formed) more in rfl

--| Filling packets' bits reads them all back.
theorem fillComplete: (packets: List Packet) → allWellFormed packets = True → readPackets Filling (encodeAll packets) = Some (packets, [])
  | [], formed => rewrite readPackets.unfold Filling [] in rfl
  | [packet, ..rest], formed =>
    let step := stepComplete Filling Filling (encodeAll rest) packet (Bool.andLeft _ _ formed) (fillingNext (encodeAll rest) packet)
    rewrite step, fillComplete rest (Bool.andRight _ _ formed) in rfl
