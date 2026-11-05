--| Soundness: whatever the decoder reads is well formed, and its encoding
--| is where the bits start.

namespace Aoc.Year2021.Day16.Proofs
import Aoc.Common (BitReader)
import Aoc.Common.Proofs (..)
import Aoc.Year2021.Day16 (..)
import Aoc.Year2021.Day16.Spec (allWellFormed, encode, encodeAll, groupBits, typeId, wellFormed)
import Std (Bool, Decidable, Eq, List, Nat, NonEmptyList, Option, Void)

--| What was wanted was read: that many packets, or packets up to the end
--| of the bits.
def Done: Wanted → List Packet → BitReader → Prop
  | Packets count, packets, _ => packets.length = count
  | Filling, _, rest => rest.unread = []

--| After the next packet, what is still wanted, if read, completes what
--| was wanted.
theorem doneNext (wanted: Wanted) (later: Wanted) (reader: BitReader) (packet: Packet) (more: List Packet) (left: BitReader)
    (next: nextWanted wanted reader = Some later) (done: Done later more left): Done wanted [packet, ..more] left :=
  match wanted, reader with
    | Packets 0, _ => cases
    | Packets (Succ count), _ => rewrite <- Option.someInjective _ _ next at done in rewrite done in rfl
    | Filling, { unread = [] } => cases
    | Filling, { unread = [_, .._] } => rewrite <- Option.someInjective _ _ next at done in done

--| Nothing more wanted: none was what was wanted.
theorem doneNone (wanted: Wanted) (reader: BitReader) (none: nextWanted wanted reader = None): Done wanted [] reader :=
  match wanted, reader with
    | Packets 0, _ => rfl
    | Packets (Succ count), _ => cases
    | Filling, { unread = [] } => rfl
    | Filling, { unread = [_, .._] } => cases

--| A literal with a version below 8 and groups, each below 16.
theorem literalWellFormed (version: Nat) (groups: NonEmptyList Nat) (small: version < 8) (each: groups.all (group => group < 16) = True):
    wellFormed (Literal version groups) = True :=
  Bool.andIntro _ _ (omega [small]) each

--| The bits of a packet, then of the packets after it.
theorem soundStep (unread: List Bool) (after: List Bool) (left: List Bool) (packet: Packet) (more: List Packet)
    (here: unread = encode packet ++ after) (later: after = encodeAll more ++ left): unread = encodeAll [packet, ..more] ++ left :=
  rewrite here, later in Eq.sym (List.appendAssoc (encode packet) (encodeAll more) left)

--| One packet read, then what was still wanted.
theorem finishStep (wanted: Wanted) (later: Wanted) (reader: BitReader) (after: BitReader) (left: BitReader) (rest: BitReader) (packet: Packet)
    (more: List Packet) (packets: List Packet) (parts: [packet, ..more] = packets ∧ left = rest) (next: nextWanted wanted reader = Some later)
    (here: reader.unread = encode packet ++ after.unread) (formed: wellFormed packet = True)
    (laterRead: after.unread = encodeAll more ++ left.unread ∧ allWellFormed more = True ∧ Done later more left):
    reader.unread = encodeAll packets ++ rest.unread ∧ allWellFormed packets = True ∧ Done wanted packets rest :=
  rewrite <- parts.left, <- parts.right in
    Both (soundStep reader.unread after.unread left.unread packet more here laterRead.left)
      (Both (Bool.andIntro _ _ formed laterRead.right.left) (doneNext wanted later reader packet more left next laterRead.right.right))

--| A type id below 8 that is no operation's is 4.
theorem operationOfNone (n: Nat) (small: n < 8) (none: operationOf n = None): n = 4 :=
  match n with
    | 4 => rfl
    | 0 => cases
    | 1 => cases
    | 2 => cases
    | 3 => cases
    | 5 => cases
    | 6 => cases
    | 7 => cases
    | Succ (Succ (Succ (Succ (Succ (Succ (Succ (Succ k))))))) => omega

--| A literal's bits, field by field.
theorem literalHere (version: Nat) (groups: NonEmptyList Nat) (unread: List Bool) (afterVersion: List Bool) (afterType: List Bool) (after: List Bool)
    (versionField: unread = Nat.toBits 3 version ++ afterVersion) (typeField: afterVersion = Nat.toBits 3 4 ++ afterType)
    (groupsField: afterType = groupBits groups ++ after): unread = encode (Literal version groups) ++ after :=
  Eq.trans versionField (Eq.cong (rest => Nat.toBits 3 version ++ rest) (Eq.trans typeField (Eq.cong (rest => Nat.toBits 3 4 ++ rest) groupsField)))

--| An operator's bits with a total length, field by field.
theorem totalHere (version: Nat) (operation: Operation) (subPackets: List Packet) (unread: List Bool) (afterVersion: List Bool) (afterType: List Bool)
    (afterBit: List Bool) (afterLength: List Bool) (following: List Bool) (versionField: unread = Nat.toBits 3 version ++ afterVersion)
    (typeField: afterVersion = Nat.toBits 3 (typeId operation) ++ afterType) (lengthType: afterType = [False, ..afterBit])
    (lengthField: afterBit = Nat.toBits 15 (encodeAll subPackets).length ++ afterLength) (insideField: afterLength = encodeAll subPackets ++ following):
    unread = encode (Operator version operation TotalLength subPackets) ++ following :=
  Eq.trans versionField (Eq.cong (rest => Nat.toBits 3 version ++ rest) (Eq.trans typeField (Eq.cong (rest => Nat.toBits 3 (typeId operation) ++ rest)
    (Eq.trans lengthType (Eq.cong (rest => [False, ..rest]) (Eq.trans lengthField (Eq.cong (rest => Nat.toBits 15 (encodeAll subPackets).length ++ rest) insideField)))))))

--| An operator's bits with a number of sub-packets, field by field.
theorem countHere (version: Nat) (operation: Operation) (subPackets: List Packet) (unread: List Bool) (afterVersion: List Bool) (afterType: List Bool)
    (afterBit: List Bool) (following: List Bool) (versionField: unread = Nat.toBits 3 version ++ afterVersion)
    (typeField: afterVersion = Nat.toBits 3 (typeId operation) ++ afterType) (lengthType: afterType = [True, ..afterBit])
    (countField: afterBit = Nat.toBits 11 subPackets.length ++ (encodeAll subPackets ++ following)):
    unread = encode (Operator version operation Count subPackets) ++ following :=
  Eq.trans versionField (Eq.cong (rest => Nat.toBits 3 version ++ rest) (Eq.trans typeField (Eq.cong (rest => Nat.toBits 3 (typeId operation) ++ rest)
    (Eq.trans lengthType (Eq.cong (rest => [True, ..rest]) countField)))))

theorem totalWellFormed (version: Nat) (operation: Operation) (subPackets: List Packet) (small: version < 8) (fits: (encodeAll subPackets).length < 32768)
    (each: allWellFormed subPackets = True): wellFormed (Operator version operation TotalLength subPackets) = True :=
  Bool.andIntro _ _ (omega [small]) (Bool.andIntro _ _ (omega [fits]) each)

theorem countWellFormed (version: Nat) (operation: Operation) (subPackets: List Packet) (small: version < 8) (fits: subPackets.length < 2048)
    (each: allWellFormed subPackets = True): wellFormed (Operator version operation Count subPackets) = True :=
  Bool.andIntro _ _ (omega [small]) (Bool.andIntro _ _ (omega [fits]) each)

theorem readPacketsSound (wanted: Wanted) (reader: BitReader) (packets: List Packet) (rest: BitReader) (read: readPackets wanted reader = Some (packets, rest)):
    reader.unread = encodeAll packets ++ rest.unread ∧ allWellFormed packets = True ∧ Done wanted packets rest
    decreasing reader.length
:=
  rewrite readPackets.unfold wanted reader at read in
  match n: nextWanted wanted reader with
    | None =>
      let parts := somePairInjective _ _ _ _ read
      rewrite <- parts.left, <- parts.right in Both rfl (Both rfl (doneNone wanted reader n))
    | Some later =>
      match v: reader.readNumber 3 with
        | None => cases
        | Some (version, afterVersion) =>
          match t: afterVersion.readNumber 3 with
            | None => cases
            | Some (typeCode, afterType) =>
              let versionRead := BitReader.readNumberSome reader 3 version afterVersion v
              let typeRead := BitReader.readNumberSome afterVersion 3 typeCode afterType t
              match o: operationOf typeCode with
                | None =>
                  match g: readGroups afterType with
                    | None => cases
                    | Some (groups, after) =>
                      match d: Nat.decLessThan after.length reader.length with
                        | No _ => cases
                        | Yes shorter =>
                          match r: readPackets later after with
                            | None => cases
                            | Some (more, left) =>
                              let parts := somePairInjective _ _ _ _ read
                              let groupsRead := readGroupsSome afterType groups after g
                              let laterRead := readPacketsSound later after more left r [decreasing := shorter]
                              let literal: typeCode = 4 := operationOfNone typeCode (omega [typeRead.right]) o
                              let typeField: afterVersion.unread = Nat.toBits 3 4 ++ afterType.unread := Eq.trans typeRead.left (Eq.cong (code => Nat.toBits 3 code ++ afterType.unread) literal)
                              let here := literalHere version groups reader.unread afterVersion.unread afterType.unread after.unread versionRead.left typeField groupsRead.left
                              let formed := literalWellFormed version groups (omega [versionRead.right]) groupsRead.right
                              finishStep wanted later reader after left rest (Literal version groups) more packets parts n here formed laterRead
                | Some operation =>
                  let typeField: afterVersion.unread = Nat.toBits 3 (typeId operation) ++ afterType.unread :=
                    Eq.trans typeRead.left (Eq.cong (code => Nat.toBits 3 code ++ afterType.unread) (operationOfSome typeCode operation o))
                  match b: afterType.readBit with
                    | None => cases
                    | Some (False, afterBit) =>
                      match l: afterBit.read 15 with
                        | None => cases
                        | Some (length, afterLength) =>
                          match sp: afterLength.read length.value with
                            | None => cases
                            | Some (inside, following) =>
                              match d: Nat.decLessThan (BitReader.of inside).length reader.length with
                                | No _ => cases
                                | Yes shorter =>
                                  match i: readPackets Filling (BitReader.of inside) with
                                    | None => cases
                                    | Some (subPackets, emptied) =>
                                      match d2: Nat.decLessThan following.length reader.length with
                                        | No _ => cases
                                        | Yes shorterAfter =>
                                          match r: readPackets later following with
                                            | None => cases
                                            | Some (more, left) =>
                                              let parts := somePairInjective _ _ _ _ read
                                              let lengthType := BitReader.readBitSome afterType False afterBit b
                                              let lengthRead := BitReader.readValue afterBit 15 length afterLength l
                                              let split := BitReader.readSome afterLength length.value inside following sp
                                              let insideRead := readPacketsSound Filling (BitReader.of inside) subPackets emptied i [decreasing := shorter]
                                              let laterRead := readPacketsSound later following more left r [decreasing := shorterAfter]
                                              let exact: inside.bits = encodeAll subPackets := Eq.trans insideRead.left (rewrite insideRead.right.right in List.appendNil (encodeAll subPackets))
                                              let lengthEq: (encodeAll subPackets).length = length.value := rewrite <- exact in split.right
                                              let lengthField: afterBit.unread = Nat.toBits 15 (encodeAll subPackets).length ++ afterLength.unread :=
                                                Eq.trans lengthRead.left (Eq.cong (n => Nat.toBits 15 n ++ afterLength.unread) (Eq.sym lengthEq))
                                              let insideField: afterLength.unread = encodeAll subPackets ++ following.unread := Eq.trans split.left (Eq.cong (field => field ++ following.unread) exact)
                                              let packet := Operator version operation TotalLength subPackets
                                              let here := totalHere version operation subPackets reader.unread afterVersion.unread afterType.unread afterBit.unread afterLength.unread
                                                following.unread versionRead.left typeField lengthType lengthField insideField
                                              let formed := totalWellFormed version operation subPackets (omega [versionRead.right]) (rewrite lengthEq in omega [lengthRead.right]) insideRead.right.left
                                              finishStep wanted later reader following left rest packet more packets parts n here formed laterRead
                    | Some (True, afterBit) =>
                      match l: afterBit.read 11 with
                        | None => cases
                        | Some (count, after) =>
                          match d: Nat.decLessThan after.length reader.length with
                            | No _ => cases
                            | Yes shorter =>
                              match i: readPackets (Packets count.value) after with
                                | None => cases
                                | Some (subPackets, following) =>
                                  match d2: Nat.decLessThan following.length reader.length with
                                    | No _ => cases
                                    | Yes shorterAfter =>
                                      match r: readPackets later following with
                                        | None => cases
                                        | Some (more, left) =>
                                          let parts := somePairInjective _ _ _ _ read
                                          let lengthType := BitReader.readBitSome afterType True afterBit b
                                          let countRead := BitReader.readValue afterBit 11 count after l
                                          let subsRead := readPacketsSound (Packets count.value) after subPackets following i [decreasing := shorter]
                                          let laterRead := readPacketsSound later following more left r [decreasing := shorterAfter]
                                          let counted: subPackets.length = count.value := subsRead.right.right
                                          let countField: afterBit.unread = Nat.toBits 11 subPackets.length ++ (encodeAll subPackets ++ following.unread) :=
                                            Eq.trans countRead.left (Eq.trans (Eq.cong (rest => Nat.toBits 11 count.value ++ rest) subsRead.left)
                                              (Eq.cong (n => Nat.toBits 11 n ++ (encodeAll subPackets ++ following.unread)) (Eq.sym counted)))
                                          let packet := Operator version operation Count subPackets
                                          let here := countHere version operation subPackets reader.unread afterVersion.unread afterType.unread afterBit.unread following.unread
                                            versionRead.left typeField lengthType countField
                                          let formed := countWellFormed version operation subPackets (omega [versionRead.right]) (rewrite counted in omega [countRead.right]) subsRead.right.left
                                          finishStep wanted later reader following left rest packet more packets parts n here formed laterRead
