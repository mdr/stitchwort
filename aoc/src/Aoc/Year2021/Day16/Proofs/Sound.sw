--| Soundness: whatever the decoder reads is well formed, and its encoding
--| is where the bits start.

namespace Aoc.Year2021.Day16.Proofs
import Aoc.Common (BitReader)
import Aoc.Common.Proofs (..)
import Aoc.Year2021.Day16 (..)
import Aoc.Year2021.Day16.Spec (
  allWellFormed,
  encode,
  encodeAll,
  fitsLength,
  groupBits,
  lengthField,
  operatorBits,
  typeId,
  wellFormed
)
import Std (Bool, Decidable, Eq, List, Nat, NonEmptyList, Option, Void)

--| What was wanted was read: that many packets, or packets up to the end
--| of the bits.
def Done: Wanted → List Packet → BitReader → Prop
  | Packets count, packets, _ => packets.length = count
  | Filling, _, rest => rest.unread = []

--| After the next packet, what is still wanted, if read, completes what
--| was wanted.
theorem doneNext ∀ (wanted later: Wanted) (reader: BitReader) (packet: Packet) (more: List Packet) (left: BitReader)
    (next: nextWanted wanted reader = Some later)
    (done: Done later more left):
    Done wanted [packet, ..more] left :=
  match wanted, reader with
    | Packets (Succ count), _ => rewrite <- Option.someInjective next at done in rewrite done in rfl
    | Filling, { unread = [_, .._] } => rewrite <- Option.someInjective next at done in done

--| Nothing more wanted: none was what was wanted.
theorem doneNone ∀ (wanted: Wanted) (reader: BitReader)
    (none: nextWanted wanted reader = None):
    Done wanted [] reader :=
  match wanted, reader with
    | Packets 0, _ => rfl
    | Packets (Succ count), _ => cases
    | Filling, { unread = [] } => rfl

--| A literal with a version below 8 and groups, each below 16.
theorem literalWellFormed ∀ (version: Nat) (groups: NonEmptyList Nat)
    (small: version < 8)
    (each: groups.all (group => group < 16) = True):
    wellFormed (Literal version groups) = True :=
  Both (omega [small]) each

--| The bits of a packet, then of the packets after it.
theorem soundStep ∀ (unread after left: List Bool) (packet: Packet) (more: List Packet)
    (here: unread = encode packet ++ after)
    (later: after = encodeAll more ++ left):
    unread = encodeAll [packet, ..more] ++ left :=
  rewrite here, later in Eq.sym (List.appendAssoc (encode packet) (encodeAll more) left)

--| One packet read, then what was still wanted.
theorem finishStep ∀ (wanted later: Wanted) (reader after left rest: BitReader)
    (packet: Packet) (more packets: List Packet)
    (parts: [packet, ..more] = packets ∧ left = rest)
    (next: nextWanted wanted reader = Some later)
    (here: reader.unread = encode packet ++ after.unread)
    (formed: wellFormed packet = True)
    (laterRead: after.unread = encodeAll more ++ left.unread ∧ allWellFormed more = True ∧ Done later more left):
    reader.unread = encodeAll packets ++ rest.unread ∧ allWellFormed packets = True ∧ Done wanted packets rest :=
  rewrite <- parts.left, <- parts.right in
    Both
      (soundStep reader.unread after.unread left.unread packet more here laterRead.left)
      (Both
        (Both formed laterRead.right.left)
        (doneNext wanted later reader packet more left next laterRead.right.right))

--| A type id below 8 that is no operator type's is 4.
theorem operatorTypeOfNone ∀ (n: Nat) (small: n < 8) (none: operatorTypeOf n = None): n = 4 := match n with
  | 4 => rfl
  | Succ (Succ (Succ (Succ (Succ (Succ (Succ (Succ k))))))) => omega

--| A literal's bits, field by field.
theorem literalHere ∀ (version: Nat) (groups: NonEmptyList Nat) (unread afterVersion afterType after: List Bool)
    (versionField: unread = Nat.toBits 3 version ++ afterVersion)
    (typeField: afterVersion = Nat.toBits 3 4 ++ afterType)
    (groupsField: afterType = groupBits groups ++ after):
    unread = encode (Literal version groups) ++ after :=
  Eq.trans versionField
    (Eq.cong
      (rest => Nat.toBits 3 version ++ rest)
      (Eq.trans typeField (Eq.cong (rest => Nat.toBits 3 4 ++ rest) groupsField)))

--| An operator's bits with a total length, field by field.
theorem totalHere ∀
    (version code count: Nat) (subBits unread afterVersion afterType afterBit afterLength following: List Bool)
    (versionField: unread = Nat.toBits 3 version ++ afterVersion)
    (typeField: afterVersion = Nat.toBits 3 code ++ afterType)
    (lengthType: afterType = [False, ..afterBit])
    (lengthField: afterBit = Nat.toBits 15 subBits.length ++ afterLength)
    (insideField: afterLength = subBits ++ following):
    unread = operatorBits version code TotalLength count subBits ++ following :=
  Eq.trans versionField
    (Eq.cong
      (rest => Nat.toBits 3 version ++ rest)
      (Eq.trans typeField
        (Eq.cong
          (rest => Nat.toBits 3 code ++ rest)
          (Eq.trans lengthType
            (Eq.cong
              (rest => [False, ..rest])
              (Eq.trans lengthField (Eq.cong (rest => Nat.toBits 15 subBits.length ++ rest) insideField)))))))

--| An operator's bits with a number of sub-packets, field by field.
theorem countHere ∀ (version code count: Nat) (subBits unread afterVersion afterType afterBit following: List Bool)
    (versionField: unread = Nat.toBits 3 version ++ afterVersion)
    (typeField: afterVersion = Nat.toBits 3 code ++ afterType)
    (lengthType: afterType = [True, ..afterBit])
    (countField: afterBit = Nat.toBits 11 count ++ (subBits ++ following)):
    unread = operatorBits version code Count count subBits ++ following :=
  Eq.trans versionField
    (Eq.cong
      (rest => Nat.toBits 3 version ++ rest)
      (Eq.trans typeField
        (Eq.cong
          (rest => Nat.toBits 3 code ++ rest)
          (Eq.trans lengthType (Eq.cong (rest => [True, ..rest]) countField)))))

--| The operator made of sub-packets has the bits of an operator with their
--| number and bits.
theorem operatorOfBits ∀ (version: Nat) (operatorType: OperatorType) (lengthType: LengthType)
    (subPackets: List Packet) (packet: Packet)
    (made: operatorOf version operatorType lengthType subPackets = Some packet):
    encode packet = operatorBits version (typeId operatorType) lengthType subPackets.length (encodeAll subPackets) :=
  match operatorType, subPackets with
    | Calculation operation, [first, ..rest] => rewrite <- Option.someInjective made in rfl
    | Comparing comparison, [first, second] =>
      rewrite <- Option.someInjective made in rewrite List.appendNil (encode second) in rfl

--| The operator made of well-formed sub-packets whose bits fit is well
--| formed.
theorem operatorOfWellFormed ∀ (version: Nat) (operatorType: OperatorType) (lengthType: LengthType)
    (subPackets: List Packet) (packet: Packet)
    (made: operatorOf version operatorType lengthType subPackets = Some packet)
    (small: version < 8)
    (fits: fitsLength lengthType subPackets.length (encodeAll subPackets) = True)
    (each: allWellFormed subPackets = True):
    wellFormed packet = True :=
  match operatorType, subPackets with
    | Calculation operation, [first, ..rest] =>
      rewrite <- Option.someInjective made in Both (omega [small]) (Both fits each)
    | Comparing comparison, [first, second] =>
      rewrite <- Option.someInjective made in
        let Both firstOk (Both secondOk _) := each
        Both (omega [small]) (Both (rewrite List.appendNil (encode second) at fits in fits) (Both firstOk secondOk))

theorem readPacketsSound ∀ (wanted: Wanted) (reader: BitReader) (packets: List Packet) (rest: BitReader)
    (read: readPackets wanted reader = Some (packets, rest)):
    reader.unread = encodeAll packets ++ rest.unread ∧ allWellFormed packets = True ∧ Done wanted packets rest
    decreasing reader.length
:=
  rewrite readPackets.unfold wanted reader at read in
    match n: nextWanted wanted reader with
      | None =>
        let parts := somePairInjective read
        rewrite <- parts.left, <- parts.right in Both rfl (Both rfl (doneNone wanted reader n))
      | Some later =>
        match v: reader.readNumber 3 with
          | Some (version, afterVersion) =>
            match t: afterVersion.readNumber 3 with
              | Some (typeCode, afterType) =>
                let versionRead := BitReader.readNumberSome reader 3 version afterVersion v
                let typeRead := BitReader.readNumberSome afterVersion 3 typeCode afterType t
                match o: operatorTypeOf typeCode with
                  | None =>
                    match g: readGroups afterType with
                      | Some (groups, after) =>
                        match d: (after.length < reader.length: Bool) with
                          | True =>
                            let shorter: after.length < reader.length := omega [d]
                            match r: readPackets later after with
                              | Some (more, left) =>
                                let parts := somePairInjective read
                                let groupsRead := readGroupsSome afterType groups after g
                                let laterRead := readPacketsSound later after more left r [decreasing := shorter]
                                let literal: typeCode = 4 := operatorTypeOfNone typeCode (omega [typeRead.right]) o
                                let typeField: afterVersion.unread = Nat.toBits 3 4 ++ afterType.unread :=
                                  Eq.trans typeRead.left
                                    (Eq.cong (code => Nat.toBits 3 code ++ afterType.unread) literal)
                                let here :=
                                  literalHere version groups reader.unread afterVersion.unread afterType.unread
                                      after.unread versionRead.left typeField groupsRead.left
                                let formed :=
                                  literalWellFormed version groups (omega [versionRead.right]) groupsRead.right
                                finishStep wanted later reader after left rest
                                  (Literal version groups)
                                  more
                                  packets
                                  parts
                                  n
                                  here
                                  formed
                                  laterRead
                  | Some operatorType =>
                    let typeField: afterVersion.unread = Nat.toBits 3 (typeId operatorType) ++ afterType.unread :=
                      Eq.trans typeRead.left
                        (Eq.cong
                          (code => Nat.toBits 3 code ++ afterType.unread)
                          (operatorTypeOfSome typeCode operatorType o))
                    match b: afterType.readBit with
                      | Some (False, afterBit) =>
                        match l: afterBit.read 15 with
                          | Some (length, afterLength) =>
                            match sp: afterLength.read length.value with
                              | Some (inside, following) =>
                                match d: ((BitReader.of inside).length < reader.length: Bool) with
                                  | True =>
                                    let shorter: (BitReader.of inside).length < reader.length := omega [d]
                                    match i: readPackets Filling (BitReader.of inside) with
                                      | Some (subPackets, emptied) =>
                                        match made: operatorOf version operatorType TotalLength subPackets with
                                          | Some packet =>
                                            match d2: (following.length < reader.length: Bool) with
                                              | True =>
                                                let shorterAfter: following.length < reader.length := omega [d2]
                                                match r: readPackets later following with
                                                  | Some (more, left) =>
                                                    let parts := somePairInjective read
                                                    let lengthType := BitReader.readBitSome afterType False afterBit b
                                                    let lengthRead :=
                                                      BitReader.readValue afterBit 15 length afterLength l
                                                    let split :=
                                                      BitReader.readSome afterLength length.value inside following sp
                                                    let insideRead :=
                                                      readPacketsSound Filling
                                                        (BitReader.of inside)
                                                        subPackets
                                                        emptied
                                                        i
                                                        [decreasing := shorter]
                                                    let laterRead :=
                                                      readPacketsSound later following more left r
                                                        [decreasing := shorterAfter]
                                                    let exact: inside.bits = encodeAll subPackets :=
                                                      Eq.trans insideRead.left
                                                        (rewrite insideRead.right.right in
                                                          List.appendNil (encodeAll subPackets))
                                                    let lengthEq: (encodeAll subPackets).length = length.value :=
                                                      rewrite <- exact in split.right
                                                    let lengthField: afterBit.unread
                                                      = Nat.toBits 15 (encodeAll subPackets).length
                                                        ++ afterLength.unread :=
                                                      Eq.trans lengthRead.left
                                                        (Eq.cong
                                                          (n => Nat.toBits 15 n ++ afterLength.unread)
                                                          (Eq.sym lengthEq))
                                                    let insideField: afterLength.unread
                                                      = encodeAll subPackets ++ following.unread :=
                                                      Eq.trans split.left
                                                        (Eq.cong (field => field ++ following.unread) exact)
                                                    let hereBits :=
                                                      totalHere version
                                                        (typeId operatorType)
                                                        subPackets.length
                                                        (encodeAll subPackets)
                                                        reader.unread
                                                        afterVersion.unread
                                                        afterType.unread
                                                        afterBit.unread
                                                        afterLength.unread
                                                        following.unread
                                                        versionRead.left
                                                        typeField
                                                        lengthType
                                                        lengthField
                                                        insideField
                                                    let here: reader.unread = encode packet ++ following.unread :=
                                                      Eq.trans hereBits
                                                        (Eq.cong
                                                          (bits => bits ++ following.unread)
                                                          (Eq.sym
                                                            (operatorOfBits version operatorType TotalLength subPackets
                                                                packet made)))
                                                    let formed :=
                                                      operatorOfWellFormed version operatorType TotalLength subPackets packet made
                                                        (omega [versionRead.right])
                                                        (rewrite lengthEq in omega [lengthRead.right])
                                                        insideRead.right.left
                                                    finishStep wanted later reader following left rest packet more
                                                        packets parts n here formed laterRead
                      | Some (True, afterBit) =>
                        match l: afterBit.read 11 with
                          | Some (count, after) =>
                            match d: (after.length < reader.length: Bool) with
                              | True =>
                                let shorter: after.length < reader.length := omega [d]
                                match i: readPackets (Packets count.value) after with
                                  | Some (subPackets, following) =>
                                    match made: operatorOf version operatorType Count subPackets with
                                      | Some packet =>
                                        match d2: (following.length < reader.length: Bool) with
                                          | True =>
                                            let shorterAfter: following.length < reader.length := omega [d2]
                                            match r: readPackets later following with
                                              | Some (more, left) =>
                                                let parts := somePairInjective read
                                                let lengthType := BitReader.readBitSome afterType True afterBit b
                                                let countRead := BitReader.readValue afterBit 11 count after l
                                                let subsRead :=
                                                  readPacketsSound
                                                    (Packets count.value)
                                                    after
                                                    subPackets
                                                    following
                                                    i
                                                    [decreasing := shorter]
                                                let laterRead :=
                                                  readPacketsSound later following more left r
                                                    [decreasing := shorterAfter]
                                                let counted: subPackets.length = count.value := subsRead.right.right
                                                let countField: afterBit.unread
                                                  = Nat.toBits 11 subPackets.length
                                                    ++ (encodeAll subPackets ++ following.unread) :=
                                                  Eq.trans countRead.left
                                                    (Eq.trans
                                                      (Eq.cong
                                                        (rest => Nat.toBits 11 count.value ++ rest)
                                                        subsRead.left)
                                                      (Eq.cong
                                                        (n =>
                                                          Nat.toBits 11 n ++ (encodeAll subPackets ++ following.unread))
                                                        (Eq.sym counted)))
                                                let hereBits :=
                                                  countHere version
                                                    (typeId operatorType)
                                                    subPackets.length
                                                    (encodeAll subPackets)
                                                    reader.unread
                                                    afterVersion.unread
                                                    afterType.unread
                                                    afterBit.unread
                                                    following.unread
                                                    versionRead.left
                                                    typeField
                                                    lengthType
                                                    countField
                                                let here: reader.unread = encode packet ++ following.unread :=
                                                  Eq.trans hereBits
                                                    (Eq.cong
                                                      (bits => bits ++ following.unread)
                                                      (Eq.sym
                                                        (operatorOfBits version operatorType Count subPackets packet
                                                            made)))
                                                let formed :=
                                                  operatorOfWellFormed version operatorType Count subPackets packet made
                                                    (omega [versionRead.right])
                                                    (rewrite counted in omega [countRead.right])
                                                    subsRead.right.left
                                                finishStep wanted later reader following left rest packet more packets
                                                    parts n here formed laterRead
