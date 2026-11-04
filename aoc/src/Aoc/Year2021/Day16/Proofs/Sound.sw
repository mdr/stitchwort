--| Soundness: whatever the decoder reads is well formed, and its encoding
--| is where the bits start.

namespace Aoc.Year2021.Day16.Proofs
import Aoc.Year2021.Day16 (..)
import Aoc.Year2021.Day16.Spec (allWellFormed, encode, encodeAll, groupBits, typeId, wellFormed)
import Std (Bool, DecEq, Decidable, Eq, List, Nat, Option, Pair, Void)

--| What was wanted was read: that many packets, or packets up to the end
--| of the bits.
def Done: Wanted → List Packet → List Bool → Prop
  | Packets count, packets, _ => packets.length = count
  | Filling, _, rest => rest = []

--| After the next packet, what is still wanted, if read, completes what
--| was wanted.
theorem doneNext (wanted: Wanted) (later: Wanted) (bits: List Bool) (packet: Packet) (more: List Packet) (left: List Bool)
    (next: nextWanted wanted bits = Some later) (done: Done later more left): Done wanted [packet, ..more] left :=
  match wanted, bits with
    | Packets 0, _ => cases
    | Packets (Succ count), _ => rewrite <- Option.someInjective _ _ next at done in rewrite done in rfl
    | Filling, [] => cases
    | Filling, [_, .._] => rewrite <- Option.someInjective _ _ next at done in done

--| Nothing more wanted: none was what was wanted.
theorem doneNone (wanted: Wanted) (bits: List Bool) (none: nextWanted wanted bits = None): Done wanted [] bits :=
  match wanted, bits with
    | Packets 0, _ => rfl
    | Packets (Succ count), _ => cases
    | Filling, [] => rfl
    | Filling, [_, .._] => cases

--| A literal with a version below 8 and groups, each below 16.
theorem literalWellFormed (version: Nat) (groups: List Nat) (small: version < 8) (some: groups ≠ []) (each: groups.all (group => group < 16) = True):
    wellFormed (Literal version groups) = True :=
  Bool.andIntro _ _ (omega [small]) (Bool.andIntro _ _ (Decidable.toBoolOf _ some) each)

--| The bits of a packet, then of the packets after it.
theorem soundStep (bits: List Bool) (after: List Bool) (left: List Bool) (packet: Packet) (more: List Packet)
    (here: bits = encode packet ++ after) (later: after = encodeAll more ++ left): bits = encodeAll [packet, ..more] ++ left :=
  rewrite here, later in Eq.sym (List.appendAssoc (encode packet) (encodeAll more) left)

--| One packet read, then what was still wanted.
theorem finishStep (wanted: Wanted) (later: Wanted) (bits: List Bool) (after: List Bool) (left: List Bool) (rest: List Bool) (packet: Packet)
    (more: List Packet) (packets: List Packet) (parts: [packet, ..more] = packets ∧ left = rest) (next: nextWanted wanted bits = Some later)
    (here: bits = encode packet ++ after) (formed: wellFormed packet = True) (laterRead: after = encodeAll more ++ left ∧ allWellFormed more = True ∧ Done later more left):
    bits = encodeAll packets ++ rest ∧ allWellFormed packets = True ∧ Done wanted packets rest :=
  rewrite <- parts.left, <- parts.right in
    Both (soundStep bits after left packet more here laterRead.left) (Both (Bool.andIntro _ _ formed laterRead.right.left) (doneNext wanted later bits packet more left next laterRead.right.right))

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

--| Three bits read as a number are that number in three bits.
theorem threeBits (a: Bool) (b: Bool) (c: Bool): [a, b, c] = Nat.toBits 3 (Nat.fromBits [a, b, c]) := Eq.sym (Nat.toBitsFromBits [a, b, c])

theorem appendCong3 (a1: List Bool) (a2: List Bool) (b1: List Bool) (b2: List Bool) (c1: List Bool) (c2: List Bool) (ea: a1 = a2) (eb: b1 = b2) (ec: c1 = c2):
    a1 ++ (b1 ++ c1) = a2 ++ (b2 ++ c2) :=
  rewrite ea, eb, ec in rfl

--| A literal's bits, then more.
theorem literalThen (version: Nat) (groups: List Nat) (after: List Bool):
    encode (Literal version groups) ++ after = Nat.toBits 3 version ++ (Nat.toBits 3 4 ++ (groupBits groups ++ after)) :=
  rfl

theorem consAppendCong (bit: Bool) (a1: List Bool) (a2: List Bool) (b1: List Bool) (b2: List Bool) (ea: a1 = a2) (eb: b1 = b2): [bit, ..a1 ++ b1] = [bit, ..a2 ++ b2] :=
  rewrite ea, eb in rfl

--| An operator's bits, then more.
theorem totalThen (version: Nat) (operation: Operation) (subPackets: List Packet) (after: List Bool):
    encode (Operator version operation TotalLength subPackets) ++ after =
      Nat.toBits 3 version ++ (Nat.toBits 3 (typeId operation) ++ [False, ..Nat.toBits 15 (encodeAll subPackets).length ++ (encodeAll subPackets ++ after)]) :=
  rfl

theorem countThen (version: Nat) (operation: Operation) (subPackets: List Packet) (after: List Bool):
    encode (Operator version operation Count subPackets) ++ after =
      Nat.toBits 3 version ++ (Nat.toBits 3 (typeId operation) ++ [True, ..Nat.toBits 11 subPackets.length ++ (encodeAll subPackets ++ after)]) :=
  rfl

--| An operator's fields: a bit, a number field, then the sub-packets
--| and what follows.
-- (Stated for any field, so that no `Nat.toBits` is computed while
-- rewriting.)
theorem fieldsCong (bit: Bool) (fields: List Bool) (after: List Bool) (inside: List Bool) (following: List Bool) (field: List Bool) (field2: List Bool)
    (sub: List Bool) (read: fields = field ++ after) (split: after = inside ++ following) (exact: inside = sub) (same: field = field2):
    [bit, ..fields] = [bit, ..field2 ++ (sub ++ following)] :=
  rewrite read, split, exact, same in rfl

theorem totalWellFormed (version: Nat) (operation: Operation) (subPackets: List Packet) (small: version < 8) (fits: (encodeAll subPackets).length < 32768)
    (each: allWellFormed subPackets = True): wellFormed (Operator version operation TotalLength subPackets) = True :=
  Bool.andIntro _ _ (omega [small]) (Bool.andIntro _ _ (omega [fits]) each)

theorem countWellFormed (version: Nat) (operation: Operation) (subPackets: List Packet) (small: version < 8) (fits: subPackets.length < 2048)
    (each: allWellFormed subPackets = True): wellFormed (Operator version operation Count subPackets) = True :=
  Bool.andIntro _ _ (omega [small]) (Bool.andIntro _ _ (omega [fits]) each)

theorem readPacketsSound (wanted: Wanted) (bits: List Bool) (packets: List Packet) (rest: List Bool) (read: readPackets wanted bits = Some (packets, rest)):
    bits = encodeAll packets ++ rest ∧ allWellFormed packets = True ∧ Done wanted packets rest
    decreasing bits.length
:=
  rewrite readPackets.unfold wanted bits at read in
  match n: nextWanted wanted bits with
    | None =>
      let parts := somePairInjective _ _ _ _ read
      rewrite <- parts.left, <- parts.right in Both rfl (Both rfl (doneNone wanted bits n))
    | Some later =>
      match bits with
        | [v1, v2, v3, t1, t2, t3, ..rest6] =>
          match o: operationOf (Nat.fromBits [t1, t2, t3]) with
            | None =>
              match g: readGroups rest6 with
                | None => cases
                | Some (groups, after) =>
                  match d: Nat.decLessThan after.length [v1, v2, v3, t1, t2, t3, ..rest6].length with
                    | No _ => cases
                    | Yes shorter =>
                      match r: readPackets later after with
                        | None => cases
                        | Some (more, left) =>
                          let parts := somePairInjective _ _ _ _ read
                          let groupsRead := readGroupsSome rest6 groups after g
                          let laterRead := readPacketsSound later after more left r [decreasing := shorter]
                          let version := Nat.fromBits [v1, v2, v3]
                          let literal: [t1, t2, t3] = Nat.toBits 3 4 := rewrite threeBits t1 t2 t3, operationOfNone _ (Nat.fromBitsBelow [t1, t2, t3]) o in rfl
                          let here: [v1, v2, v3, t1, t2, t3, ..rest6] = encode (Literal version groups) ++ after :=
                            Eq.trans (appendCong3 _ _ _ _ _ _ (threeBits v1 v2 v3) literal groupsRead.left) (Eq.sym (literalThen version groups after))
                          let formed := literalWellFormed version groups (Nat.fromBitsBelow [v1, v2, v3]) groupsRead.right.left groupsRead.right.right
                          finishStep wanted later _ after left rest (Literal version groups) more packets parts n here formed laterRead
            | Some operation =>
              let version := Nat.fromBits [v1, v2, v3]
              let typeBits: [t1, t2, t3] = Nat.toBits 3 (typeId operation) := rewrite threeBits t1 t2 t3, operationOfSome _ operation o in rfl
              match rest6 with
                | [] => cases
                | [False, ..fields] =>
                  match l: readNumber 15 fields with
                    | None => cases
                    | Some (length, after) =>
                      match sp: splitField length after with
                        | None => cases
                        | Some (inside, following) =>
                          match d: Nat.decLessThan inside.length [v1, v2, v3, t1, t2, t3, False, ..fields].length with
                            | No _ => cases
                            | Yes shorter =>
                              match i: readPackets Filling inside with
                                | None => cases
                                | Some (subPackets, emptied) =>
                                  match d2: Nat.decLessThan following.length [v1, v2, v3, t1, t2, t3, False, ..fields].length with
                                    | No _ => cases
                                    | Yes shorterAfter =>
                                      match r: readPackets later following with
                                        | None => cases
                                        | Some (more, left) =>
                                          let parts := somePairInjective _ _ _ _ read
                                          let lengthRead := readNumberSome 15 fields length after l
                                          let split := splitFieldSome length after inside following sp
                                          let insideRead := readPacketsSound Filling inside subPackets emptied i [decreasing := shorter]
                                          let laterRead := readPacketsSound later following more left r [decreasing := shorterAfter]
                                          let emptiedNil: emptied = [] := insideRead.right.right
                                          let exact: inside = encodeAll subPackets := Eq.trans insideRead.left (rewrite emptiedNil in List.appendNil (encodeAll subPackets))
                                          let lengthEq: (encodeAll subPackets).length = length := rewrite <- exact in split.right
                                          let fieldsEq: [False, ..fields] = [False, ..Nat.toBits 15 (encodeAll subPackets).length ++ (encodeAll subPackets ++ following)] :=
                                            fieldsCong False fields after inside following (Nat.toBits 15 length) (Nat.toBits 15 (encodeAll subPackets).length) (encodeAll subPackets) lengthRead.left split.left exact
                                              (Eq.cong (Nat.toBits 15) (Eq.sym lengthEq))
                                          let packet := Operator version operation TotalLength subPackets
                                          let here: [v1, v2, v3, t1, t2, t3, False, ..fields] = encode packet ++ following :=
                                            Eq.trans (appendCong3 [v1, v2, v3] (Nat.toBits 3 version) [t1, t2, t3] (Nat.toBits 3 (typeId operation)) [False, ..fields] [False, ..Nat.toBits 15 (encodeAll subPackets).length ++ (encodeAll subPackets ++ following)] (threeBits v1 v2 v3) typeBits fieldsEq)
                                              (Eq.sym (totalThen version operation subPackets following))
                                          let formed := totalWellFormed version operation subPackets (Nat.fromBitsBelow [v1, v2, v3]) (rewrite lengthEq in lengthRead.right) insideRead.right.left
                                          finishStep wanted later _ following left rest packet more packets parts n here formed laterRead
                | [True, ..fields] =>
                  match l: readNumber 11 fields with
                    | None => cases
                    | Some (count, after) =>
                      match d: Nat.decLessThan after.length [v1, v2, v3, t1, t2, t3, True, ..fields].length with
                        | No _ => cases
                        | Yes shorter =>
                          match i: readPackets (Packets count) after with
                            | None => cases
                            | Some (subPackets, following) =>
                              match d2: Nat.decLessThan following.length [v1, v2, v3, t1, t2, t3, True, ..fields].length with
                                | No _ => cases
                                | Yes shorterAfter =>
                                  match r: readPackets later following with
                                    | None => cases
                                    | Some (more, left) =>
                                      let parts := somePairInjective _ _ _ _ read
                                      let countRead := readNumberSome 11 fields count after l
                                      let subsRead := readPacketsSound (Packets count) after subPackets following i [decreasing := shorter]
                                      let laterRead := readPacketsSound later following more left r [decreasing := shorterAfter]
                                      let counted: subPackets.length = count := subsRead.right.right
                                      let fieldsEq: [True, ..fields] = [True, ..Nat.toBits 11 subPackets.length ++ (encodeAll subPackets ++ following)] :=
                                        fieldsCong True fields after (encodeAll subPackets) following (Nat.toBits 11 count) (Nat.toBits 11 subPackets.length) (encodeAll subPackets) countRead.left subsRead.left rfl
                                          (Eq.cong (Nat.toBits 11) (Eq.sym counted))
                                      let packet := Operator version operation Count subPackets
                                      let here: [v1, v2, v3, t1, t2, t3, True, ..fields] = encode packet ++ following :=
                                        Eq.trans (appendCong3 [v1, v2, v3] (Nat.toBits 3 version) [t1, t2, t3] (Nat.toBits 3 (typeId operation)) [True, ..fields] [True, ..Nat.toBits 11 subPackets.length ++ (encodeAll subPackets ++ following)] (threeBits v1 v2 v3) typeBits fieldsEq)
                                          (Eq.sym (countThen version operation subPackets following))
                                      let formed := countWellFormed version operation subPackets (Nat.fromBitsBelow [v1, v2, v3]) (rewrite counted in countRead.right) subsRead.right.left
                                      finishStep wanted later _ following left rest packet more packets parts n here formed laterRead
        | [] => cases
        | [_] => cases
        | [_, _] => cases
        | [_, _, _] => cases
        | [_, _, _, _] => cases
        | [_, _, _, _, _] => cases
