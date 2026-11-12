--| The decoder's pieces that read no packets: a literal's groups and an
--| operator's type id. Each reads exactly the spec's bits for what it gives
--| back. (Reading a field is `BitReader`'s, in Aoc.Common.Proofs.)

namespace Aoc.Year2021.Day16.Proofs
import Aoc.Common (BitReader)
import Aoc.Common.Proofs (..)
import Aoc.Year2021.Day16 (..)
import Aoc.Year2021.Day16.Spec (groupBits, groupBitsFrom, typeId)
import Std (Bool, Eq, List, Nat, NonEmptyList, Option, Void)

--| The last group: a bit saying no more follow, then four bits.
theorem readGroupsLast (reader: BitReader) (afterBit: BitReader) (after: BitReader) (group: Nat) (bit: reader.readBit = Some (False, afterBit))
    (number: afterBit.readNumber 4 = Some (group, after)): readGroups reader = Some (NonEmptyList.singleton group, after) :=
  rewrite readGroups.unfold reader, bit, number in rfl

--| A group that another follows.
theorem readGroupsMore (reader: BitReader) (afterBit: BitReader) (after: BitReader) (group: Nat) (groups: NonEmptyList Nat) (rest: BitReader)
    (bit: reader.readBit = Some (True, afterBit)) (number: afterBit.readNumber 4 = Some (group, after)) (shorter: after.length < reader.length)
    (others: readGroups after = Some (groups, rest)): readGroups reader = Some (NonEmptyList.cons group groups.toList, rest) :=
  rewrite readGroups.unfold reader, bit, number in
    match h: (after.length < reader.length: Bool) with
      | True => rewrite others in rfl

--| A literal's groups, each below 16, are read back from their bits.
theorem readGroupsBitsFrom (rest: List Bool) (tail: List Nat) (group: Nat) (small: ({ head = group, tail }: NonEmptyList Nat).all (group => group < 16) = True):
    readGroups { unread = groupBitsFrom group tail ++ rest } = Some ({ head = group, tail }, { unread = rest }) :=
  match tail with
    | [] =>
      readGroupsLast { unread = groupBitsFrom group [] ++ rest } { unread = Nat.toBits 4 group ++ rest } { unread = rest } group rfl
        (BitReader.readNumberAppend 4 group rest (omega [small]))
    | [next, ..more] =>
      let fits: group < 16 := omega [small]
      let others: ({ head = next, tail = more }: NonEmptyList Nat).all (group => group < 16) = True := Bool.andRight small
      let tail := groupBitsFrom next more ++ rest
      let length := List.lengthAppend (Nat.toBits 4 group) tail
      readGroupsMore { unread = groupBitsFrom group [next, ..more] ++ rest } { unread = Nat.toBits 4 group ++ tail } { unread = tail } group { head = next, tail = more } { unread = rest } rfl
        (BitReader.readNumberAppend 4 group tail (omega [fits])) (omega [length, Nat.toBitsLength 4 group]) (readGroupsBitsFrom rest more next others)

theorem readGroupsBits (rest: List Bool) (groups: NonEmptyList Nat) (small: groups.all (group => group < 16) = True):
    readGroups { unread = groupBits groups ++ rest } = Some (groups, { unread = rest }) :=
  match groups with
    | { head, tail } => readGroupsBitsFrom rest tail head small

--| What `readGroups` reads is the spec's bits for the groups it gives,
--| each below 16.
theorem readGroupsSome (reader: BitReader) (groups: NonEmptyList Nat) (rest: BitReader) (read: readGroups reader = Some (groups, rest)):
    reader.unread = groupBits groups ++ rest.unread ∧ groups.all (group => group < 16) = True
    decreasing reader.length
:=
  rewrite readGroups.unfold reader at read in
  match b: reader.readBit with
    | Some (more, afterMore) =>
      match n: afterMore.readNumber 4 with
        | Some (group, after) =>
          let bitRead := BitReader.readBitSome reader more afterMore b
          let numberRead := BitReader.readNumberSome afterMore 4 group after n
          let fits: group < 16 := omega [numberRead.right]
          match more with
            | True =>
              match d: (after.length < reader.length: Bool) with
                | True =>
                  let shorter: after.length < reader.length := omega [d]
                  match g: readGroups after with
                    | Some (gs, others) =>
                      let parts := somePairInjective read
                      match readGroupsSome after gs others g [decreasing := shorter] with
                        | Both split small =>
                          let first: (group < 16) = True := omega [fits]
                          rewrite <- parts.left, <- parts.right in
                            Both (rewrite bitRead, numberRead.left, split in rfl) (Bool.andIntro first small)
            | False =>
              let parts := somePairInjective read
              let small: (NonEmptyList.singleton group).all (x => x < 16) = True := omega [fits]
              rewrite <- parts.left, <- parts.right in Both (rewrite bitRead, numberRead.left in rfl) small

--| Each operator type is read back from its type id.
theorem operatorTypeOfTypeId (operatorType: OperatorType): operatorTypeOf (typeId operatorType) = Some operatorType := cases

--| An operator type is read only from its type id.
theorem operatorTypeOfSome (n: Nat) (operatorType: OperatorType) (read: operatorTypeOf n = Some operatorType): n = typeId operatorType :=
  match n with
    | 0 => rewrite <- Option.someInjective read in rfl
    | 1 => rewrite <- Option.someInjective read in rfl
    | 2 => rewrite <- Option.someInjective read in rfl
    | 3 => rewrite <- Option.someInjective read in rfl
    | 5 => rewrite <- Option.someInjective read in rfl
    | 6 => rewrite <- Option.someInjective read in rfl
    | 7 => rewrite <- Option.someInjective read in rfl
