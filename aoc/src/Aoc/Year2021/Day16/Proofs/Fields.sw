--| The decoder's pieces that read no packets: a literal's groups and an
--| operator's type id. Each reads exactly the spec's bits for what it gives
--| back. (Reading a field is `BitReader`'s, in Aoc.Common.Proofs.)

namespace Aoc.Year2021.Day16.Proofs
import Aoc.Common (BitReader)
import Aoc.Common.Proofs (..)
import Aoc.Year2021.Day16 (..)
import Aoc.Year2021.Day16.Spec (groupBits, typeId)
import Std (Bool, Eq, List, Nat, Option, Void)

--| The last group: a bit saying no more follow, then four bits.
theorem readGroupsLast (reader: BitReader) (afterBit: BitReader) (after: BitReader) (group: Nat) (bit: reader.readBit = Some (False, afterBit))
    (number: afterBit.readNumber 4 = Some (group, after)): readGroups reader = Some ([group], after) :=
  rewrite readGroups.unfold reader, bit, number in rfl

--| A group that another follows.
theorem readGroupsMore (reader: BitReader) (afterBit: BitReader) (after: BitReader) (group: Nat) (groups: List Nat) (rest: BitReader)
    (bit: reader.readBit = Some (True, afterBit)) (number: afterBit.readNumber 4 = Some (group, after)) (shorter: after.length < reader.length)
    (others: readGroups after = Some (groups, rest)): readGroups reader = Some ([group, ..groups], rest) :=
  rewrite readGroups.unfold reader, bit, number in
    match Nat.decLessThan after.length reader.length with
      | Yes _ => rewrite others in rfl
      | No longer => Void.exfalso (longer shorter)

--| A literal's groups, each below 16, are read back from their bits.
theorem readGroupsBits (rest: List Bool): (groups: List Nat) → groups ≠ [] → groups.all (group => group < 16) = True →
    readGroups { unread = groupBits groups ++ rest } = Some (groups, { unread = rest })
  | [], some, small => Void.exfalso (some rfl)
  | [group], some, small =>
    readGroupsLast { unread = groupBits [group] ++ rest } { unread = Nat.toBits 4 group ++ rest } { unread = rest } group rfl
      (BitReader.readNumberAppend 4 group rest (omega [small]))
  | [group, next, ..more], some, small =>
    let fits: group < 16 := omega [small]
    let others: [next, ..more].all (group => group < 16) = True := Bool.andRight _ _ small
    let tail := groupBits [next, ..more] ++ rest
    let length := List.lengthAppend (Nat.toBits 4 group) tail
    readGroupsMore { unread = groupBits [group, next, ..more] ++ rest } { unread = Nat.toBits 4 group ++ tail } { unread = tail } group [next, ..more] { unread = rest } rfl
      (BitReader.readNumberAppend 4 group tail (omega [fits])) (omega [length, Nat.toBitsLength 4 group]) (readGroupsBits rest [next, ..more] (u => cases) others)

--| What `readGroups` reads is the spec's bits for the groups it gives,
--| at least one, each below 16.
theorem readGroupsSome (reader: BitReader) (groups: List Nat) (rest: BitReader) (read: readGroups reader = Some (groups, rest)):
    reader.unread = groupBits groups ++ rest.unread ∧ groups ≠ [] ∧ groups.all (group => group < 16) = True
    decreasing reader.length
:=
  rewrite readGroups.unfold reader at read in
  match b: reader.readBit with
    | None => cases
    | Some (more, afterMore) =>
      match n: afterMore.readNumber 4 with
        | None => cases
        | Some (group, after) =>
          let bitRead := BitReader.readBitSome reader more afterMore b
          let numberRead := BitReader.readNumberSome afterMore 4 group after n
          let fits: group < 16 := omega [numberRead.right]
          match more with
            | True =>
              match d: Nat.decLessThan after.length reader.length with
                | No _ => cases
                | Yes shorter =>
                  match g: readGroups after with
                    | None => cases
                    | Some (gs, others) =>
                      let parts := somePairInjective _ _ _ _ read
                      match readGroupsSome after gs others g [decreasing := shorter] with
                        | Both split (Both some small) =>
                          let first: (group < 16) = True := omega [fits]
                          match gs with
                            | [] => Void.exfalso (some rfl)
                            | [next, ..more] =>
                              rewrite <- parts.left, <- parts.right in
                                Both (rewrite bitRead, numberRead.left, split in rfl) (Both (u => cases) (Bool.andIntro _ _ first small))
            | False =>
              let parts := somePairInjective _ _ _ _ read
              let small: [group].all (x => x < 16) = True := omega [fits]
              rewrite <- parts.left, <- parts.right in Both (rewrite bitRead, numberRead.left in rfl) (Both (u => cases) small)

--| Each operation is read back from its type id.
theorem operationOfTypeId (operation: Operation): operationOf (typeId operation) = Some operation := cases

--| An operation is read only from its type id.
theorem operationOfSome (n: Nat) (operation: Operation) (read: operationOf n = Some operation): n = typeId operation :=
  match n with
    | 0 => rewrite <- Option.someInjective _ _ read in rfl
    | 1 => rewrite <- Option.someInjective _ _ read in rfl
    | 2 => rewrite <- Option.someInjective _ _ read in rfl
    | 3 => rewrite <- Option.someInjective _ _ read in rfl
    | 5 => rewrite <- Option.someInjective _ _ read in rfl
    | 6 => rewrite <- Option.someInjective _ _ read in rfl
    | 7 => rewrite <- Option.someInjective _ _ read in rfl
    | 4 => cases
    | _ => cases
