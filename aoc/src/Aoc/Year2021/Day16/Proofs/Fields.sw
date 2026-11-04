--| The decoder's pieces that read no packets: a number in a field, a
--| literal's groups, an operator's type id. Each reads exactly the spec's
--| bits for what it gives back.

namespace Aoc.Year2021.Day16.Proofs
import Aoc.Year2021.Day16 (..)
import Aoc.Year2021.Day16.Spec (groupBits, typeId)
import Std (Bool, DecEq, Eq, List, Nat, Option, Pair, Void)

--| `Some` of two pairs: the same parts.
theorem somePairInjective (x1: a) (y1: b) (x2: a) (y2: b) (h: Some (x1, y1) = Some (x2, y2)): x1 = x2 ∧ y1 = y2 :=
  let both := Option.someInjective _ _ h
  Both (Pair.mkInjectiveFst _ _ _ _ both) (Pair.mkInjectiveSnd _ _ _ _ both)

--| A field of the right length is split off.
theorem splitFieldAppend (field: List Bool) (rest: List Bool) (count: Nat) (length: field.length = count): splitField count (field ++ rest) = Some (field, rest) :=
  rewrite List.takeAppendLength field rest count length, List.dropAppendLength field rest count length, length, DecEq.refl count in rfl

--| What `splitField` splits off is a field of the right length.
theorem splitFieldSome (count: Nat) (bits: List Bool) (field: List Bool) (rest: List Bool) (split: splitField count bits = Some (field, rest)):
    bits = field ++ rest ∧ field.length = count :=
  let taken := bits.take count
  let unfolded: (if taken.length == count then Some (taken, bits.drop count) else None) = Some (field, rest) := split
  match e: taken.length == count with
    | True =>
      let parts := somePairInjective _ _ _ _ unfolded
      rewrite <- parts.left, <- parts.right in Both (Eq.sym (List.appendTakeDrop bits count)) (DecEq.sound _ _ e)
    | False => cases

--| A number that fits its field is read back.
theorem readNumberBits (width: Nat) (n: Nat) (rest: List Bool) (small: n < Nat.pow 2 width): readNumber width (Nat.toBits width n ++ rest) = Some (n, rest) :=
  rewrite splitFieldAppend (Nat.toBits width n) rest width (Nat.toBitsLength width n), Nat.fromBitsToBits width n small in rfl

--| What `readNumber` reads is the number's bits, and the number fits.
theorem readNumberSome (width: Nat) (bits: List Bool) (n: Nat) (rest: List Bool) (read: readNumber width bits = Some (n, rest)):
    bits = Nat.toBits width n ++ rest ∧ n < Nat.pow 2 width :=
  match e: splitField width bits with
    | None => cases
    | Some (field, after) =>
      let parts := somePairInjective _ _ _ _ read
      let split := splitFieldSome width bits field after e
      let written := Nat.toBitsFromBits field
      rewrite split.right, parts.left at written in
        Both (rewrite <- parts.right, written in split.left) (rewrite <- parts.left in (rewrite split.right at (Nat.fromBitsBelow field)))

--| A literal's groups, each below 16, are read back from their bits.
theorem readGroupsBits (rest: List Bool): (groups: List Nat) → groups ≠ [] → groups.all (group => group < 16) = True → readGroups (groupBits groups ++ rest) = Some (groups, rest)
  | [], some, small => Void.exfalso (some rfl)
  | [group], some, small => rewrite Nat.fromBitsToBits 4 group (omega [small]) in rfl
  | [group, next, ..more], some, small =>
    let fits: group < 16 := omega [small]
    let others: [next, ..more].all (group => group < 16) = True := Bool.andRight _ _ small
    rewrite readGroupsBits rest [next, ..more] (u => cases) others, Nat.fromBitsToBits 4 group fits in rfl

--| What `readGroups` reads is the spec's bits for the groups it gives,
--| at least one, each below 16.
theorem readGroupsSome: (bits: List Bool) → (groups: List Nat) → (rest: List Bool) → readGroups bits = Some (groups, rest) →
    bits = groupBits groups ++ rest ∧ groups ≠ [] ∧ groups.all (group => group < 16) = True
  | [more, a, b, c, d, ..tail], groups, rest, read =>
    let written: Nat.toBits 4 (Nat.fromBits [a, b, c, d]) = [a, b, c, d] := Nat.toBitsFromBits [a, b, c, d]
    let fits: Nat.fromBits [a, b, c, d] < 16 := Nat.fromBitsBelow [a, b, c, d]
    match more with
      | True =>
        match e: readGroups tail with
          | None => cases
          | Some (gs, after) =>
            let parts := somePairInjective _ _ _ _ read
            match readGroupsSome tail gs after e with
              | Both split (Both some small) =>
                let group := Nat.fromBits [a, b, c, d]
                let first: (group < 16) = True := omega [fits]
                match gs with
                  | [] => Void.exfalso (some rfl)
                  | [next, ..more] =>
                    let regrouped: Nat.toBits 4 group ++ tail = (Nat.toBits 4 group ++ groupBits [next, ..more]) ++ after :=
                      rewrite split in Eq.sym (List.appendAssoc (Nat.toBits 4 group) (groupBits [next, ..more]) after)
                    let same := Eq.trans (Eq.cong (bits => bits ++ tail) (Eq.sym written)) regrouped
                    rewrite <- parts.left, <- parts.right in Both (Eq.cong (bits => [True, ..bits]) same) (Both (u => cases) (Bool.andIntro _ _ first small))
      | False =>
        let parts := somePairInjective _ _ _ _ read
        let group := Nat.fromBits [a, b, c, d]
        let small: [group].all (x => x < 16) = True := omega [fits]
        rewrite <- parts.left, <- parts.right in Both (Eq.cong (bits => [False, ..bits ++ tail]) (Eq.sym written)) (Both (u => cases) small)
  | [], groups, rest, read => cases
  | [_], groups, rest, read => cases
  | [_, _], groups, rest, read => cases
  | [_, _, _], groups, rest, read => cases
  | [_, _, _, _], groups, rest, read => cases

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
