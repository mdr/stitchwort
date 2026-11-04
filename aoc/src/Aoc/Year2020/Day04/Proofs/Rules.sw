--| Part 2's rules, field by field: each of the program's checks is the
--| puzzle's rule for that field (Spec/), for every value.

namespace Aoc.Year2020.Day04.Proofs
import Aoc.Year2020.Day04 (..)
import Aoc.Year2020.Day04.Spec (..)
import Std (Bool, Char, DecEq, Eq, List, Nat, Option, Parse, Text, Void)

theorem readDigitsAll: (acc: Nat) → (chars: List Char) →
    Text.readDigits acc chars = (if chars.all Parse.isDigit then Some (List.foldLeft (chars.map (digit => digit.digitValue.getOrElse 0)) acc (acc digit => acc * 10 + digit)) else None)
  | acc, [] => rfl
  | acc, [char, ..rest] =>
    match value: char.digitValue with
      | None => rfl
      | Some d => readDigitsAll (acc * 10 + d) rest

theorem toNatDigits (chars: List Char):
    Text.toNat (Text.fromList chars) = (if chars ≠ [] ∧ chars.all Parse.isDigit then Some (Parse.digitsValue chars) else None) :=
  match chars with
    | [] => rfl
    | [char, ..rest] => readDigitsAll 0 [char, ..rest]

theorem betweenToNat (low: Nat) (high: Nat) (chars: List Char):
    between low high (Text.toNat (Text.fromList chars)) = (chars ≠ [] ∧ chars.all Parse.isDigit ∧ low <= number chars ∧ number chars <= high) :=
  rewrite toNatDigits chars in cases

theorem andShape (a: Bool) (b: Bool) (c: Bool) (d: Bool): (a ∧ True ∧ b ∧ c ∧ d) = ((a ∧ b) ∧ c ∧ d) := cases

theorem yearChars (low: Nat) (high: Nat): (chars: List Char) → yearBetween low high (Text.fromList chars) = year low high (Text.fromList chars)
  | [] => rfl
  | [char, ..rest] => rewrite betweenToNat low high [char, ..rest] in andShape _ _ _ _

theorem yearSpec (low: Nat) (high: Nat) (value: Text): yearBetween low high value = year low high value :=
  match value with
    | MkText chars => yearChars low high chars

theorem andIsSome (a: Bool) (b: Bool) (x: Nat): (a ∧ Option.isSome (if b then Some x else None)) = (a ∧ b) := cases

theorem passportIdChars: (chars: List Char) → Key.valid PassportId (Text.fromList chars) = digits 9 (Text.fromList chars)
  | [] => rfl
  | [char, ..rest] => rewrite toNatDigits [char, ..rest] in andIsSome _ _ _

theorem passportIdSpec (value: Text): Key.valid PassportId value = digits 9 value :=
  match value with
    | MkText chars => passportIdChars chars

theorem hairColorChars: (chars: List Char) → hairColorValid (Text.fromList chars) = hairColor (Text.fromList chars)
  | ['#', ..digits] => rfl
  | _ => rfl

theorem hairColorSpec (value: Text): Key.valid HairColor value = hairColor value :=
  match value with
    | MkText chars => hairColorChars chars

--| The seven colours are different, so a value that is one of them is
--| exactly one.
theorem eyeColorSpec (value: Text): Key.valid EyeColor value = eyeColor value :=
  match amb: "amb" == value with
    | True => rewrite <- DecEq.sound "amb" value amb in rfl
    | False =>
      match blu: "blu" == value with
        | True => rewrite <- DecEq.sound "blu" value blu in rfl
        | False =>
          match brn: "brn" == value with
            | True => rewrite <- DecEq.sound "brn" value brn in rfl
            | False =>
              match gry: "gry" == value with
                | True => rewrite <- DecEq.sound "gry" value gry in rfl
                | False =>
                  match grn: "grn" == value with
                    | True => rewrite <- DecEq.sound "grn" value grn in rfl
                    | False =>
                      match hzl: "hzl" == value with
                        | True => rewrite <- DecEq.sound "hzl" value hzl in rfl
                        | False =>
                          match oth: "oth" == value with
                            | True => rfl
                            | False => rfl

--| `stripSuffix` compares characters by `sameChar`, the spec by `==`.
theorem sameCharEq (c: Char) (d: Char): Text.sameChar c d = (c == d) :=
  match same: Text.sameChar c d with
    | True => rewrite Char.ext c d (Nat.equalSound _ _ same) in Eq.sym (DecEq.refl d)
    | False =>
      match equal: c == d with
        | True => Void.exfalso (Bool.falseNotTrue (rewrite DecEq.sound c d equal, Text.sameCharRefl d at same in Eq.sym same))
        | False => rfl

theorem pairEq (x: Char) (y: Char) (f: Char) (s: Char): ([x, y] == [f, s]) = (f == x ∧ s == y) :=
  match first: f == x with
    | True =>
      rewrite DecEq.sound f x first in
        match second: s == y with
          | True => rewrite DecEq.sound s y second in DecEq.refl [x, y]
          | False =>
            match equal: [x, y] == [x, s] with
              | True => Void.exfalso (DecEq.soundFalse s y second (Eq.sym (Eq.cong (list => (list.get 1).getOrElse y) (DecEq.sound _ _ equal))))
              | False => rfl
    | False =>
      match equal: [x, y] == [f, s] with
        | True => Void.exfalso (DecEq.soundFalse f x first (Eq.sym (Eq.cong (list => (list.get 0).getOrElse x) (DecEq.sound _ _ equal))))
        | False => rfl

theorem reverseTwo (y: Char) (x: Char) (rest: List Char): List.reverse [y, x, ..rest] = List.reverse rest ++ [x, y] :=
  List.reverseOntoAppend rest [x, y]

theorem dropTwo (front: List Char) (x: Char) (y: Char): (front ++ [x, y]).drop ((front ++ [x, y]).length - 2) = [x, y] :=
  List.dropAppendLength front [x, y] _ (rewrite List.lengthAppend front [x, y] in omega)

theorem takeTwo (front: List Char) (x: Char) (y: Char): (front ++ [x, y]).take ((front ++ [x, y]).length - 2) = front :=
  List.takeAppendLength front [x, y] _ (rewrite List.lengthAppend front [x, y] in omega)

theorem stripSuffixReversed (first: Char) (second: Char): (back: List Char) →
    Text.stripSuffix (Text.fromList back.reverse) (Text.fromList [first, second])
      = (if back.reverse.drop (back.reverse.length - 2) == [first, second] then Some (Text.fromList (back.reverse.take (back.reverse.length - 2))) else None)
  | [] => rfl
  | [y] => cases
  | [y, x, ..rest] =>
    rewrite List.reverseReverse [y, x, ..rest], reverseTwo y x rest, dropTwo (List.reverse rest) x y, takeTwo (List.reverse rest) x y,
      pairEq x y first second, sameCharEq second y, sameCharEq first x in cases

theorem stripSuffixTwo (first: Char) (second: Char) (chars: List Char):
    Text.stripSuffix (Text.fromList chars) (Text.fromList [first, second])
      = (if chars.drop (chars.length - 2) == [first, second] then Some (Text.fromList (chars.take (chars.length - 2))) else None) :=
  let reversed := stripSuffixReversed first second chars.reverse
  rewrite List.reverseReverse chars at reversed in reversed

theorem heightChars (chars: List Char): heightValid (Text.fromList chars) = height (Text.fromList chars) :=
  rewrite stripSuffixTwo 'c' 'm' chars in
    match cm: chars.drop (chars.length - 2) == ['c', 'm'] with
      | True => rewrite DecEq.sound _ _ cm, betweenToNat 150 193 (chars.take (chars.length - 2)) in cases
      | False =>
        rewrite stripSuffixTwo 'i' 'n' chars in
        match inches: chars.drop (chars.length - 2) == ['i', 'n'] with
          | True => rewrite betweenToNat 59 76 (chars.take (chars.length - 2)) in cases
          | False => cases

theorem heightSpec (value: Text): Key.valid Height value = height value :=
  match value with
    | MkText chars => heightChars chars

theorem validSpec (key: Key) (value: Text): key.valid value = validValue key.code value :=
  match key with
    | BirthYear => yearSpec 1920 2002 value
    | IssueYear => yearSpec 2010 2020 value
    | ExpirationYear => yearSpec 2020 2030 value
    | Height => heightSpec value
    | HairColor => hairColorSpec value
    | EyeColor => eyeColorSpec value
    | PassportId => passportIdSpec value
    | CountryId => rfl
