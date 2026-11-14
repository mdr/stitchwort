--| Part 2's rules, field by field: each of the program's checks is the
--| puzzle's rule for that field (Spec/), for every value.

namespace Aoc.Year2020.Day04.Proofs
import Aoc.Year2020.Day04 (..)
import Aoc.Year2020.Day04.Spec (..)
import Std (Bool, Char, DecEq, Eq, List, Nat, Option, Parse, Text, byDecision)

theorem betweenToNat ∀ (low high: Nat) (chars: List Char):
    between low high (Text.toNat (Text.fromList chars))
      = (chars ≠ [] ∧ chars.all Parse.isDigit ∧ low <= number chars <= high) :=
  rewrite Text.toNatDigits chars in cases

theorem andShape [a b c d: Bool]: (a ∧ True ∧ b ∧ c ∧ d) = ((a ∧ b) ∧ c ∧ d) := cases

theorem yearChars ∀ (low high: Nat) (chars: List Char):
    yearBetween low high (Text.fromList chars) = year low high (Text.fromList chars) :=
  match chars with
    | [] => rfl
    | [char, ..rest] => rewrite betweenToNat low high [char, ..rest] in andShape

theorem yearSpec ∀ (low high: Nat) (value: Text): yearBetween low high value = year low high value := match value with
  | MkText chars => yearChars low high chars

theorem andIsSome [a b: Bool] [x: Nat]: (a ∧ Option.isSome (if b then Some x else None)) = (a ∧ b) := cases

theorem passportIdChars ∀ (chars: List Char):
    Key.valid PassportId (Text.fromList chars) = digits 9 (Text.fromList chars) :=
  match chars with
    | [] => rfl
    | [char, ..rest] => rewrite Text.toNatDigits [char, ..rest] in andIsSome

theorem passportIdSpec ∀ (value: Text): Key.valid PassportId value = digits 9 value := match value with
  | MkText chars => passportIdChars chars

theorem hairColorChars ∀ (chars: List Char): hairColorValid (Text.fromList chars) = hairColor (Text.fromList chars) :=
  match chars with
    | ['#', ..digits] => rfl
    | _ => rfl

theorem hairColorSpec ∀ (value: Text): Key.valid HairColor value = hairColor value := match value with
  | MkText chars => hairColorChars chars

--| The seven colours are different, so a value that is one of them is
--| exactly one.
theorem eyeColorSpec ∀ (value: Text): Key.valid EyeColor value = eyeColor value :=
  rewrite List.lengthFilter eyeColors (== value), List.countEqDistinct value eyeColors byDecision in cases

theorem lastIs ∀ (chars unit: List Char):
    (Text.drop (Text.fromList chars) (Text.length (Text.fromList chars) - Text.length (Text.fromList unit))
      == Text.fromList unit)
      = (chars.drop (chars.length - unit.length) == unit) :=
  Text.fromListEq

theorem heightChars ∀ (chars: List Char): heightValid (Text.fromList chars) = height (Text.fromList chars) :=
  rewrite Text.stripSuffixDrop (Text.fromList chars) "cm" in
    match cm: Text.drop (Text.fromList chars) (Text.length (Text.fromList chars) - Text.length "cm") == "cm" with
      | True =>
        let isCm := Eq.trans (Eq.sym (lastIs chars ['c', 'm'])) cm;
        rewrite isCm.read, betweenToNat 150 193 (chars.take (chars.length - 2)) in cases
      | False =>
        rewrite Text.stripSuffixDrop (Text.fromList chars) "in" in
          match inches: Text.drop (Text.fromList chars) (Text.length (Text.fromList chars) - Text.length "in")
            == "in" with
            | True =>
              let isIn := Eq.trans (Eq.sym (lastIs chars ['i', 'n'])) inches;
              rewrite isIn, betweenToNat 59 76 (chars.take (chars.length - 2)) in cases
            | False =>
              rewrite Eq.trans (Eq.sym (lastIs chars ['c', 'm'])) cm,
                  Eq.trans (Eq.sym (lastIs chars ['i', 'n'])) inches in
                cases

theorem heightSpec ∀ (value: Text): Key.valid Height value = height value := match value with
  | MkText chars => heightChars chars

theorem validSpec ∀ (key: Key) (value: Text): key.valid value = validValue key.code value := match key with
  | BirthYear => yearSpec 1920 2002 value
  | IssueYear => yearSpec 2010 2020 value
  | ExpirationYear => yearSpec 2020 2030 value
  | Height => heightSpec value
  | HairColor => hairColorSpec value
  | EyeColor => eyeColorSpec value
  | PassportId => passportIdSpec value
  | CountryId => rfl
