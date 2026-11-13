--| Day 4 proved: both of the program's checks are the puzzle's (Spec/), for
--| every passport, so both answers are the puzzle's for every list of
--| passports. Field by field in Rules.sw.

namespace Aoc.Year2020.Day04.Proofs
import Aoc.Year2020.Day04 (..)
import Aoc.Year2020.Day04.Spec (..)
import Std (Bool, DecEq, Eq, Finite, List, NonEmptyList, Text)

--| No two keys are written alike.
theorem codeEq ∀ (a: Key) (b: Key): (a.code == b.code) = (a == b) :=
  DecEq.sound (Finite.check (((x, y)) => (x.code == y.code) == (x == y)) rfl (a, b))

theorem writtenHas ∀ (passport: Passport) (key: Key): (pairs passport).any (((written, _)) => written == key.code) = passport.has key :=
  Eq.trans (List.anyMap passport.fields.toList (((written, _)) => written == key.code) (field => (field.key.code, field.value)))
    (List.anyCong passport.fields.toList _ _ (field => codeEq field.key key))

theorem missingHas ∀ (passport: Passport): missing passport = (keys.filter (key => not (passport.has key))).map Key.code :=
  Eq.trans (List.filterOfMap keys (key => not ((pairs passport).any (((written, _)) => written == key))) Key.code)
    (Eq.cong (chosen => List.map chosen Key.code) (List.filterCongMem keys _ _ (key m => Eq.cong not (writtenHas passport key))))

--| "All eight fields, or all but cid" is having the seven others.
theorem allButCid ∀ (has: Key → Bool):
    required.all has = ((keys.filter (key => not (has key))).map Key.code == [] ∨ (keys.filter (key => not (has key))).map Key.code == ["cid"]) :=
  cases

theorem hasRequiredSpec ∀ (passport: Passport): passport.hasRequired = validPart1 passport :=
  rewrite missingHas passport in allButCid passport.has

theorem part1Correct ∀ (passports: List Passport): solvePart1 passports = part1Answer passports :=
  rewrite List.lengthFilter passports validPart1 in List.countCongMem _ _ _ (passport m => hasRequiredSpec passport)

theorem valuesValidSpec ∀ (passport: Passport): passport.valuesValid = (pairs passport).all (((key, value)) => validValue key value) :=
  Eq.sym (Eq.trans (List.allMapBool passport.fields.toList (((key, value)) => validValue key value) (field => (field.key.code, field.value)))
    (List.allCong passport.fields.toList _ _ (field => Eq.sym (validSpec field.key field.value))))

theorem part2Correct ∀ (passports: List Passport): solvePart2 passports = part2Answer passports :=
  rewrite List.lengthFilter passports validPart2 in
    List.countCongMem _ _ _ (passport m => rewrite hasRequiredSpec passport, valuesValidSpec passport in rfl)
