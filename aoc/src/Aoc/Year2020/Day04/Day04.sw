--| Advent of Code 2020, day 4: a batch file of passports, each a run of
--| `key:value` fields separated by spaces or line breaks, with a blank line
--| between passports. Part 1 counts the passports that have the seven
--| required fields (`cid` may be missing); part 2 those whose fields also
--| hold valid values, by a rule for each field.
--|
--|   $ cd aoc && stitchwort run Aoc.Year2020.Day04.main < inputs/2020/day04.txt
--|
--| The proofs, that the parser reads the puzzle's format and that both
--| checks are the puzzle's, field by field, are in `Aoc.Year2020.Day04.Proofs`
--| (Proofs/), and the tests in `Aoc.Year2020.Day04.Tests` (Tests/); `run`
--| checks neither.

namespace Aoc.Year2020.Day04
import Std (Char, Fail, IO, List, NonEmptyList, Option, Parse, Text)

def main(): {IO, Fail} () :=
  let passports := parsePassports IO.readAll()
  IO.print "Part 1: ${solvePart1 passports}"
  IO.print "Part 2: ${solvePart2 passports}"

type Key =
  | BirthYear
  | IssueYear
  | ExpirationYear
  | Height
  | HairColor
  | EyeColor
  | PassportId
  | CountryId

def Key.code: Key → Text
  | BirthYear => "byr"
  | IssueYear => "iyr"
  | ExpirationYear => "eyr"
  | Height => "hgt"
  | HairColor => "hcl"
  | EyeColor => "ecl"
  | PassportId => "pid"
  | CountryId => "cid"

def keys: List Key := [BirthYear, IssueYear, ExpirationYear, Height, HairColor, EyeColor, PassportId, CountryId]

type Field = { key: Key, value: Text }

type Passport = { fields: NonEmptyList Field }

def isValueChar (char: Char): Bool := not char.isWhitespace

def field(): {Parse} Field :=
  let key := Parse.pick (keys.map (key => (key.code, key)))
  Parse.char ':'
  let value := Parse.takeWhile1 "a value" isValueChar
  { key, value }

def fieldBreak(): {Parse} () := Parse.oneOf [() => Parse.char ' ', Parse.newline]

def passport(): {Parse} Passport :=
  let fields := Parse.sepBy1 field fieldBreak
  { fields }

def parsePassports (input: Text): {Fail} List Passport := Parse.all input (() => Parse.sections passport |> .toList)

def Passport.has (passport: Passport) (key: Key): Bool := passport.fields.any (.key == key)

def required: List Key := [BirthYear, IssueYear, ExpirationYear, Height, HairColor, EyeColor, PassportId]

def Passport.hasRequired (passport: Passport): Bool := required.all passport.has

def between (low: Nat) (high: Nat): Option Nat → Bool
  | Some n => low <= n <= high
  | None => False

def yearBetween (low: Nat) (high: Nat) (value: Text): Bool := value.length == 4 ∧ between low high value.toNat

def heightValid (value: Text): Bool := match value.stripSuffix "cm" with
  | Some number => between (low := 150) (high := 193) number.toNat
  | None =>
    match value.stripSuffix "in" with
      | Some number => between (low := 59) (high := 76) number.toNat
      | None => False

def isHexDigit (char: Char): Bool := char.isAsciiDigit ∨ ('a' <= char <= 'f')

def hairColorValid (value: Text): Bool :=
  value.toList |> matches | ['#', ..digits] => digits.length == 6 ∧ digits.all isHexDigit

def eyeColors: List Text := ["amb", "blu", "brn", "gry", "grn", "hzl", "oth"]

def Key.valid (key: Key) (value: Text): Bool := match key with
  | BirthYear => yearBetween (low := 1920) (high := 2002) value
  | IssueYear => yearBetween (low := 2010) (high := 2020) value
  | ExpirationYear => yearBetween (low := 2020) (high := 2030) value
  | Height => heightValid value
  | HairColor => hairColorValid value
  | EyeColor => eyeColors.contains value
  | PassportId => value.length == 9 ∧ value.toNat.isSome
  | CountryId => True

def Passport.valuesValid (passport: Passport): Bool := passport.fields.all (field => field.key.valid field.value)

def solvePart1 (passports: List Passport): Nat := passports.count Passport.hasRequired

def solvePart2 (passports: List Passport): Nat := passports.count (passport => passport.hasRequired ∧ passport.valuesValid)
