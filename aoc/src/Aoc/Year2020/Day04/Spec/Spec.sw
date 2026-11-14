--| Day 4 as the puzzle states it, about the fields as the batch file writes
--| them: each key by its three letters. The proofs (Proofs/) show the
--| program's checks and counts are these.

namespace Aoc.Year2020.Day04.Spec
import Aoc.Year2020.Day04 (Passport)
import Std (List, Parse, Text)

--| "Each passport is represented as a sequence of key:value pairs".
def pairs (passport: Passport): List (Text, Text) := passport.fields.toList.map (field => (field.key.code, field.value))

--| The expected fields: "byr (Birth Year), iyr (Issue Year), eyr
--| (Expiration Year), hgt (Height), hcl (Hair Color), ecl (Eye Color), pid
--| (Passport ID), cid (Country ID)".
def expected: List Text := ["byr", "iyr", "eyr", "hgt", "hcl", "ecl", "pid", "cid"]

def missing (passport: Passport): List Text :=
  expected.filter (key => not ((pairs passport).any ((written, _) => written == key)))

--| "Passports … with all eight fields are valid", and "treat cid as
--| optional": a passport whose only missing field is cid is valid too.
def validPart1 (passport: Passport): Bool := missing passport == [] ∨ missing passport == ["cid"]

--| "Count the number of valid passports."
def part1Answer (passports: List Passport): Nat := (passports.filter validPart1).length

def number (digits: List Char): Nat := Parse.digitsValue digits

--| "`count` digits", 0 to 9.
def digits (count: Nat) (value: Text): Bool := value.toList.length == count ∧ value.toList.all Parse.isDigit

--| "Four digits; at least `low` and at most `high`."
def year (low high: Nat) (value: Text): Bool := digits 4 value ∧ low <= number value.toList <= high

--| "A number followed by either cm or in: If cm, the number must be at
--| least 150 and at most 193. If in, the number must be at least 59 and at
--| most 76."
def height (value: Text): Bool :=
  let chars := value.toList
  let split := chars.length - 2
  let amount := chars.take split
  let unit := chars.drop split
  let isNumber := amount ≠ [] ∧ amount.all Parse.isDigit
  let n := number amount
  isNumber ∧ ((unit == ['c', 'm'] ∧ 150 <= n <= 193) ∨ (unit == ['i', 'n'] ∧ 59 <= n <= 76))

--| "A # followed by exactly six characters 0-9 or a-f."
def hairColor (value: Text): Bool :=
  value.toList
    |> matches | ['#', ..rest] => rest.length == 6 ∧ rest.all (char => Parse.isDigit char ∨ ('a' <= char <= 'f'))

--| "Exactly one of: amb blu brn gry grn hzl oth."
def eyeColor (value: Text): Bool := (["amb", "blu", "brn", "gry", "grn", "hzl", "oth"].filter (== value)).length == 1

--| "cid (Country ID) - ignored, missing or not."
def validValue (key value: Text): Bool :=
  if key == "byr" then year 1920 2002 value
  else if key == "iyr" then year 2010 2020 value
  else if key == "eyr" then year 2020 2030 value
  else if key == "hgt" then height value
  else if key == "hcl" then hairColor value
  else if key == "ecl" then eyeColor value
  else if key == "pid" then digits 9 value
  else True

--| "Count the number of valid passports - those that have all required
--| fields and valid values."
def validPart2 (passport: Passport): Bool :=
  validPart1 passport ∧ (pairs passport).all ((key, value) => validValue key value)

def part2Answer (passports: List Passport): Nat := (passports.filter validPart2).length
