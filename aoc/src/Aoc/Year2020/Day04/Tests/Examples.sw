--| Day 4's tests: the examples from the puzzle and unit tests.
--
-- Kept apart from the program, so `stitchwort run Aoc.Year2020.Day04.main`
-- doesn't check them.

namespace Aoc.Year2020.Day04.Tests
import Aoc.Year2020.Day04 (..)
import Std (Fail, List, Result, Text)

def example: Text := """
  ecl:gry pid:860033327 eyr:2020 hcl:#fffffd
  byr:1937 iyr:2017 cid:147 hgt:183cm

  iyr:2013 ecl:amb cid:350 eyr:2023 pid:028048884
  hcl:#cfa07d byr:1929

  hcl:#ae17e1 iyr:2013
  eyr:2024
  ecl:brn pid:760753108 byr:1931
  hgt:179cm

  hcl:#cfa07d eyr:2025 pid:166559648
  iyr:2011 ecl:brn hgt:59in
  """

--| Part 2's four invalid passports.
def invalidExample: Text := """
  eyr:1972 cid:100
  hcl:#18171d ecl:amb hgt:170 pid:186cm iyr:2018 byr:1926

  iyr:2019
  hcl:#602927 eyr:1967 hgt:170cm
  ecl:grn pid:012533040 byr:1946

  hcl:dab227 iyr:2012
  ecl:brn hgt:182cm pid:021572410 eyr:2020 byr:1992 cid:277

  hgt:59cm ecl:zzz
  eyr:2038 hcl:74454a iyr:2023
  pid:3556412378 byr:2007
  """

--| Part 2's four valid passports.
def validExample: Text := """
  pid:087499704 hgt:74in ecl:grn iyr:2012 eyr:2030 byr:1980
  hcl:#623a2f

  eyr:2029 ecl:blu cid:129 byr:1989
  iyr:2014 pid:896056539 hcl:#a97842 hgt:165cm

  hcl:#888785
  hgt:164cm byr:2001 iyr:2015 cid:88
  pid:545766238 ecl:hzl
  eyr:2022

  iyr:2010 hgt:158cm hcl:#b6652a ecl:blu byr:1944 eyr:2021 pid:093154719
  """

def parsed (input: Text): Result (List Passport) Text := Fail.toResult (() => parsePassports input)

def exampleAnswers (input: Text): Result (Nat, Nat) Text :=
  (parsed input).map (passports => (solvePart1 passports, solvePart2 passports))

test "example" := exampleAnswers example == Ok (2, 2)
test "example, passport by passport" :=
  (parsed example).map (.map Passport.hasRequired) == Ok [True, False, True, False]
test "part 2, the invalid passports" := exampleAnswers invalidExample == Ok (4, 0)
test "part 2, the valid passports" := exampleAnswers validExample == Ok (4, 4)

test "a passport parsed" := parsed """
  hcl:#ae17e1 iyr:2013
  eyr:2024"""
  == Ok [
    {
      fields = [
        { key = HairColor, value = "#ae17e1" },
        { key = IssueYear, value = "2013" },
        { key = ExpirationYear, value = "2024" }
      ]
    }
  ]
test "line breaks at the end" := (parsed "cid:1\n\ncid:2\n").map List.length == Ok 2
test "an unknown key" :=
  parsed "byr:1937 abc:1"
    == Err "line 1, column 10: expected 'byr', 'iyr', 'eyr', 'hgt', 'hcl', 'ecl', 'pid' or 'cid', got 'abc'"
test "an empty value" := parsed "byr: iyr:2017" == Err "line 1, column 5: expected a value, got ' '"
-- The extra blank line is line 3, where the next passport should start.
test "two blank lines" :=
  parsed "cid:1\n\n\ncid:2"
    == Err
        "line 3, column 1: expected 'byr', 'iyr', 'eyr', 'hgt', 'hcl', 'ecl', 'pid' or 'cid', got the end of the line"

test "byr" := Key.valid BirthYear "2002" ∧ not (Key.valid BirthYear "2003")
test "hgt" :=
  Key.valid Height "60in" ∧ Key.valid Height "190cm" ∧ not (Key.valid Height "190in") ∧ not (Key.valid Height "190")
test "hcl" := Key.valid HairColor "#123abc" ∧ not (Key.valid HairColor "#123abz") ∧ not (Key.valid HairColor "123abc")
test "ecl" := Key.valid EyeColor "brn" ∧ not (Key.valid EyeColor "wat")
test "pid" := Key.valid PassportId "000000001" ∧ not (Key.valid PassportId "0123456789")

test "years have four digits" :=
  not (Key.valid BirthYear "01990")
    ∧ not (Key.valid BirthYear "+990")
    ∧ Key.valid IssueYear "2010"
    ∧ not (Key.valid IssueYear "2021")
test "a height needs a number" :=
  not (Key.valid Height "cm")
    ∧ not (Key.valid Height "+60in")
    ∧ Key.valid Height "059in"
    ∧ not (Key.valid Height "60 in")
test "hcl, six characters exactly" :=
  not (Key.valid HairColor "#123ab") ∧ not (Key.valid HairColor "#123abcd") ∧ not (Key.valid HairColor "#123ABC")
test "pid, nine digits with leading zeros" :=
  Key.valid PassportId "000000000" ∧ not (Key.valid PassportId "00000000a") ∧ not (Key.valid PassportId "00000000")
test "cid, anything" := Key.valid CountryId "x"
