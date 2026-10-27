-- Day 3's tests: the example from the puzzle and unit tests. Kept apart from
-- the program, so `stitchwort run Aoc.Year2025.Day03.main` doesn't check them.

namespace Aoc.Year2025.Day03.Tests
import Aoc.Year2025.Day03 (..)
import Std (Fail, List, Text)

def example: List Text := """
  987654321111111
  811111111111119
  234234234234278
  818181911112111
  """.lines

def banksOf (lines: List Text): Result (List Bank) Text := Fail.toResult (() => parseBanks lines)

def exampleBanks: List Bank := Fail.orElse [] (() => parseBanks example)

test "example" := (solvePart1 exampleBanks, solvePart2 exampleBanks) == (357, 3121910778619)
test "banks part 1" := exampleBanks.map (maxJoltage 2) == [98, 89, 78, 92]
test "banks part 2" := exampleBanks.map (maxJoltage 12) == [987654321111, 811111111119, 434234234278, 888911112111]

test "parseOption" := banksOf [" 100200300400 "] == Ok [[1, 0, 0, 2, 0, 0, 3, 0, 0, 4, 0, 0]]
test "a bank that isn't a row of numbers" := banksOf ["123456789012", "1234567x9012"] == Err "line 2: expected a row of digits, got '1234567x9012'"
test "a blank line" := banksOf ["123456789012", ""] == Err "line 2: expected a row of digits, got ''"
test "spaces around a bank" := banksOf [" 123456789012 ", "987654321098"] == Ok [[1, 2, 3, 4, 5, 6, 7, 8, 9, 0, 1, 2], [9, 8, 7, 6, 5, 4, 3, 2, 1, 0, 9, 8]]
test "a bank of exactly 12" := (banksOf ["111111111111"]).map (bs => bs.map List.length) == Ok [12]
test "a bank shorter than 12" := banksOf ["123"] == Err "line 1: expected at least 12 batteries, got 3"
test "one short bank among good ones" := banksOf ["123456789012", "12345678901", "123456789012"] == Err "line 2: expected at least 12 batteries, got 11"
test "a short bank is still a row of digits first" := banksOf ["12x"] == Err "line 1: expected a row of digits, got '12x'"

test "zeros" := Bank.best [0, 0, 5, 0] 2 == [5, 0]
test "leftmost wins" := Bank.best [3, 9, 9, 1] 1 == [9]
-- The tie between the 7s decides it: the first 7 leaves 573 to choose from, so
-- 77; taking the last 7 would give 73.
test "leftmost largest wins" := Bank.best [2, 7, 5, 7, 3] 2 == [7, 7]
test "keep everything" := Bank.best [4, 5, 6] 3 == [4, 5, 6]
test "too short" := Bank.best [1, 2] 5 == [1, 2]
test "pick none" := Bank.best [1, 2, 3] 0 == []

-- The same tie, checked when the file is checked.
theorem leftmostLargest: maxJoltage 2 [2, 7, 5, 7, 3] = 77 := rfl
