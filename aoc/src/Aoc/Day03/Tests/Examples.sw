-- Day 3's tests: the example from the puzzle and unit tests. Kept apart from
-- the program, so `stitchwort run Aoc.Day03.main` doesn't check them.

namespace Aoc.Day03.Tests
import Aoc.Day03 (..)
import Std (Fail, Fin, List, Text)

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

def bankOf (t: Text): Bank := Fail.orElse [] (() => Bank.read t)

test "parse" := (bankOf " 1002 ").map Fin.toNat == [1, 0, 0, 2]
test "a bank that isn't a row of numbers" := banksOf ["123", "1x02"] == Err "line 2: expected a row of digits, got '1x02'"
test "a blank line" := banksOf ["123", ""] == Err "line 2: expected a row of digits, got ''"
test "spaces around a bank" := (banksOf [" 12 ", "3"]).map (bs => bs.map (b => b.map Fin.toNat)) == Ok [[1, 2], [3]]

-- `Bank.best k` of the bank written as `digits`, as numbers.
def bestOf (k: Nat) (digits: Text): List Nat := (Bank.best k (bankOf digits)).map Fin.toNat

test "zeros" := bestOf 2 "0050" == [5, 0]
test "leftmost wins" := bestOf 1 "3991" == [9]
-- The tie between the 7s decides it: the first 7 leaves 573 to choose from, so
-- 77; taking the last 7 would give 73.
test "leftmost largest wins" := bestOf 2 "27573" == [7, 7]
test "keep everything" := bestOf 3 "456" == [4, 5, 6]
test "too short" := bestOf 5 "12" == [1, 2]
test "pick none" := bestOf 0 "123" == []
