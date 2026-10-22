-- Day 3's tests: the example from the puzzle and unit tests. Kept apart from
-- the program, so `stitchwort run Aoc.Day03.main` doesn't check them.

namespace Aoc.Day03.Tests
import Aoc.Day03 (..)
import Std (Fin, List, Text)

def example: List Text := """
  987654321111111
  811111111111119
  234234234234278
  818181911112111
  """.lines

test "example" := (solvePart1 (parseBanks example), solvePart2 (parseBanks example)) == (357, 3121910778619)
test "banks part 1" := (parseBanks example).map (joltage 2) == [98, 89, 78, 92]
test "banks part 2" := (parseBanks example).map (joltage 12) == [987654321111, 811111111119, 434234234278, 888911112111]

test "parse" := (Bank.parse "1x02").map Fin.toNat == [1, 0, 2]

-- `Bank.best k` of the bank written as `digits`, as numbers.
def bestOf (k: Nat) (digits: Text): List Nat := (Bank.best k (Bank.parse digits)).map Fin.toNat

test "zeros" := bestOf 2 "0050" == [5, 0]
test "leftmost wins" := bestOf 1 "3991" == [9]
-- The tie between the 7s decides it: the first 7 leaves 573 to choose from, so
-- 77; taking the last 7 would give 73.
test "leftmost largest wins" := bestOf 2 "27573" == [7, 7]
test "keep everything" := bestOf 3 "456" == [4, 5, 6]
test "too short" := bestOf 5 "12" == [1, 2]
test "pick none" := bestOf 0 "123" == []
