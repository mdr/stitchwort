-- Day 3's tests: the example from the puzzle and unit tests. Kept apart from
-- the program, so `stitchwort run Aoc.Day03.main` doesn't check them.

namespace Aoc.Day03.Tests
import Aoc.Day03 (..)
import Std (List, Text)

def example: List Text := """
  987654321111111
  811111111111119
  234234234234278
  818181911112111
  """.lines

test "example" := (solvePart1 (parseBanks example), solvePart2 (parseBanks example)) == (357, 3121910778619)
test "banks part 1" := (parseBanks example).map (maxJoltage 2) == [98, 89, 78, 92]
test "banks part 2" := (parseBanks example).map (maxJoltage 12) == [987654321111, 811111111119, 434234234278, 888911112111]

test "parse" := Bank.parse "1x02" == [1, 0, 2]

-- A bank's digits are written as numerals: each is checked to be a `Fin 10`.
test "zeros" := Bank.best 2 [0, 0, 5, 0] == [5, 0]
test "leftmost wins" := Bank.best 1 [3, 9, 9, 1] == [9]
-- The tie between the 7s decides it: the first 7 leaves 573 to choose from, so
-- 77; taking the last 7 would give 73.
test "leftmost largest wins" := Bank.best 2 [2, 7, 5, 7, 3] == [7, 7]
test "keep everything" := Bank.best 3 [4, 5, 6] == [4, 5, 6]
test "too short" := Bank.best 5 [1, 2] == [1, 2]
test "pick none" := Bank.best 0 [1, 2, 3] == []
test "joltage" := maxJoltage 2 [2, 7, 5, 7, 3] == 77

-- The same, checked when the file is: the answer computes.
theorem leftmostLargest: maxJoltage 2 [2, 7, 5, 7, 3] = 77 := rfl
