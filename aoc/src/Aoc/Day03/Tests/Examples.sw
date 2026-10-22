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
test "banks part 1" := (parseBanks example).map (joltage 2) == [98, 89, 78, 92]
test "banks part 2" := (parseBanks example).map (joltage 12) == [987654321111, 811111111119, 434234234278, 888911112111]

test "parse" := Bank.parse "102" == [1, 0, 2]

test "zeros" := Bank.best 2 [0, 0, 5, 0] == [5, 0]
test "leftmost wins" := Bank.best 1 [3, 9, 9, 1] == [9]
test "keep everything" := Bank.best 3 [4, 5, 6] == [4, 5, 6]
test "too short" := Bank.best 5 [1, 2] == [1, 2]
test "pick none" := Bank.best 0 [1, 2, 3] == []
