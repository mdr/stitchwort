--| Day 5's specification (Spec/Spec.sw) on the puzzle's examples and the
--| real input.

namespace Aoc.Year2020.Day05.Tests
import Aoc.Year2020.Day05.Spec (..)
import Std (List, Option, Text)

def written (input: Text): List (List Char) := input.lines.map Text.toList

test "example, the spec" := seat "FBFBBFFRLR".toList == Some { row = 44, column = 5 }
test "the other examples, the spec" := seatIds (written """
  BFFFBBFRRR
  FFFBBBFRRR
  BBFFBBFRLL""") == [567, 119, 820]
test "not a pass, the spec" :=
  seat "FBFBBFFRLB".toList == None ∧ seat "FBFBBFFRL".toList == None ∧ seat "FBFBBFFRLRL".toList == None
test "real input, the spec" :=
  (
    part1Answer (written (include "../../../../../inputs/2020/day05.txt")),
    part2Answers (written (include "../../../../../inputs/2020/day05.txt"))
  )
    == (Some 813, [612])
