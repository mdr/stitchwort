--| The real puzzle input (aoc/inputs/2021/day08.txt, committed), through
--| `include`: the answers are checked on it when the tests run.
namespace Aoc.Year2021.Day08.Tests
import Aoc.Year2021.Day08 (..)
import Std (Fail, Text)

def inputEntries: Result (List Entry) Text :=
  Fail.toResult (() => parseEntries (include "../../../../../inputs/2021/day08.txt"))

test "real input, part 1" := inputEntries.map solvePart1 == Ok 445
test "real input, part 2" := inputEntries.map solvePart2 == Ok 1043101
