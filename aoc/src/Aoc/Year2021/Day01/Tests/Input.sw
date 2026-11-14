--| The real puzzle input (aoc/inputs/2021/day01.txt, committed), through
--| `include`: the answers are checked on it when the tests run.
namespace Aoc.Year2021.Day01.Tests
import Aoc.Year2021.Day01 (..)
import Std (Fail, Text)

def inputDepths: Result (List Nat) Text :=
  Fail.toResult (() => parseDepths (include "../../../../../inputs/2021/day01.txt"))

test "real input, part 1" := inputDepths.map solvePart1 == Ok 1616
test "real input, part 2" := inputDepths.map solvePart2 == Ok 1645
