--| The real puzzle input (aoc/inputs/2021/day06.txt, committed), through
--| `include`: the answers are checked on it when the tests run.
namespace Aoc.Year2021.Day06.Tests
import Aoc.Year2021.Day06 (..)
import Std (Fail, Text)

def inputTimers: Result (List Nat) Text :=
  Fail.toResult (() => parseTimers (include "../../../../../inputs/2021/day06.txt"))

test "real input, part 1" := inputTimers.map solvePart1 == Ok 380243
test "real input, part 2" := inputTimers.map solvePart2 == Ok 1708791884591
