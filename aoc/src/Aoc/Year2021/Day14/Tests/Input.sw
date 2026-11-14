--| The real puzzle input (aoc/inputs/2021/day14.txt, committed), through
--| `include`: the answers are checked on it when the tests run.
namespace Aoc.Year2021.Day14.Tests
import Aoc.Year2021.Day14 (..)
import Std (Fail, Text)

def inputManual: Result Manual Text :=
  Fail.toResult (() => parseManual (include "../../../../../inputs/2021/day14.txt"))

test "real input, part 1" := inputManual.map solvePart1 == Ok 2712
test "real input, part 2" := inputManual.map solvePart2 == Ok 8336623059567
