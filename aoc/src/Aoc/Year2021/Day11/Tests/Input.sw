--| The real puzzle input (aoc/inputs/2021/day11.txt, committed), through
--| `include`: the answers are checked on it when the tests run.
namespace Aoc.Year2021.Day11.Tests
import Aoc.Year2021.Day11 (..)
import Std (Fail, Text)

def inputCavern: Result Cavern Text :=
  Fail.toResult (() => parseCavern (include "../../../../../inputs/2021/day11.txt"))

test "real input, part 1" := inputCavern.map Cavern.solvePart1 == Ok 1773
test "real input, part 2" := inputCavern.map Cavern.solvePart2 == Ok (Some 494)
