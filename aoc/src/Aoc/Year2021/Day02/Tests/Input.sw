--| The real puzzle input (aoc/inputs/2021/day02.txt, committed), through
--| `include`: the answers are checked on it when the tests run.
namespace Aoc.Year2021.Day02.Tests
import Aoc.Year2021.Day02 (..)
import Std (Fail, Text)

def inputCommands: Result (List Command) Text :=
  Fail.toResult (() => parseCommands (include "../../../../../inputs/2021/day02.txt"))

test "real input, part 1" := inputCommands.map solvePart1 == Ok 1635930
test "real input, part 2" := inputCommands.map solvePart2 == Ok 1781819478
