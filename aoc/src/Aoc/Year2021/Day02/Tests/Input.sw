-- The real puzzle input (aoc/inputs/2021/day02.txt, committed), through
-- `include`: the answers are checked on it when the tests run.
namespace Aoc.Year2021.Day02.Tests
import Aoc.Year2021.Day02 (..)
import Std (Fail)

def inputCommands: List Command := Fail.orElse [] (() => parseCommands (include "../../../../../inputs/2021/day02.txt"))

test "real input, part 1" := solvePart1 inputCommands == 1635930
test "real input, part 2" := solvePart2 inputCommands == 1781819478
