-- The real puzzle input (aoc/inputs/2021/day07.txt, committed), through
-- `include`: the answers are checked on it when the tests run.
namespace Aoc.Year2021.Day07.Tests
import Aoc.Year2021.Day07 (..)
import Std (Fail)

def inputCrabs: List Nat := Fail.orElse [] (() => parseCrabs (include "../../../../../inputs/2021/day07.txt"))

test "real input, part 1" := solvePart1 inputCrabs == 340052
test "real input, part 2" := solvePart2 inputCrabs == 92948968
