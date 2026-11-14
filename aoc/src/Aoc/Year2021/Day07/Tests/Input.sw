--| The real puzzle input (aoc/inputs/2021/day07.txt, committed), through
--| `include`: the answers are checked on it when the tests run.
namespace Aoc.Year2021.Day07.Tests
import Aoc.Year2021.Day07 (..)
import Std (Fail, Text)

def inputCrabs: Result (List Nat) Text :=
  Fail.toResult (() => parseCrabs (include "../../../../../inputs/2021/day07.txt"))

test "real input, part 1" := inputCrabs.map solvePart1 == Ok 340052
test "real input, part 2" := inputCrabs.map solvePart2 == Ok 92948968
