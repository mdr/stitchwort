-- The real puzzle input (aoc/inputs/2021/day11.txt, committed), through
-- `include`: the answers are checked on it when the tests run.
namespace Aoc.Year2021.Day11.Tests
import Aoc.Year2021.Day11 (..)
import Std (Fail, List)

def inputLevels: List (List Nat) := Fail.orElse [] (() => parseLevels (include "../../../../../inputs/2021/day11.txt"))

test "real input, part 1" := solvePart1 inputLevels == 1773
test "real input, part 2" := solvePart2 inputLevels == Some 494
