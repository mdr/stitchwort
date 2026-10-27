-- The real puzzle input (aoc/inputs/2024/day01.txt, committed), through
-- `include`: the answers are checked on it when the tests run.
namespace Aoc.Year2024.Day01.Tests
import Aoc.Year2024.Day01 (..)
import Std (Fail)

def inputLists: LocationLists :=
  Fail.orElse { left = [], right = [] } (() => parseLocationLists (include "../../../../../inputs/2024/day01.txt").lines)

test "real input, part 1" := solvePart1 inputLists == 2066446
test "real input, part 2" := solvePart2 inputLists == 24931009
