-- The real puzzle input (aoc-2024/inputs/day01.txt, committed), through
-- `include`: the answers are checked on it when the tests run.
namespace Aoc.Day01.Tests
import Aoc.Day01 (..)
import Std (Fail)

def inputLists: LocationLists :=
  Fail.orElse { left = [], right = [] } (() => parseLocationLists (include "../../../../inputs/day01.txt").lines)

test "real input, part 1" := solvePart1 inputLists == 2066446
test "real input, part 2" := solvePart2 inputLists == 24931009
