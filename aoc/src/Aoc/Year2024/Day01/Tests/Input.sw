-- The real puzzle input (aoc/inputs/2024/day01.txt, committed), through
-- `include`: the answers are checked on it when the tests run.
namespace Aoc.Year2024.Day01.Tests
import Aoc.Year2024.Day01 (..)
import Std (Fail, Result, Text)

def inputLists: Result LocationLists Text :=
  Fail.toResult (() => parseLocationLists (include "../../../../../inputs/2024/day01.txt"))

test "real input, part 1" := inputLists.map solvePart1 == Ok 2066446
test "real input, part 2" := inputLists.map solvePart2 == Ok 24931009
