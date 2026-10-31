-- The real puzzle input (aoc/inputs/2021/day01.txt, committed), through
-- `include`: the answers are checked on it when the tests run.
namespace Aoc.Year2021.Day01.Tests
import Aoc.Year2021.Day01 (..)
import Std (Fail)

def inputDepths: List Nat := Fail.orElse [] (() => parseDepths (include "../../../../../inputs/2021/day01.txt"))

test "real input, part 1" := solvePart1 inputDepths == 1616
test "real input, part 2" := solvePart2 inputDepths == 1645
