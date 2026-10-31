-- The real puzzle input (aoc/inputs/2021/day05.txt, committed), through
-- `include`: the answers are checked on it when the tests run.
namespace Aoc.Year2021.Day05.Tests
import Aoc.Year2021.Day05 (..)
import Std (Fail)

def inputLines: List Line := Fail.orElse [] (() => parseLines (include "../../../../../inputs/2021/day05.txt"))

test "real input, part 1" := solvePart1 inputLines == 8060
test "real input, part 2" := solvePart2 inputLines == 21577
