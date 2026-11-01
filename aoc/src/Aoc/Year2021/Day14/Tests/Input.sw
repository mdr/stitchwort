-- The real puzzle input (aoc/inputs/2021/day14.txt, committed), through
-- `include`: the answers are checked on it when the tests run.
namespace Aoc.Year2021.Day14.Tests
import Aoc.Year2021.Day14 (..)
import Std (Fail)

def inputManual: Manual := Fail.orElse { template = [], rules = [] } (() => parseManual (include "../../../../../inputs/2021/day14.txt"))

test "real input, part 1" := solvePart1 inputManual == 2712
test "real input, part 2" := solvePart2 inputManual == 8336623059567
