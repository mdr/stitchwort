-- The real puzzle input (aoc/inputs/2021/day06.txt, committed), through
-- `include`: the answers are checked on it when the tests run.
namespace Aoc.Year2021.Day06.Tests
import Aoc.Year2021.Day06 (..)
import Std (Fail)

def inputTimers: List Nat := Fail.orElse [] (() => parseTimers (include "../../../../../inputs/2021/day06.txt"))

test "real input, part 1" := solvePart1 inputTimers == 380243
test "real input, part 2" := solvePart2 inputTimers == 1708791884591
