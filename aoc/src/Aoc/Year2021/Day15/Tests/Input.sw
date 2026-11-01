-- The real puzzle input (aoc/inputs/2021/day15.txt, committed), through
-- `include`: the answers are checked on it when the tests run.
namespace Aoc.Year2021.Day15.Tests
import Aoc.Year2021.Day15 (..)
import Std (Fail)

def inputCave: Cave := Fail.orElse { rows = [] } (() => parseCave (include "../../../../../inputs/2021/day15.txt"))

test "real input, part 1" := solvePart1 inputCave == 656
test "real input, part 2" := solvePart2 inputCave == 2979
