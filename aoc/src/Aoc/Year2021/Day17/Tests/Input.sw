-- The real puzzle input (aoc/inputs/2021/day17.txt, committed), through
-- `include`: the answers are checked on it when the tests run.
namespace Aoc.Year2021.Day17.Tests
import Aoc.Year2021.Day17 (..)
import Std (Fail)

def inputTarget: Target := Fail.orElse { left = 0, right = 0, bottom = 0, top = 0 } (() => parseTarget (include "../../../../../inputs/2021/day17.txt"))

test "real input, part 1" := solvePart1 inputTarget == Some 6786
test "real input, part 2" := solvePart2 inputTarget == 2313
