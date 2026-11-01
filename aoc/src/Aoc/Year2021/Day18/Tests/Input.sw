-- The real puzzle input (aoc/inputs/2021/day18.txt, committed), through
-- `include`: the answers are checked on it when the tests run.
namespace Aoc.Year2021.Day18.Tests
import Aoc.Year2021.Day18 (..)
import Std (Fail)

def inputNumbers: List Number := Fail.orElse Nil (() => parseNumbers (include "../../../../../inputs/2021/day18.txt"))

test "real input, part 1" := solvePart1 inputNumbers == Some 4391
test "real input, part 2" := solvePart2 inputNumbers == Some 4626
