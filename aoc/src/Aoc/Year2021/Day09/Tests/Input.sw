-- The real puzzle input (aoc/inputs/2021/day09.txt, committed), through
-- `include`: the answers are checked on it when the tests run.
namespace Aoc.Year2021.Day09.Tests
import Aoc.Year2021.Day09 (..)
import Std (Fail)

def inputMap: HeightMap := Fail.orElse { rows = [] } (() => parseHeightMap (include "../../../../../inputs/2021/day09.txt"))

test "real input, part 1" := solvePart1 inputMap == 494
test "real input, part 2" := solvePart2 inputMap == 1048128
test "the real input keeps the promise" := eachInOneBasin inputMap
