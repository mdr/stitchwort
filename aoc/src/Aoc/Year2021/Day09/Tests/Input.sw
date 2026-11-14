--| The real puzzle input (aoc/inputs/2021/day09.txt, committed), through
--| `include`: the answers are checked on it when the tests run.
namespace Aoc.Year2021.Day09.Tests
import Aoc.Year2021.Day09 (..)
import Std (Fail, Text)

def inputMap: Result HeightMap Text :=
  Fail.toResult (() => parseHeightMap (include "../../../../../inputs/2021/day09.txt"))

test "real input, part 1" := inputMap.map solvePart1 == Ok 494
test "real input, part 2" := inputMap.map solvePart2 == Ok 1048128
test "the real input keeps the promise" := inputMap.map eachInOneBasin == Ok True
