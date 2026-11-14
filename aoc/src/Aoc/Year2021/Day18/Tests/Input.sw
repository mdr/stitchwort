--| The real puzzle input (aoc/inputs/2021/day18.txt, committed), through
--| `include`: the answers are checked on it when the tests run.
namespace Aoc.Year2021.Day18.Tests
import Aoc.Year2021.Day18 (..)
import Std (Fail, Text)

def inputNumbers: Result (List Number) Text :=
  Fail.toResult (() => parseNumbers (include "../../../../../inputs/2021/day18.txt"))

test "real input, part 1" := inputNumbers.map solvePart1 == Ok (Some 4391)
test "real input, part 2" := inputNumbers.map solvePart2 == Ok (Some 4626)
