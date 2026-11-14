--| The real puzzle input (aoc/inputs/2021/day17.txt, committed), through
--| `include`: the answers are checked on it when the tests run.
namespace Aoc.Year2021.Day17.Tests
import Aoc.Year2021.Day17 (..)
import Std (Fail, Text)

def inputTarget: Result Target Text :=
  Fail.toResult (() => parseTarget (include "../../../../../inputs/2021/day17.txt"))

test "real input, part 1" := inputTarget.map solvePart1 == Ok (Some 6786)
test "real input, part 2" := inputTarget.map solvePart2 == Ok 2313
