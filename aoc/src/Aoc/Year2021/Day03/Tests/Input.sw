--| The real puzzle input (aoc/inputs/2021/day03.txt, committed), through
--| `include`: the answers are checked on it when the tests run.
namespace Aoc.Year2021.Day03.Tests
import Aoc.Common (Bits)
import Aoc.Year2021.Day03 (..)
import Std (Fail, List, Text)

def inputReport: Result (List Bits) Text :=
  Fail.toResult (() => parseReport (include "../../../../../inputs/2021/day03.txt"))

test "real input, part 1" := inputReport.map solvePart1 == Ok 4191876
test "real input, part 2" := inputReport.map solvePart2 == Ok (Some 3414905)
