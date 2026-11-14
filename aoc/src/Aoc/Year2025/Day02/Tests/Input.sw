--| The real puzzle input (aoc/inputs/2025/day02.txt, committed), through
--| `include`: the answers are checked on it when the tests run, and editing
--| the input reruns exactly these tests.
namespace Aoc.Year2025.Day02.Tests
import Aoc.Year2025.Day02 (..)
import Std (Fail, List, Result, Text)
import Aoc.Common (Range)

def inputRanges: Result (List Range) Text :=
  Fail.toResult (() => parseRanges (include "../../../../../inputs/2025/day02.txt"))

test "real input, part 1" := inputRanges.map solvePart1 == Ok 16793817782
test "real input, part 2" := inputRanges.map solvePart2 == Ok 27469417404
