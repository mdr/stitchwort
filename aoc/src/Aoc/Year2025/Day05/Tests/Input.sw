--| The real puzzle input (aoc/inputs/2025/day05.txt, committed), through
--| `include`: the answers are checked on it when the tests run, and editing
--| the input reruns exactly these tests.
namespace Aoc.Year2025.Day05.Tests
import Aoc.Year2025.Day05 (..)
import Std (Fail, Result, Text)

def inputDatabase: Result Database Text :=
  Fail.toResult (() => parseDatabase (include "../../../../../inputs/2025/day05.txt"))

test "real input, part 1" := inputDatabase.map solvePart1 == Ok 525
test "real input, part 2" := inputDatabase.map solvePart2 == Ok 333892124923577
