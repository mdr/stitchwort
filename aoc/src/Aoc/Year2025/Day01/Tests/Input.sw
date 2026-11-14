--| The real puzzle input (aoc/inputs/2025/day01.txt, committed), through
--| `include`: the answers are checked on it when the tests run, and editing
--| the input reruns exactly these tests.
namespace Aoc.Year2025.Day01.Tests
import Aoc.Year2025.Day01 (..)
import Std (Fail, List, Result, Text)

def inputTurns: Result (List Turn) Text :=
  Fail.toResult (() => parseTurns (include "../../../../../inputs/2025/day01.txt"))

test "real input, part 1" := inputTurns.map solvePart1 == Ok 1076
test "real input, part 2" := inputTurns.map solvePart2 == Ok 6379
