--| The real puzzle input (aoc/inputs/2025/day03.txt, committed), through
--| `include`: the answers are checked on it when the tests run, and editing
--| the input reruns exactly these tests.
namespace Aoc.Year2025.Day03.Tests
import Aoc.Year2025.Day03 (..)
import Std (Fail, List, Result, Text)

def inputBanks: Result (List Bank) Text :=
  Fail.toResult (() => parseBanks (include "../../../../../inputs/2025/day03.txt"))

test "real input, part 1" := inputBanks.map solvePart1 == Ok 17263
test "real input, part 2" := inputBanks.map solvePart2 == Ok 170731717900423
