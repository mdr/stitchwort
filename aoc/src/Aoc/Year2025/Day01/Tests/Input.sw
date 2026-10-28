-- The real puzzle input (aoc/inputs/2025/day01.txt, committed), through
-- `include`: the answers are checked on it when the tests run, and editing
-- the input reruns exactly these tests.
namespace Aoc.Year2025.Day01.Tests
import Aoc.Year2025.Day01 (..)
import Std (Fail)

test "real input, part 1" := solvePart1 (Fail.orElse [] (() => parseTurns (include "../../../../../inputs/2025/day01.txt"))) == 1076
test "real input, part 2" := solvePart2 (Fail.orElse [] (() => parseTurns (include "../../../../../inputs/2025/day01.txt"))) == 6379
