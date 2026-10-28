-- The real puzzle input (aoc/inputs/2025/day03.txt, committed), through
-- `include`: the answers are checked on it when the tests run, and editing
-- the input reruns exactly these tests.
namespace Aoc.Year2025.Day03.Tests
import Aoc.Year2025.Day03 (..)
import Std (Fail)

test "real input, part 1" := solvePart1 (Fail.orElse [] (() => parseBanks (include "../../../../../inputs/2025/day03.txt"))) == 17263
test "real input, part 2" := solvePart2 (Fail.orElse [] (() => parseBanks (include "../../../../../inputs/2025/day03.txt"))) == 170731717900423
