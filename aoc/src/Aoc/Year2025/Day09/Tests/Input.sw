-- The real puzzle input (aoc/inputs/2025/day09.txt, committed), through
-- `include`: the answers are checked on it when the tests run, and editing
-- the input reruns exactly these tests.
namespace Aoc.Year2025.Day09.Tests
import Aoc.Year2025.Day09 (..)
import Std (Fail)

test "real input, part 1" := solvePart1 (Fail.orElse [] (() => parseTiles (include "../../../../../inputs/2025/day09.txt"))) == 4756718172
test "real input, part 2" := solvePart2 (Fail.orElse [] (() => parseTiles (include "../../../../../inputs/2025/day09.txt"))) == 1665679194
