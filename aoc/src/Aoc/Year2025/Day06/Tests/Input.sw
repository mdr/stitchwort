-- The real puzzle input (aoc/inputs/2025/day06.txt, committed), through
-- `include`: the answers are checked on it when the tests run, and editing
-- the input reruns exactly these tests.
namespace Aoc.Year2025.Day06.Tests
import Aoc.Year2025.Day06 (..)

test "real input, part 1" := solvePart1 (parseWorksheet (include "../../../../../inputs/2025/day06.txt").lines) == 4722948564882
test "real input, part 2" := solvePart2 (parseWorksheet (include "../../../../../inputs/2025/day06.txt").lines) == 9581313737063
