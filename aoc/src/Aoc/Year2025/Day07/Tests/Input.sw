-- The real puzzle input (aoc/inputs/2025/day07.txt, committed), through
-- `include`: the answers are checked on it when the tests run, and editing
-- the input reruns exactly these tests.
namespace Aoc.Year2025.Day07.Tests
import Aoc.Year2025.Day07 (..)
import Std (Option)

test "real input, part 1" := (parseManifoldOption (include "../../../../../inputs/2025/day07.txt").lines).map solvePart1 == Some 1594
test "real input, part 2" := (parseManifoldOption (include "../../../../../inputs/2025/day07.txt").lines).map solvePart2 == Some 15650261281478
