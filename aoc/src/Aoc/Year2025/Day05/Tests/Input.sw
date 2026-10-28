-- The real puzzle input (aoc/inputs/2025/day05.txt, committed), through
-- `include`: the answers are checked on it when the tests run, and editing
-- the input reruns exactly these tests.
namespace Aoc.Year2025.Day05.Tests
import Aoc.Year2025.Day05 (..)
import Std (Fail)

test "real input, part 1" := solvePart1 (Fail.orElse emptyDatabase (() => parseDatabase (include "../../../../../inputs/2025/day05.txt"))) == 525
test "real input, part 2" := solvePart2 (Fail.orElse emptyDatabase (() => parseDatabase (include "../../../../../inputs/2025/day05.txt"))) == 333892124923577
