-- The real puzzle input (aoc/inputs/2025/day02.txt, committed), through
-- `include`: the answers are checked on it when the tests run, and editing
-- the input reruns exactly these tests.
namespace Aoc.Year2025.Day02.Tests
import Aoc.Year2025.Day02 (..)
import Std (Fail)

test "real input, part 1" := solvePart1 (Fail.orElse [] (() => parseRanges (include "../../../../../inputs/2025/day02.txt"))) == 16793817782
test "real input, part 2" := solvePart2 (Fail.orElse [] (() => parseRanges (include "../../../../../inputs/2025/day02.txt"))) == 27469417404
