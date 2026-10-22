-- The real puzzle input (aoc/inputs/day06.txt, committed, D119), through
-- `include`: the answers are checked on it when the tests run, and editing
-- the input reruns exactly these tests.
namespace Aoc.Day06.Tests
import Aoc.Day06 (..)

test "real input, part 1" := solvePart1 (parseWorksheet (include "../../../../inputs/day06.txt").lines) == 4722948564882
test "real input, part 2" := solvePart2 (parseWorksheet (include "../../../../inputs/day06.txt").lines) == 9581313737063
