-- The real puzzle input (aoc/inputs/day04.txt, committed, D119), through
-- `include`: the answers are checked on it when the tests run, and editing
-- the input reruns exactly these tests.
namespace Aoc.Day04.Tests
import Aoc.Day04 (..)
import Std (Result)

test "real input, part 1" := (parseGrid (include "../../../../inputs/day04.txt").lines).map solvePart1 == Ok 1397
test "real input, part 2" := (parseGrid (include "../../../../inputs/day04.txt").lines).map solvePart2 == Ok 8758
