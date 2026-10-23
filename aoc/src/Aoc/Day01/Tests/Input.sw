-- The real puzzle input (aoc/inputs/day01.txt, committed, D119), through
-- `include`: the answers are checked on it when the tests run, and editing
-- the input reruns exactly these tests.
namespace Aoc.Day01.Tests
import Aoc.Day01 (..)
import Std (Fail)

test "real input, part 1" := solvePart1 (Fail.orElse [] (() => parseTurns (include "../../../../inputs/day01.txt").lines)) == 1076
test "real input, part 2" := solvePart2 (Fail.orElse [] (() => parseTurns (include "../../../../inputs/day01.txt").lines)) == 6379
