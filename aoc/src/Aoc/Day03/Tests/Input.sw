-- The real puzzle input (aoc/inputs/day03.txt, committed, D119), through
-- `include`: the answers are checked on it when the tests run, and editing
-- the input reruns exactly these tests.
namespace Aoc.Day03.Tests
import Aoc.Day03 (..)
import Std (Fail)

test "real input, part 1" := solvePart1 (Fail.orElse [] (() => parseBanks (include "../../../../inputs/day03.txt").lines)) == 17263
test "real input, part 2" := solvePart2 (Fail.orElse [] (() => parseBanks (include "../../../../inputs/day03.txt").lines)) == 170731717900423
