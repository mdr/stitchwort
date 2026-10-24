-- The real puzzle input (aoc/inputs/day09.txt, committed, D119), through
-- `include`: the answers are checked on it when the tests run, and editing
-- the input reruns exactly these tests.
namespace Aoc.Day09.Tests
import Aoc.Day09 (..)
import Std (Fail)

test "real input, part 1" := solvePart1 (Fail.orElse [] (() => parseTiles (include "../../../../inputs/day09.txt").lines)) == 4756718172
test "real input, part 2" := solvePart2 (Fail.orElse [] (() => parseTiles (include "../../../../inputs/day09.txt").lines)) == 1665679194
