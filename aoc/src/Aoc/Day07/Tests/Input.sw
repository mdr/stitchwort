-- The real puzzle input (aoc/inputs/day07.txt, committed, D119), through
-- `include`: the answers are checked on it when the tests run, and editing
-- the input reruns exactly these tests.
namespace Aoc.Day07.Tests
import Aoc.Day07 (..)
import Std (Option)

test "real input, part 1" := Option.map (parseManifoldOption (include "../../../../inputs/day07.txt").lines) solvePart1 == Some 1594
test "real input, part 2" := Option.map (parseManifoldOption (include "../../../../inputs/day07.txt").lines) solvePart2 == Some 15650261281478
