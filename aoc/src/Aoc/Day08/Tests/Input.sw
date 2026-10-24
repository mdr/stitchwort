-- The real puzzle input (aoc/inputs/day08.txt, committed, D119), through
-- `include`: the answers are checked on it when the tests run, and editing
-- the input reruns exactly these tests.
namespace Aoc.Day08.Tests
import Aoc.Day08 (..)
import Std (Fail)

test "real input, part 1" := solvePart1 1000 (Fail.orElse (Boxes.of []) (() => parseBoxes (include "../../../../inputs/day08.txt").lines)) == 42315
test "real input, part 2" := solvePart2 (Fail.orElse (Boxes.of []) (() => parseBoxes (include "../../../../inputs/day08.txt").lines)) == Some 8079278220
