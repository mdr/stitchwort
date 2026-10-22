-- The real puzzle input (aoc/inputs/day08.txt, committed, D119), through
-- `include`: the answers are checked on it when the tests run, and editing
-- the input reruns exactly these tests.
namespace Aoc.Day08.Tests
import Aoc.Day08 (..)
import Std (Option)

def realInput: Boxes := parseBoxes (include "../../../../inputs/day08.txt").lines

test "real input, part 1" := solvePart1 1000 realInput == 42315
test "real input, part 2" := solvePart2 realInput == Some 8079278220
