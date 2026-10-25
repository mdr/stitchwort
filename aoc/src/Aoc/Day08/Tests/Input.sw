-- The real puzzle input (aoc/inputs/day08.txt, committed, D119), through
-- `include`: the answers are checked on it when the tests run, and editing
-- the input reruns exactly these tests.
namespace Aoc.Day08.Tests
import Aoc.Day08 (..)
import Std (Fail, Result, Text)

def input: Result Boxes Text := Fail.toResult (() => parseBoxes (include "../../../../inputs/day08.txt").lines)

test "real input loads" := input.isOk
test "real input, part 1" := input.map (solvePart1 1000) == Ok 42315
test "real input, part 2" := input.map solvePart2 == Ok (Some 8079278220)
