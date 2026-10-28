-- The real puzzle input (aoc/inputs/2025/day08.txt, committed), through
-- `include`: the answers are checked on it when the tests run, and editing
-- the input reruns exactly these tests.
namespace Aoc.Year2025.Day08.Tests
import Aoc.Year2025.Day08 (..)
import Std (Fail, Result, Text)

def input: Result Boxes Text := Fail.toResult (() => parseBoxes (include "../../../../../inputs/2025/day08.txt"))

test "real input loads" := input.isOk
test "real input, part 1" := input.map (solvePart1 1000) == Ok 42315
test "real input, part 2" := input.map solvePart2 == Ok (Some 8079278220)
