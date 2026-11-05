--| The real puzzle input (aoc/inputs/2025/day09.txt, committed), through
--| `include`: the answers are checked on it when the tests run, and editing
--| the input reruns exactly these tests.
namespace Aoc.Year2025.Day09.Tests
import Aoc.Common (Line, Point)
import Aoc.Year2025.Day09 (..)
import Std (Fail, List, Result, Text)

def input: Result (List Point) Text := Fail.toResult (() => parseTiles (include "../../../../../inputs/2025/day09.txt"))

test "real input, part 1" := input.map solvePart1 == Ok 4756718172
test "real input, part 2" := input.map solvePart2 == Ok 1665679194
