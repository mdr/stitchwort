--| The real puzzle input (aoc/inputs/2021/day05.txt, committed), through
--| `include`: the answers are checked on it when the tests run.
namespace Aoc.Year2021.Day05.Tests
import Aoc.Common (Line)
import Aoc.Year2021.Day05 (..)
import Std (Fail, Text)

def inputLines: Result (List Line) Text :=
  Fail.toResult (() => parseLines (include "../../../../../inputs/2021/day05.txt"))

test "real input, part 1" := inputLines.map solvePart1 == Ok 8060
test "real input, part 2" := inputLines.map solvePart2 == Ok 21577
