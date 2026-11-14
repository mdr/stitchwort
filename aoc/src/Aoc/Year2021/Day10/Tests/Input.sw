--| The real puzzle input (aoc/inputs/2021/day10.txt, committed), through
--| `include`: the answers are checked on it when the tests run.
namespace Aoc.Year2021.Day10.Tests
import Aoc.Year2021.Day10 (..)
import Std (Fail, List, Text)

def inputLines: Result (List (List Token)) Text :=
  Fail.toResult (() => parseLines (include "../../../../../inputs/2021/day10.txt"))

test "real input, part 1" := inputLines.map solvePart1 == Ok 364389
test "real input, part 2" := inputLines.map solvePart2 == Ok 2870201088
--| The puzzle's promise: an odd number of incomplete lines.
test "an odd number of incomplete lines" :=
  inputLines.map (lines => (lines.filterMap autocompleteScore).length % 2) == Ok 1
