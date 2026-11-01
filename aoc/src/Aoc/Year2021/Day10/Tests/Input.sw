-- The real puzzle input (aoc/inputs/2021/day10.txt, committed), through
-- `include`: the answers are checked on it when the tests run.
namespace Aoc.Year2021.Day10.Tests
import Aoc.Year2021.Day10 (..)
import Std (Fail, List)

def inputLines: List (List Token) := Fail.orElse [] (() => parseLines (include "../../../../../inputs/2021/day10.txt"))

test "real input, part 1" := solvePart1 inputLines == 364389
test "real input, part 2" := solvePart2 inputLines == 2870201088
-- The puzzle's promise: an odd number of incomplete lines.
test "an odd number of incomplete lines" := (inputLines.filterMap autocompleteScore).length % 2 == 1
