--| The real puzzle input (aoc/inputs/2021/day15.txt, committed), through
--| `include`: the answers are checked on it when the tests run.
namespace Aoc.Year2021.Day15.Tests
import Aoc.Year2021.Day15 (..)
import Std (Fail, Text)

def inputCave: Result Cave Text := Fail.toResult (() => parseCave (include "../../../../../inputs/2021/day15.txt"))

test "real input, part 1" := inputCave.map solvePart1 == Ok 656
test "real input, part 2" := inputCave.map solvePart2 == Ok 2979
