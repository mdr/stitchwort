--| The real puzzle input (aoc/inputs/2020/day05.txt, committed), through
--| `include`: the answers are checked on it when the tests run, and editing
--| the input reruns exactly these tests.
namespace Aoc.Year2020.Day05.Tests
import Aoc.Year2020.Day05 (..)
import Std (Fail, List, Option, Result, Text)

def inputPasses: Result (List Pass) Text :=
  Fail.toResult (() => parsePasses (include "../../../../../inputs/2020/day05.txt"))

test "real input, part 1" := inputPasses.map solvePart1 == Ok (Some 813)
test "real input, part 2" := inputPasses.map solvePart2 == Ok (Some 612)
test "real input, 807 passes" := inputPasses.map List.length == Ok 807
