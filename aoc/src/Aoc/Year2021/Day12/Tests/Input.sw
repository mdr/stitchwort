--| The real puzzle input (aoc/inputs/2021/day12.txt, committed), through
--| `include`: the answers are checked on it when the tests run.
namespace Aoc.Year2021.Day12.Tests
import Aoc.Year2021.Day12 (..)
import Std (Fail, List, Text)

def inputPassages: Result (List Passage) Text :=
  Fail.toResult (() => parsePassages (include "../../../../../inputs/2021/day12.txt"))

test "real input, part 1" := inputPassages.map solvePart1 == Ok 3510
test "real input, part 2" := inputPassages.map solvePart2 == Ok 122880
