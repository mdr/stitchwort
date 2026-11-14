--| The real puzzle input (aoc/inputs/2020/day03.txt, committed), through
--| `include`: the answers are checked on it when the tests run, and editing
--| the input reruns exactly these tests.
namespace Aoc.Year2020.Day03.Tests
import Aoc.Common (Grid)
import Aoc.Year2020.Day03 (..)
import Std (Fail, List, Result, Text)

def inputMap: Result (Grid Square) Text :=
  Fail.toResult (() => parseMap (include "../../../../../inputs/2020/day03.txt"))

test "real input, part 1" := inputMap.map solvePart1 == Ok 276
test "real input, part 2" := inputMap.map solvePart2 == Ok 7812180000
test "real input, slope by slope" := inputMap.map (map => slopes.map (treesOn map)) == Ok [100, 276, 85, 90, 37]
test "real input, 323 rows of 31" := inputMap.map (map => (map.height, map.width)) == Ok (323, 31)
