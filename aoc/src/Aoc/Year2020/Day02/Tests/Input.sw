--| The real puzzle input (aoc/inputs/2020/day02.txt, committed), through
--| `include`: the answers are checked on it when the tests run, and editing
--| the input reruns exactly these tests.
namespace Aoc.Year2020.Day02.Tests
import Aoc.Year2020.Day02 (..)
import Std (Fail, List, Result, Text)

def inputEntries: Result (List Entry) Text :=
  Fail.toResult (() => parseEntries (include "../../../../../inputs/2020/day02.txt"))

test "real input, part 1" := inputEntries.map solvePart1 == Ok 603
test "real input, part 2" := inputEntries.map solvePart2 == Ok 404
test "real input, 1000 entries" := inputEntries.map List.length == Ok 1000
