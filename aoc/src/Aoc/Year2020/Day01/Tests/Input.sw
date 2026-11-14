--| The real puzzle input (aoc/inputs/2020/day01.txt, committed), through
--| `include`: the answers are checked on it when the tests run, and editing
--| the input reruns exactly these tests.
namespace Aoc.Year2020.Day01.Tests
import Aoc.Year2020.Day01 (..)
import Std (Fail, List, Option, Result, Text)

def inputEntries: Result (List Nat) Text :=
  Fail.toResult (() => parseEntries (include "../../../../../inputs/2020/day01.txt"))

test "real input, part 1" := inputEntries.map solvePart1 == Ok (Some 1016619)
test "real input, part 2" := inputEntries.map solvePart2 == Ok (Some 218767230)
