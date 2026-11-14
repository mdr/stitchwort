--| The real puzzle input (aoc/inputs/2020/day04.txt, committed), through
--| `include`: the answers are checked on it when the tests run, and editing
--| the input reruns exactly these tests.
namespace Aoc.Year2020.Day04.Tests
import Aoc.Year2020.Day04 (..)
import Std (Fail, List, Result, Text)

def inputPassports: Result (List Passport) Text :=
  Fail.toResult (() => parsePassports (include "../../../../../inputs/2020/day04.txt"))

test "real input, part 1" := inputPassports.map solvePart1 == Ok 200
test "real input, part 2" := inputPassports.map solvePart2 == Ok 116
test "real input, 265 passports" := inputPassports.map List.length == Ok 265
