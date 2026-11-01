-- The real puzzle input (aoc/inputs/2021/day11.txt, committed), through
-- `include`: the answers are checked on it when the tests run.
namespace Aoc.Year2021.Day11.Tests
import Aoc.Year2021.Day11 (..)
import Std (Fail, List, Text)

def inputLevels: Result (List (List Nat)) Text := Fail.toResult (() => parseLevels (include "../../../../../inputs/2021/day11.txt"))

test "real input, part 1" := inputLevels.map solvePart1 == Ok 1773
test "real input, part 2" := inputLevels.map solvePart2 == Ok (Some 494)
