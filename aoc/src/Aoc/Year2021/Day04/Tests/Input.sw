-- The real puzzle input (aoc/inputs/2021/day04.txt, committed), through
-- `include`: the answers are checked on it when the tests run.
namespace Aoc.Year2021.Day04.Tests
import Aoc.Year2021.Day04 (..)
import Std (Fail, Text)

def inputGame: Result Game Text := Fail.toResult (() => parseGame (include "../../../../../inputs/2021/day04.txt"))

test "real input, part 1" := inputGame.map solvePart1 == Ok (Some 49860)
test "real input, part 2" := inputGame.map solvePart2 == Ok (Some 24628)
