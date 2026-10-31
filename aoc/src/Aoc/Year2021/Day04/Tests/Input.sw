-- The real puzzle input (aoc/inputs/2021/day04.txt, committed), through
-- `include`: the answers are checked on it when the tests run.
namespace Aoc.Year2021.Day04.Tests
import Aoc.Year2021.Day04 (..)
import Std (Fail)

def inputGame: Game := Fail.orElse { draws = [], boards = [] } (() => parseGame (include "../../../../../inputs/2021/day04.txt"))

test "real input, part 1" := solvePart1 inputGame == Some 49860
test "real input, part 2" := solvePart2 inputGame == Some 24628
