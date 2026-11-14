--| The real puzzle input (aoc/inputs/2024/day03.txt, committed), through
--| `include`: the answers are checked on it when the tests run.
namespace Aoc.Year2024.Day03.Tests
import Aoc.Year2024.Day03 (..)
import Std (Fail, List, Result, Text)

def inputInstructions: Result (List Instruction) Text :=
  Fail.toResult (() => parseInstructions (include "../../../../../inputs/2024/day03.txt"))

test "real input, part 1" := inputInstructions.map solvePart1 == Ok 174960292
test "real input, part 2" := inputInstructions.map solvePart2 == Ok 56275602
