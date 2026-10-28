-- The real puzzle input (aoc/inputs/2024/day03.txt, committed), through
-- `include`: the answers are checked on it when the tests run.
namespace Aoc.Year2024.Day03.Tests
import Aoc.Year2024.Day03 (..)
import Std (Fail)

def inputInstructions: List Instruction := Fail.orElse [] (() => parseInstructions (include "../../../../../inputs/2024/day03.txt"))

test "real input, part 1" := solvePart1 inputInstructions == 174960292
test "real input, part 2" := solvePart2 inputInstructions == 56275602
