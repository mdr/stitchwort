-- The real puzzle input (aoc/inputs/2024/day06.txt, committed), through
-- `include`: the answers are checked on it when the tests run.
namespace Aoc.Year2024.Day06.Tests
import Aoc.Year2024.Day06 (..)

def inputLab: Lab := labOf (include "../../../../../inputs/2024/day06.txt").lines

test "real input, part 1" := solvePart1 inputLab == Some 4967
test "real input, part 2" := solvePart2 inputLab == Some 1789
