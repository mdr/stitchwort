-- The real puzzle input (aoc/inputs/2024/day04.txt, committed), through
-- `include`: the answers are checked on it when the tests run.
namespace Aoc.Year2024.Day04.Tests
import Aoc.Year2024.Day04 (..)

def inputGrid: Grid := parseGrid (include "../../../../../inputs/2024/day04.txt").lines

test "real input, part 1" := solvePart1 inputGrid == 2524
test "real input, part 2" := solvePart2 inputGrid == 1873
