-- The real puzzle input (aoc/inputs/2021/day12.txt, committed), through
-- `include`: the answers are checked on it when the tests run.
namespace Aoc.Year2021.Day12.Tests
import Aoc.Year2021.Day12 (..)
import Std (Fail, List)

def inputPassages: List (Text, Text) := Fail.orElse [] (() => parsePassages (include "../../../../../inputs/2021/day12.txt"))

test "real input, part 1" := solvePart1 inputPassages == 3510
test "real input, part 2" := solvePart2 inputPassages == 122880
