-- The real puzzle input (aoc/inputs/2021/day08.txt, committed), through
-- `include`: the answers are checked on it when the tests run.
namespace Aoc.Year2021.Day08.Tests
import Aoc.Year2021.Day08 (..)
import Std (Fail)

def inputEntries: List Entry := Fail.orElse [] (() => parseEntries (include "../../../../../inputs/2021/day08.txt"))

test "real input, part 1" := solvePart1 inputEntries == 445
test "real input, part 2" := solvePart2 inputEntries == 1043101
