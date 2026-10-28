-- The real puzzle input (aoc/inputs/2024/day02.txt, committed), through
-- `include`: the answers are checked on it when the tests run.
namespace Aoc.Year2024.Day02.Tests
import Aoc.Year2024.Day02 (..)
import Std (Fail)

def inputReports: List Report :=
  Fail.orElse [] (() => parseReports (include "../../../../../inputs/2024/day02.txt"))

test "real input, part 1" := solvePart1 inputReports == 534
test "real input, part 2" := solvePart2 inputReports == 577
