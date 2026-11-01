-- The real puzzle input (aoc/inputs/2024/day02.txt, committed), through
-- `include`: the answers are checked on it when the tests run.
namespace Aoc.Year2024.Day02.Tests
import Aoc.Year2024.Day02 (..)
import Std (Fail, List, Result, Text)

def inputReports: Result (List Report) Text :=
  Fail.toResult (() => parseReports (include "../../../../../inputs/2024/day02.txt"))

test "real input, part 1" := inputReports.map solvePart1 == Ok 534
test "real input, part 2" := inputReports.map solvePart2 == Ok 577
