-- The spec run on the examples: it gives the puzzle's answers too.

namespace Aoc.Year2024.Day04.Tests
import Aoc.Year2024.Day04 (..)
import Aoc.Year2024.Day04.Spec (..)

test "spec, example, part 1" := part1Spec example == 18
test "spec, example, part 2" := part2Spec example == 9
test "spec, eight from one X" := part1Spec (parseGrid ["S..S..S", ".A.A.A.", "..MMM..", "SAMXMAS", "..MMM..", ".A.A.A.", "S..S..S"]) == 8
test "spec, rows of different lengths" := part1Spec (parseGrid ["X", "MM", "AAA", "SSSS"]) == 2
test "spec, a cross in rows of different lengths" := part2Spec (parseGrid ["M.S", ".A", "M.S"]) == 1
