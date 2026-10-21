-- The real puzzle input (aoc/inputs/day04.txt, committed, D119), through
-- `include`: the answers are checked on it when the tests run, and editing
-- the input reruns exactly these tests.
namespace Aoc.Day04

test "real input, part 1" := Maybe.map solvePart1 (parseGrid (include "../../../inputs/day04.txt").lines) == Just 1397
test "real input, part 2" := Maybe.map solvePart2 (parseGrid (include "../../../inputs/day04.txt").lines) == Just 8758
