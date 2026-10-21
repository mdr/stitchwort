-- The real puzzle input (aoc/inputs/day05.txt, committed, D119), through
-- `include`: the answers are checked on it when the tests run, and editing
-- the input reruns exactly these tests.
namespace Aoc.Day05

test "real input, part 1" := solvePart1 (parseDatabase (include "../../../inputs/day05.txt").lines) == 525
test "real input, part 2" := solvePart2 (parseDatabase (include "../../../inputs/day05.txt").lines) == 333892124923577
