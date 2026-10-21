-- The real puzzle input (aoc/inputs/day07.txt, committed, D119), through
-- `include`: the answers are checked on it when the tests run, and editing
-- the input reruns exactly these tests.
namespace Aoc.Day07

test "real input, part 1" := Option.map solvePart1 (parseManifold (include "../../../inputs/day07.txt").lines) == Some 1594
test "real input, part 2" := Option.map solvePart2 (parseManifold (include "../../../inputs/day07.txt").lines) == Some 15650261281478
