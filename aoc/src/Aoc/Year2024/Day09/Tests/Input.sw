-- The real puzzle input (aoc/inputs/2024/day09.txt, committed), through
-- `include`: the answers are checked on it when the tests run.
namespace Aoc.Year2024.Day09.Tests
import Aoc.Year2024.Day09 (..)
import Std (Fail, List, Nat)

def inputDiskMap: List Nat := Fail.orElse [] (() => parseDiskMap (include "../../../../../inputs/2024/day09.txt"))

test "real input, part 1" := solvePart1 inputDiskMap == 6242766523059
test "real input, part 2" := solvePart2 inputDiskMap == 6272188244509
test "real input, size" := inputDiskMap.length == 19999 && (blocks inputDiskMap).length == 94500
test "real input, no file of length 0" := (layoutFrom 0 0 inputDiskMap).fst.all (file => file.span.length != 0)
