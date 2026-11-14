--| The real puzzle input (aoc/inputs/2024/day09.txt, committed), through
--| `include`: the answers are checked on it when the tests run.
namespace Aoc.Year2024.Day09.Tests
import Aoc.Year2024.Day09 (..)
import Aoc.Year2024.Day09.Spec (part1, part2)
import Std (Fail, List, Nat, Result, Text)

def inputDiskMap: Result DiskMap Text :=
  Fail.toResult (() => parseDiskMap (include "../../../../../inputs/2024/day09.txt"))

test "real input, part 1" := inputDiskMap.map solvePart1 == Ok 6242766523059
test "real input, part 2" := inputDiskMap.map solvePart2 == Ok 6272188244509
test "real input, size" :=
  inputDiskMap.map (diskMap => (diskMap.lengths.length, diskMap.blocks.blocks.length)) == Ok (19999, 94500)
test "real input, no file of length 0" :=
  inputDiskMap.map (diskMap => (layoutFrom 0 0 diskMap.lengths).fst.all (file => file.span.length != 0)) == Ok True

--| The spec is too slow for the whole input: each move walks the disk.
test "real input, its first 99 digits, the spec agrees" :=
  inputDiskMap.map (diskMap =>
    let start: DiskMap := { lengths = diskMap.lengths.take 99 }
    solvePart1 start == part1 start && solvePart2 start == part2 start)
    == Ok True
