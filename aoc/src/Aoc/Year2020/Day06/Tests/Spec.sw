--| Day 6's specification (Spec/Spec.sw) on the puzzle's examples and the
--| real input.

namespace Aoc.Year2020.Day06.Tests
import Aoc.Year2020.Day06.Spec (..)
import Std (List)

test "example, the spec's groups" := (groupsOf example).map List.length == [1, 3, 2, 4, 1]

test "example, the spec" := (part1Answer (groupsOf example), part2Answer (groupsOf example)) == (11, 6)

test "real input, the spec" :=
  let input := include "../../../../../inputs/2020/day06.txt"
  (part1Answer (groupsOf input), part2Answer (groupsOf input)) == (6630, 3437)
