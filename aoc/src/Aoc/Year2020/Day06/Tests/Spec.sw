--| Day 6's specification (Spec/Spec.sw) on the puzzle's examples and the
--| real input.

namespace Aoc.Year2020.Day06.Tests
import Aoc.Year2020.Day06.Spec (..)
import Std (Char, List, Text)

--| The input's groups of lines, split at the blank lines.
def groupsOf (input: Text): List (List (List Char)) := (input.lines.map Text.toList).splitBy (line => line == [])

test "example, the spec" :=
  let groups := groupsOf "abc\n\na\nb\nc\n\nab\nac\n\na\na\na\na\n\nb"
  (part1Answer groups, part2Answer groups) == (11, 6)

test "real input, the spec" :=
  let groups := groupsOf (include "../../../../../inputs/2020/day06.txt")
  (part1Answer groups, part2Answer groups) == (6630, 3437)
