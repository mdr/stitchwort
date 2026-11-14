--| Day 1's specification (Spec/Spec.sw) on the puzzle's example and the real
--| input: each has exactly one answer, the program's.

namespace Aoc.Year2020.Day01.Tests
import Aoc.Year2020.Day01.Spec (..)
import Std (List, Result)

test "example, every pair and triple" :=
  exampleEntries.map (entries => (part1Answers entries, part2Answers entries)) == Ok ([514579], [241861950])
test "real input, every pair" := inputEntries.map part1Answers == Ok [1016619]
test "real input, every triple" := inputEntries.map part2Answers == Ok [218767230]
