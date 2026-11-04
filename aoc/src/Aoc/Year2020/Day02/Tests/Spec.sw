--| Day 2's specification (Spec/Spec.sw) on the puzzle's example and the real
--| input.

namespace Aoc.Year2020.Day02.Tests
import Aoc.Year2020.Day02.Spec (..)
import Std (List, Result)

test "example, the spec" := exampleEntries.map (entries => (part1Answer entries, part2Answer entries)) == Ok (2, 1)
test "real input, the spec" := inputEntries.map (entries => (part1Answer entries, part2Answer entries)) == Ok (603, 404)
