--| Day 3's specification (Spec/Spec.sw) on the puzzle's example and the real
--| input.

namespace Aoc.Year2020.Day03.Tests
import Aoc.Year2020.Day03.Spec (..)
import Std (List, Result)

test "example, the spec" := exampleMap.map (map => (part1Answer map, part2Answer map)) == Ok (7, 336)
test "real input, the spec" := inputMap.map (map => (part1Answer map, part2Answer map)) == Ok (276, 7812180000)
