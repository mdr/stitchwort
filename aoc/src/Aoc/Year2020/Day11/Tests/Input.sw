--| The real puzzle input (aoc/inputs/2020/day11.txt, committed), through
--| `include`: the answers are checked on it when the tests run, and editing
--| the input reruns exactly these tests.
namespace Aoc.Year2020.Day11.Tests
import Aoc.Year2020.Day11 (..)
import Std (List, Option, Result, Text)

def input: Text := include "../../../../../inputs/2020/day11.txt"

test "real input, 91 rows of 99" :=
  (parsed input).map (layout => (layout.grid.height, layout.grid.width)) == Ok (91, 99)
test "real input, part 1" := part1 input == Ok (Some 2354)
test "real input, part 2" := part2 input == Ok (Some 2072)
