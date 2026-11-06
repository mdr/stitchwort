--| The real puzzle input (aoc/inputs/2020/day13.txt, committed), through
--| `include`: the answers are checked on it when the tests run, and editing
--| the input reruns exactly these tests.
namespace Aoc.Year2020.Day13.Tests
import Aoc.Year2020.Day13 (..)
import Std (List, Result, Text)

def input: Text := include "../../../../../inputs/2020/day13.txt"

test "real input, 9 buses in service" := (parsed input).map (notes => notes.buses.length) == Ok 9
test "real input, part 1" := part1 input == Ok (Some 2165)
test "real input, part 2" := part2 input == Ok (Some 534035653563227)
