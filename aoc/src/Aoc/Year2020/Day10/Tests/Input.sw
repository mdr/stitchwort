--| The real puzzle input (aoc/inputs/2020/day10.txt, committed), through
--| `include`: the answers are checked on it when the tests run, and editing
--| the input reruns exactly these tests.
namespace Aoc.Year2020.Day10.Tests
import Aoc.Year2020.Day10 (..)
import Std (List, Option, Result, Text)

def input: Text := include "../../../../../inputs/2020/day10.txt"

test "real input, 104 adapters" := (parsed input).map (b => b.adapters.length) == Ok 104
test "real input, part 1" := part1 input == Ok (Some 2376)
test "real input, part 2" := part2 input == Ok (Some 129586085429248)
