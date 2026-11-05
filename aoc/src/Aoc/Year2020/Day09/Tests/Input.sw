--| The real puzzle input (aoc/inputs/2020/day09.txt, committed), through
--| `include`: the answers are checked on it when the tests run, and editing
--| the input reruns exactly these tests.
namespace Aoc.Year2020.Day09.Tests
import Aoc.Year2020.Day09 (..)
import Std (List, Option, Result, Text)

def input: Text := include "../../../../../inputs/2020/day09.txt"

test "real input, 1000 numbers" := (parsed input).map (data => data.numbers.length) == Ok 1000
test "real input, part 1" := part1 input (preamble := 25) == Ok (Some 373803594)
test "real input, part 2" := part2 input (preamble := 25) == Ok (Some 51152360)
