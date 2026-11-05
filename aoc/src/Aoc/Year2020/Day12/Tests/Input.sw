--| The real puzzle input (aoc/inputs/2020/day12.txt, committed), through
--| `include`: the answers are checked on it when the tests run, and editing
--| the input reruns exactly these tests.
namespace Aoc.Year2020.Day12.Tests
import Aoc.Year2020.Day12 (..)
import Std (List, Result, Text)

def input: Text := include "../../../../../inputs/2020/day12.txt"

test "real input, 783 instructions" := (parsed input).map (route => route.instructions.length) == Ok 783
test "real input, part 1" := part1 input == Ok 415
test "real input, part 2" := part2 input == Ok 29401
