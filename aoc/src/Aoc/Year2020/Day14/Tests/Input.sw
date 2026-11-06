--| The real puzzle input (aoc/inputs/2020/day14.txt, committed), through
--| `include`: the answers are checked on it when the tests run, and editing
--| the input reruns exactly these tests.
namespace Aoc.Year2020.Day14.Tests
import Aoc.Year2020.Day14 (..)
import Std (List, Result, Text)

def input: Text := include "../../../../../inputs/2020/day14.txt"

test "real input, 572 instructions" := (parsed input).map (program => program.instructions.length) == Ok 572
test "real input, part 1" := part1 input == Ok 13496669152158
test "real input, part 2" := part2 input == Ok 3278997609887
