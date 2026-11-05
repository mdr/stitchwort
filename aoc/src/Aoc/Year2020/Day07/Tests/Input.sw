--| The real puzzle input (aoc/inputs/2020/day07.txt, committed), through
--| `include`: the answers are checked on it when the tests run, and editing
--| the input reruns exactly these tests.
namespace Aoc.Year2020.Day07.Tests
import Aoc.Year2020.Day07 (..)
import Std (Fail, List, Nat, Result, Text)

def input: Text := include "../../../../../inputs/2020/day07.txt"

test "real input, 594 rules" := (parsed input).map (rules => rules.all.length) == Ok 594
test "real input, part 1" := (parsed input).map solvePart1 == Ok 126
test "real input, part 2" := part2 input == Ok 220149
