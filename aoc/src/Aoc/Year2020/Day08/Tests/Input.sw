--| The real puzzle input (aoc/inputs/2020/day08.txt, committed), through
--| `include`: the answers are checked on it when the tests run, and editing
--| the input reruns exactly these tests.
namespace Aoc.Year2020.Day08.Tests
import Aoc.Year2020.Day08 (..)
import Std (Fail, Int, List, Nat, Option, Result, Text)

def input: Text := include "../../../../../inputs/2020/day08.txt"

test "real input, 626 instructions" := (parsed input).map (program => program.instructions.length) == Ok 626
test "real input, part 1" := part1 input == Ok 1832
test "real input, part 2" := part2 input == Ok 662
test "real input, exactly one repair terminates" :=
  (parsed input).map (program =>
    let code := program.code
    program.instructions.withIndex.filterMap (((position, instruction)) => code.terminatesRepaired position instruction)
      |> .length)
    == Ok 1
