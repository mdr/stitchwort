--| The real puzzle input (aoc/inputs/2020/day06.txt, committed), through
--| `include`: the answers are checked on it when the tests run, and editing
--| the input reruns exactly these tests.
namespace Aoc.Year2020.Day06.Tests
import Aoc.Year2020.Day06 (..)
import Std (Fail, List, Nat, Result, Text)

def inputGroups: Result (List Group) Text :=
  Fail.toResult (() => parseGroups (include "../../../../../inputs/2020/day06.txt"))

test "real input, part 1" := inputGroups.map solvePart1 == Ok 6630
test "real input, part 2" := inputGroups.map solvePart2 == Ok 3437
test "real input, 483 groups of 1713 people" :=
  inputGroups.map (groups => (groups.length, groups.sumBy (group => group.people.length))) == Ok (483, 1713)
