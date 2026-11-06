--| The real puzzle input (aoc/inputs/2020/day18.txt, committed), through
--| `include`: the answers are checked on it when the tests run, and editing
--| the input reruns exactly these tests.
namespace Aoc.Year2020.Day18.Tests
import Aoc.Year2020.Day18 (..)
import Std (List, Result, Text)

def input: Text := include "../../../../../inputs/2020/day18.txt"

test "real input, 372 lines" := (parsed input samePrecedence).map (homework => homework.expressions.length) == Ok 372
test "real input, part 1" := (parsed input samePrecedence).map .sum == Ok 15285807527593
test "real input, part 2" := (parsed input additionFirst).map .sum == Ok 461295257566346
