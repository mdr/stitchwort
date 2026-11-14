--| The real puzzle input (aoc/inputs/2024/day07.txt, committed), through
--| `include`: the answers are checked on it when the tests run.
namespace Aoc.Year2024.Day07.Tests
import Aoc.Year2024.Day07 (..)
import Std (Fail, List, Result, Text)

def inputEquations: Result (List Equation) Text :=
  Fail.toResult (() => parseEquations (include "../../../../../inputs/2024/day07.txt"))

test "real input, part 1" := inputEquations.map solvePart1 == Ok 66343330034722
test "real input, part 2" := inputEquations.map solvePart2 == Ok 637696070419031
test "real input, size" := inputEquations.map (equations => equations.length) == Ok 850
test "real input, two to twelve numbers, none of them 0" :=
  inputEquations.map (equations =>
    equations.all (equation => 2 <= equation.numbers.length <= 12 && equation.numbers.all (number => number != 0)))
    == Ok True
