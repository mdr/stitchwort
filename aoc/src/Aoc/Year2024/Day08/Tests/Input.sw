--| The real puzzle input (aoc/inputs/2024/day08.txt, committed), through
--| `include`: the answers are checked on it when the tests run.
namespace Aoc.Year2024.Day08.Tests
import Aoc.Year2024.Day08 (..)
import Std (Fail, List, Result, Text)

def inputCity: Result City Text := Fail.toResult (() => parseCity (include "../../../../../inputs/2024/day08.txt"))

test "real input, part 1" := inputCity.map solvePart1 == Ok 344
test "real input, part 2" := inputCity.map solvePart2 == Ok 1182
test "real input, size" :=
  inputCity.map (city => city.height == 50 && city.width == 50 && city.antennas.length == 207) == Ok True

--| Every frequency has a second antenna, so every antenna is a part 2
--| antinode.
test "real input, no lone antennas" :=
  inputCity.map (city => city.antennas.all (antenna => city.antennaPairs.any (pair => pair.fst == antenna.position)))
    == Ok True

--| No two antennas of a frequency are a multiple of 3 apart in both
--| directions, so there are no antinodes between antennas: each pair has one
--| on either side, as the puzzle says.
test "real input, no antinodes between antennas" :=
  inputCity.map (city =>
    city.antennaPairs.all (((far, near)) => (near.minus far).rows % 3 != 0 || (near.minus far).columns % 3 != 0))
    == Ok True
