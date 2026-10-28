-- The real puzzle input (aoc/inputs/2024/day08.txt, committed), through
-- `include`: the answers are checked on it when the tests run.
namespace Aoc.Year2024.Day08.Tests
import Aoc.Year2024.Day08 (..)
import Std (Fail, List)

def inputCity: City := Fail.orElse { height = 0, width = 0, antennas = [] } (() => parseCity (include "../../../../../inputs/2024/day08.txt"))

test "real input, part 1" := solvePart1 inputCity == 344
test "real input, part 2" := solvePart2 inputCity == 1182
test "real input, size" := inputCity.height == 50 && inputCity.width == 50 && inputCity.antennas.length == 207

-- Every frequency has a second antenna, so every antenna is a part 2
-- antinode.
test "real input, no lone antennas" :=
  inputCity.antennas.all (antenna => inputCity.antennaPairs.any (pair => pair.fst == antenna.position))

-- No two antennas of a frequency are a multiple of 3 apart in both
-- directions, so there are no antinodes between antennas: each pair has one
-- on either side, as the puzzle says.
test "real input, no antinodes between antennas" :=
  inputCity.antennaPairs.all (((far, near)) => (near.minus far).row % 3 != 0 || (near.minus far).column % 3 != 0)
