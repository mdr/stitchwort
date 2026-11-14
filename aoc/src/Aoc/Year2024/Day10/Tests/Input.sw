--| The real puzzle input (aoc/inputs/2024/day10.txt, committed), through
--| `include`: the answers are checked on it when the tests run.
namespace Aoc.Year2024.Day10.Tests
import Aoc.Year2024.Day10 (..)
import Std (Fail, List, Nat, Option, Result, Text)

def inputMap: Result TopographicMap Text :=
  Fail.toResult (() => parseMap (include "../../../../../inputs/2024/day10.txt"))

test "real input, part 1" := inputMap.map solvePart1 == Ok 461
test "real input, part 2" := inputMap.map solvePart2 == Ok 875
test "real input, size" :=
  inputMap.map (map => (map.grid.rows.length, map.positions.length, map.trailheads.length)) == Ok (40, 1600, 175)

--| As the puzzle says, the real map has no impassable tiles.
test "real input, every tile has a height" :=
  inputMap.map (map => map.grid.rows.all (row => row.all (tile => tile.isSome))) == Ok True
