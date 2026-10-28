-- The real puzzle input (aoc/inputs/2024/day10.txt, committed), through
-- `include`: the answers are checked on it when the tests run.
namespace Aoc.Year2024.Day10.Tests
import Aoc.Year2024.Day10 (..)
import Std (Fail, List, Nat, Option)

def inputMap: TopographicMap := Fail.orElse { rows = [] } (() => parseMap (include "../../../../../inputs/2024/day10.txt"))

test "real input, part 1" := solvePart1 inputMap == 461
test "real input, part 2" := solvePart2 inputMap == 875
test "real input, size" := inputMap.rows.length == 40 && inputMap.positions.length == 1600 && inputMap.trailheads.length == 175

-- As the puzzle says, the real map has no impassable tiles.
test "real input, every tile has a height" := inputMap.rows.all (row => row.all (tile => tile.isSome))
