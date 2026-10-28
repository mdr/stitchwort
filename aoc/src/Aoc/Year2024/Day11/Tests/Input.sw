-- The real puzzle input (aoc/inputs/2024/day11.txt, committed), through
-- `include`: the answers are checked on it when the tests run.
namespace Aoc.Year2024.Day11.Tests
import Aoc.Year2024.Day11 (..)
import Std (Fail, List, Map, Nat)

def inputStones: List Nat := Fail.orElse [] (() => parseStones (include "../../../../../inputs/2024/day11.txt"))

test "real input, part 1" := solvePart1 inputStones == 186175
test "real input, part 2" := solvePart2 inputStones == 220566831337810
test "real input, size" := inputStones.length == 8

-- How many different numbers the stones show after 75 blinks: why counting
-- by number is small.
test "real input, distinct numbers after 75 blinks" := 75.iterate blinkCounts (Map.counts inputStones) |> .size |> (== 3792)
