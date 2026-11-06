--| The real puzzle input (aoc/inputs/2020/day17.txt, committed), through
--| `include`: the answers are checked on it when the tests run, and editing
--| the input reruns exactly these tests.
namespace Aoc.Year2020.Day17.Tests
import Aoc.Year2020.Day17 (..)
import Std (List, Result, Text)

def input: Text := include "../../../../../inputs/2020/day17.txt"

test "real input, 8 rows of 8" := (parsed input).map (slice => (slice.grid.height, slice.grid.width)) == Ok (8, 8)
test "real input, part 1" := (parsed input).map (slice => slice.pocket 3 |> .boot |> .activeCount) == Ok 289
test "real input, part 2" := (parsed input).map (slice => slice.pocket 4 |> .boot |> .activeCount) == Ok 2084
