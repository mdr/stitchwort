--| The real puzzle input (aoc/inputs/2020/day20.txt, committed), through
--| `include`: the answers are checked on it when the tests run, and editing
--| the input reruns exactly these tests.
namespace Aoc.Year2020.Day20.Tests
import Aoc.Year2020.Day20 (..)
import Std (List, Result, Text)

def input: Text := include "../../../../../inputs/2020/day20.txt"

test "real input, 144 tiles" := (parsed input).map (jigsaw => jigsaw.tiles.length) == Ok 144
test "real input, part 1" := (parsed input).map (.cornerProduct) == Ok 66020135789767
test "real input, part 2" := (assembled input).map (.roughness) == Ok 1537
test "real input, the tiles are rectangles" := (parsed input).map (.rectangular) == Ok True
