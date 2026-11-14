--| The real puzzle input (aoc/inputs/2020/day15.txt, committed), through
--| `include`. Part 2 isn't here: its 30,000,000 turns take about half a
--| minute and 900 MB, so `aoc_answers.rs` checks it in a test that runs only
--| when asked for.
namespace Aoc.Year2020.Day15.Tests
import Aoc.Year2020.Day15 (..)
import Std (List, NonEmptyList, Result, Text)

def input: Text := include "../../../../../inputs/2020/day15.txt"

test "real input, its starting numbers" :=
  (parsed input).map (starting => starting.numbers.toList) == Ok [15, 12, 0, 14, 3, 1]
test "real input, part 1" := spoken input 2020 == Ok 249
