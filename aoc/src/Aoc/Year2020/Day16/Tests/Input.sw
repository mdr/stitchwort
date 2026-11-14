--| The real puzzle input (aoc/inputs/2020/day16.txt, committed), through
--| `include`: the answers are checked on it when the tests run, and editing
--| the input reruns exactly these tests.
namespace Aoc.Year2020.Day16.Tests
import Aoc.Year2020.Day16 (..)
import Std (List, Option, Result, Text)

def input: Text := include "../../../../../inputs/2020/day16.txt"

test "real input, 20 fields and 236 nearby tickets" :=
  (parsed input).map (notes => (notes.rules.length, notes.nearby.length)) == Ok (20, 236)
test "real input, 190 valid tickets" := (parsed input).map (notes => notes.validTickets.length) == Ok 190
test "real input, part 1" := errorRate input == Ok 21071
test "real input, part 2" := (parsed input).map (.departureProduct) == Ok (Some 3429967441937)
