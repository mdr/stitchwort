--| The real puzzle input (aoc/inputs/2020/day19.txt, committed), through
--| `include`: the answers are checked on it when the tests run, and editing
--| the input reruns exactly these tests.
namespace Aoc.Year2020.Day19.Tests
import Aoc.Year2020.Day19 (..)
import Std (List, Result, Text)

def input: Text := include "../../../../../inputs/2020/day19.txt"

test "real input, 130 rules and 458 messages" :=
  (parsed input).map (received => (received.rules.numbered.length, received.messages.length)) == Ok (130, 458)
test "real input, the rules are productive in both parts" :=
  (parsed input).map (received => received.rules.productive && received.withLoops.rules.productive) == Ok True
test "real input, part 1" := (parsed input).map .matchingCount == Ok 182
test "real input, part 2" := (parsed input).map (received => received.withLoops.matchingCount) == Ok 334
