--| Advent of Code 2021, day 1: a submarine's sonar reports the sea floor's
--| depth, one measurement per line. Part 1 counts the measurements that are
--| deeper than the one before. Part 2 adds up each run of three consecutive
--| measurements (a sliding window) and counts the sums that are larger than
--| the one before.
--|
--|   $ cd aoc && stitchwort run Aoc.Year2021.Day01.main < inputs/2021/day01.txt
--|
--| The puzzle input is committed in aoc/inputs/2021/.
--|
--| Part 2 doesn't add up the windows: two windows next to each other share all
--| but one measurement each, so the later sum is larger exactly when the
--| measurement it gains is deeper than the one it loses, three places earlier.
--| Both parts are then one function, `increasesOver`. The proofs, that both
--| answers are the puzzle's for every input (and windows of any size), are in
--| `Aoc.Year2021.Day01.Proofs` (Proofs/), and the tests in
--| `Aoc.Year2021.Day01.Tests` (Tests/); `run` checks neither.

namespace Aoc.Year2021.Day01
import Std (Fail, IO, List, Parse)
import Std.Parse (nat, token)

def main(): {IO, Fail} () :=
  let depths := parseDepths IO.readAll()
  IO.print "Part 1: ${solvePart1 depths}"
  IO.print "Part 2: ${solvePart2 depths}"

--| One depth per line, spaces around it allowed. Anything else fails, naming
--| the line and column.
def parseDepths (input: Text): {Fail} List Nat := Parse.eachLine input (() => token nat)

--| Part 1: each measurement against the one before it.
def solvePart1 (depths: List Nat): Nat := increasesOver 1 depths

--| Part 2: windows of three, compared through the measurement each gains and
--| the one it loses.
def solvePart2 (depths: List Nat): Nat := increasesOver 3 depths

--| How many measurements are deeper than the one `gap` places before them.
def increasesOver (gap: Nat) (depths: List Nat): Nat :=
  depths.zip (depths.drop gap) |> .count (pair => pair.fst < pair.snd)
