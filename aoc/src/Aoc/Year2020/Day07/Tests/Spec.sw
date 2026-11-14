--| Day 7's specification (Spec/Spec.sw) on the puzzle's examples and the
--| real input. Part 1's spec is a proposition, so only part 2 runs.

namespace Aoc.Year2020.Day07.Tests
import Aoc.Year2020.Day07 (Rules)
import Aoc.Year2020.Day07.Spec (..)
import Std (List, Option, Result)

def specTotal (input: Text) (depth: Nat): Result (Option Nat) Text :=
  (parsed input).map (rules => bagsWithin rules.all depth shinyGold)

test "example, the spec's part 2" := specTotal example 10 == Ok (Some 32)
test "second example, the spec's part 2, deep enough" :=
  (specTotal example2 6, specTotal example2 7) == (Ok None, Ok (Some 126))
test "real input, the spec's part 2" := specTotal input 30 == Ok (Some 220149)
