-- The real puzzle input (aoc/inputs/2024/day05.txt, committed), through
-- `include`: the answers are checked on it when the tests run.
namespace Aoc.Year2024.Day05.Tests
import Aoc.Year2024.Day05 (..)
import Std (Fail, List, Nat)

def inputQueue: PrintQueue := Fail.orElse { rules = [], updates = [] } (() => parsePrintQueue (include "../../../../../inputs/2024/day05.txt"))

-- Any two different pages of the update are ordered by exactly one rule.
def orderedOneWay (precedes: Nat → Nat → Bool) (update: Update): Bool :=
  update.pages.all (page => update.pages.all (other => page == other || precedes page other != precedes other page))

-- The assumption part 2's proofs make (`Spec.StrictTotalOrderOn`), checked on
-- each update: its pages are different, any two are ordered one way, and
-- once sorted every page is ordered before every later one, so the order is
-- transitive.
def rulesOrderPages (precedes: Nat → Nat → Bool) (update: Update): Bool :=
  update.pages.distinct.length == update.pages.length && orderedOneWay precedes update && inOrder precedes (update.reorder precedes).pages

test "real input, part 1" := solvePart1 inputQueue == 4569
test "real input, part 2" := solvePart2 inputQueue == 6456
test "real input, size" := (inputQueue.rules.length, inputQueue.updates.length) == (1176, 197)
test "real input, every update has a middle page" := inputQueue.updates.all (update => update.pages.length % 2 == 1)
test "real input, the rules order each update's pages" :=
  inputQueue.updates.all (rulesOrderPages (mustPrecede (ruleSet inputQueue.rules)))
-- On all pages the rules aren't an order: some rules X|Y and Y|Z have no
-- X|Z, so only a per-update assumption holds.
test "real input, the rules aren't transitive" :=
  let precedes := mustPrecede (ruleSet inputQueue.rules)
  inputQueue.rules.any (first =>
    inputQueue.rules.any (second => first.after == second.before && first.before != second.after && !(precedes first.before second.after)))
