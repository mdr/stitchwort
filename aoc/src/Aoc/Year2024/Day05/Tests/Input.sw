--| The real puzzle input (aoc/inputs/2024/day05.txt, committed), through
--| `include`: the answers are checked on it when the tests run.
namespace Aoc.Year2024.Day05.Tests
import Aoc.Year2024.Day05 (..)
import Std (Fail, List, Nat, Result, Text)

def inputQueue: Result PrintQueue Text :=
  Fail.toResult (() => parsePrintQueue (include "../../../../../inputs/2024/day05.txt"))

--| Any two different pages of the update are ordered by exactly one rule.
def orderedOneWay (precedes: Nat → Nat → Bool) (update: Update): Bool :=
  update.pages.all (page => update.pages.all (other => page == other || precedes page other != precedes other page))

--| The assumption part 2's proofs make (`Spec.StrictTotalOrderOn`), checked on
--| each update: its pages are different, any two are ordered one way, and once
--| sorted every page is ordered before every later one, so the order is
--| transitive.
def rulesOrderPages (precedes: Nat → Nat → Bool) (update: Update): Bool :=
  update.pages.unique.length == update.pages.length
    && orderedOneWay precedes update
    && inOrder precedes (update.reorder precedes).pages

test "real input, part 1" := inputQueue.map solvePart1 == Ok 4569
test "real input, part 2" := inputQueue.map solvePart2 == Ok 6456
test "real input, size" := inputQueue.map (queue => (queue.rules.length, queue.updates.length)) == Ok (1176, 197)
test "real input, every update has a middle page" :=
  inputQueue.map (queue => queue.updates.all (update => update.pages.length % 2 == 1)) == Ok True
test "real input, the rules order each update's pages" :=
  inputQueue.map (queue => queue.updates.all (rulesOrderPages (mustPrecede (ruleSet queue.rules)))) == Ok True
--| On all pages the rules aren't an order: some rules X|Y and Y|Z have no
--| X|Z, so only a per-update assumption holds.
test "real input, the rules aren't transitive" :=
  inputQueue.map (queue =>
    let precedes := mustPrecede (ruleSet queue.rules)
    queue.rules.any (first =>
      queue.rules.any (second =>
        first.after == second.before && first.before != second.after && !(precedes first.before second.after))))
    == Ok True
