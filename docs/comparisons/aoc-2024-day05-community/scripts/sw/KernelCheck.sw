-- Can the kernel prove the part 2 assumption for the real input by `rfl`?
-- The notes say evaluation in the kernel won't do it in reasonable time; this
-- measures it, a step at a time.
namespace Scratch.KernelCheck
import Aoc.Year2024.Day05 (..)
import Std (Fail, List, Nat)

def inputQueue: PrintQueue := Fail.orElse { rules = [], updates = [] } (() => parsePrintQueue (include "../../inputs/day05.txt"))

theorem parsedSize: inputQueue.updates.length = 197 := rfl

def orderedOneWay (precedes: Nat → Nat → Bool) (update: Update): Bool :=
  update.pages.all (page => update.pages.all (other => page == other || precedes page other != precedes other page))

def rulesOrderPages (precedes: Nat → Nat → Bool) (update: Update): Bool :=
  update.pages.distinct.length == update.pages.length && orderedOneWay precedes update && inOrder precedes (update.reorder precedes).pages

theorem everyUpdateOrdered: inputQueue.updates.all (rulesOrderPages (mustPrecede (ruleSet inputQueue.rules))) = True := rfl
