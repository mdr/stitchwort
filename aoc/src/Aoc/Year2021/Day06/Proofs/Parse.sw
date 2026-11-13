--| The parser keeps the puzzle's promise: every timer of a successful
--| parse is at most 8, so both parts' theorems hold of whatever
--| `parseTimers` reads.
-- (D2108)

namespace Aoc.Year2021.Day06.Proofs
import Aoc.Year2021.Day06 (..)
import Aoc.Year2021.Day06.Spec (..)
import Std (Bool, Eq, Fail, List, Option, Result, Void)

--| Part 1 from the input text: if `parseTimers` reads `input` as `fish`,
--| part 1's answer is the number of fish the puzzle's list has after 80
--| days.
theorem part1FromInput ∀ (input: Text) (fish: List Nat) (parsed: Fail.toResult (() => parseTimers input) = Ok fish):
    solvePart1 fish = fishCount 80 fish :=
  part1Correct fish (parseTimersBounded input fish parsed)

--| Part 2 from the input text, after 256 days.
theorem part2FromInput ∀ (input: Text) (fish: List Nat) (parsed: Fail.toResult (() => parseTimers input) = Ok fish):
    solvePart2 fish = fishCount 256 fish :=
  part2Correct fish (parseTimersBounded input fish parsed)

--| Every timer `parseTimers` reads is at most 8.
theorem parseTimersBounded ∀ (input: Text) (fish: List Nat) (parsed: Fail.toResult (() => parseTimers input) = Ok fish):
    fish.all (t => t ≤ 8) = True :=
  checkedBounded _ fish parsed

--| Whatever reads the timers, `checkTimers` passes on only timers of at
--| most 8.
theorem checkedBounded ∀ (read: () → {Fail} List Nat) (fish: List Nat) (parsed: Fail.toResult (() => checkTimers (read ())) = Ok fish):
    fish.all (t => t ≤ 8) = True :=
  let split := rewrite Fail.toResultThen read checkTimers at parsed
  Result.flatMapEqOk (Fail.toResult read) (x => Fail.toResult (() => checkTimers x)) fish split
    (u _ checked => checkTimersOk u fish checked)

--| `checkTimers` passes its timers on unchanged, and only if none is above 8.
theorem checkTimersOk ∀ (timers: List Nat) (checked: List Nat) (h: Fail.toResult (() => checkTimers timers) = Ok checked):
    checked.all (t => t ≤ 8) = True := match e: firstAbove8 timers with
      | Some (index, _) => Void.exfalso (Result.errNotOk h)
      | None =>
        let notAbove := List.findNoneAll timers (t => 8 < t) (List.findWithIndexFromNone (t => 8 < t) 0 timers e)
        rewrite <- Result.okInjective h, List.allCong timers (t => t ≤ 8) (t => not (8 < t)) (t => cases) in notAbove
