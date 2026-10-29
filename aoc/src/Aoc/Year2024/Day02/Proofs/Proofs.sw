-- Day 2 proved, for every list of reports: both parts count the reports the
-- puzzle calls safe, and the dampener never loses a report that was safe
-- already.

namespace Aoc.Year2024.Day02.Proofs
import Aoc.Year2024.Day02 (..)
import Aoc.Year2024.Day02.Spec (..)
import Std (Bool, Eq, List, Nat)

-- One step rises gently: it increases, by one to three.
theorem risesGentlyUp (level: Nat) (next: Nat): risesGently level next = (level < next && differByOneToThree level next) := cases

-- One step falls gently: it decreases, by one to three.
theorem risesGentlyDown (level: Nat) (next: Nat): risesGently next level = (level > next && differByOneToThree level next) := cases

-- Every step rises gently: the levels are all increasing, and adjacent ones
-- differ by one to three.
theorem allRiseGently (levels: List Nat):
    levels.chain risesGently = (allIncreasing levels && adjacentDifferByOneToThree levels) :=
  Eq.trans
    (List.chainCong levels risesGently (level next => level < next && differByOneToThree level next) risesGentlyUp)
    (List.chainAnd levels (level next => level < next) differByOneToThree)

-- Every step falls gently: all decreasing, and adjacent ones differ by one to
-- three.
theorem allFallGently (levels: List Nat):
    levels.chain (level next => risesGently next level) = (allDecreasing levels && adjacentDifferByOneToThree levels) :=
  Eq.trans
    (List.chainCong levels (level next => risesGently next level) (level next => level > next && differByOneToThree level next) risesGentlyDown)
    (List.chainAnd levels (level next => level > next) differByOneToThree)

-- The program's check is the puzzle's rules.
theorem isSafeCorrect (report: Report): report.isSafe = safe report :=
  rewrite allRiseGently report.levels, allFallGently report.levels in cases

-- Part 1 counts the safe reports.
theorem part1Correct (reports: List Report): solvePart1 reports = safeReports reports :=
  List.countCongMem reports Report.isSafe safe (report _ => isSafeCorrect report)

-- Whatever keeps every adjacent pair of a list keeps a safe report safe.
theorem safeKept (shrink: List Nat → List Nat)
    (keeps: (levels: List Nat) → (holds: Nat → Nat → Bool) → levels.chain holds = True → (shrink levels).chain holds = True)
    (levels: List Nat) (wasSafe: safe { levels } = True): safe { levels = shrink levels } = True :=
  let differences := keeps levels differByOneToThree (Bool.andRight _ _ wasSafe)
  match increasing: allIncreasing levels with
    | True =>
      let stillIncreasing := keeps levels (level next => level < next) increasing
      cases
    | False =>
      let stillDecreasing := keeps levels (level next => level > next) (cases)
      cases

-- Removing the first level of a safe report leaves it safe.
theorem safeWithoutFirst (level: Nat) (rest: List Nat) (wasSafe: safe { levels = Cons level rest } = True): safe { levels = rest } = True :=
  safeKept List.tailOf List.chainTail (Cons level rest) wasSafe

-- Removing the last level of a safe report leaves it safe.
theorem safeWithoutLast (report: Report) (wasSafe: safe report = True): safe { levels = report.levels.init } = True :=
  safeKept List.init List.chainInit report.levels wasSafe

-- So the dampener alone finds every report that was safe already: for a
-- report with any levels, "safe, or safe with one level removed" is just "safe
-- with one level removed".
theorem dampenerAloneSuffices (level: Nat) (rest: List Nat):
    safeWithDampener { levels = Cons level rest } =
      (removals (Cons level rest) |> .any (levels => safe { levels })) :=
  match wasSafe: safe { levels = Cons level rest } with
    | True =>
      let kept := safeWithoutFirst level rest wasSafe
      cases
    | False => rfl

-- The dampener only adds safe reports: part 2's answer is at least part 1's.
theorem part2AtLeastPart1 (reports: List Report): solvePart1 reports ≤ solvePart2 reports :=
  rewrite part1Correct reports, part2Correct reports in
  List.countLeMem reports safe safeWithDampener (report _ wasSafe => rewrite wasSafe in rfl)
