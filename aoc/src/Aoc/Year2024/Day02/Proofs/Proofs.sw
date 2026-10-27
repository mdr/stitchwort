-- Day 2 proved, for every list of reports: both parts count the reports the
-- puzzle calls safe, and the dampener never loses a report that was safe
-- already.

namespace Aoc.Year2024.Day02.Proofs
import Aoc.Year2024.Day02 (..)
import Aoc.Year2024.Day02.Spec (..)
import Std (Bool, List, Nat)

-- One step rises gently: it increases, by one to three.
theorem risesGentlyUp (level: Nat) (next: Nat): risesGently level next = (level < next && differByOneToThree level next) := cases

-- One step falls gently: it decreases, by one to three.
theorem risesGentlyDown (level: Nat) (next: Nat): risesGently next level = (level > next && differByOneToThree level next) := cases

-- Four conditions regrouped.
theorem shuffle (a: Bool) (b: Bool) (c: Bool) (d: Bool): ((a && b) && (c && d)) = ((a && c) && (b && d)) := cases

-- Every step rises gently: the levels are all increasing, and adjacent ones
-- differ by one to three.
theorem allRiseGently: (levels: List Nat) →
    (steps levels).all (step => risesGently step.fst step.snd) = (allIncreasing levels && adjacentDifferByOneToThree levels)
  | Nil => rfl
  | Cons level Nil => rfl
  | Cons level (Cons next rest) =>
    calc (steps (Cons level (Cons next rest))).all (step => risesGently step.fst step.snd)
      _ = (risesGently level next && (steps (Cons next rest)).all (step => risesGently step.fst step.snd)) := rfl
      _ = ((level < next && differByOneToThree level next) && (allIncreasing (Cons next rest) && adjacentDifferByOneToThree (Cons next rest)))
        := rewrite risesGentlyUp level next, allRiseGently (Cons next rest) in rfl
      _ = (allIncreasing (Cons level (Cons next rest)) && adjacentDifferByOneToThree (Cons level (Cons next rest)))
        := shuffle _ _ _ _

-- Every step falls gently: all decreasing, and adjacent ones differ by one to
-- three.
theorem allFallGently: (levels: List Nat) →
    (steps levels).all (step => risesGently step.snd step.fst) = (allDecreasing levels && adjacentDifferByOneToThree levels)
  | Nil => rfl
  | Cons level Nil => rfl
  | Cons level (Cons next rest) =>
    calc (steps (Cons level (Cons next rest))).all (step => risesGently step.snd step.fst)
      _ = (risesGently next level && (steps (Cons next rest)).all (step => risesGently step.snd step.fst)) := rfl
      _ = ((level > next && differByOneToThree level next) && (allDecreasing (Cons next rest) && adjacentDifferByOneToThree (Cons next rest)))
        := rewrite risesGentlyDown level next, allFallGently (Cons next rest) in rfl
      _ = (allDecreasing (Cons level (Cons next rest)) && adjacentDifferByOneToThree (Cons level (Cons next rest)))
        := shuffle _ _ _ _

-- The program's check is the puzzle's rules.
theorem isSafeCorrect (report: Report): isSafe report = safe report :=
  rewrite allRiseGently report.levels, allFallGently report.levels in cases

-- Part 1 counts the safe reports.
theorem part1Correct (reports: List Report): solvePart1 reports = safeReports reports :=
  List.countCongMem reports isSafe safe (report _ => isSafeCorrect report)

-- With the dampener, the program's check is the puzzle's rule.
theorem isSafeWithDampenerCorrect (report: Report): isSafeWithDampener report = safeWithDampener report :=
  let removed := (index: Nat) => ({ levels = report.levels.removeAt index }: Report)
  let indices := List.range report.levels.length
  rewrite isSafeCorrect report, List.anyMap indices isSafe removed,
    List.anyCongMem indices (index => isSafe (removed index)) (index => safe (removed index)) (index _ => isSafeCorrect (removed index))
    in rfl

-- Part 2 counts the reports that are safe with the dampener.
theorem part2Correct (reports: List Report): solvePart2 reports = safeReportsWithDampener reports :=
  List.countCongMem reports isSafeWithDampener safeWithDampener (report _ => isSafeWithDampenerCorrect report)

-- Removing the first level keeps every adjacent pair that remains.
theorem adjacentWithoutFirst (holds: Nat → Nat → Bool): (levels: List Nat) →
    everyAdjacentPair holds levels = True → everyAdjacentPair holds levels.tailOf = True
  | Nil, all => rfl
  | Cons level Nil, all => rfl
  | Cons level (Cons next more), all => Bool.andRight _ _ all

-- Removing the last level does too.
theorem adjacentWithoutLast (holds: Nat → Nat → Bool): (levels: List Nat) →
    everyAdjacentPair holds levels = True → everyAdjacentPair holds (levels.removeAt (levels.length - 1)) = True
  | Nil, all => rfl
  | Cons level Nil, all => rfl
  | Cons level (Cons next Nil), all => rfl
  | Cons level (Cons next (Cons after more)), all =>
    let first := Bool.andLeft _ _ all
    let kept := adjacentWithoutLast holds (Cons next (Cons after more)) (Bool.andRight _ _ all)
    cases

-- Whatever keeps every adjacent pair of a list keeps a safe report safe.
theorem safeKept (shrink: List Nat → List Nat)
    (keeps: (holds: Nat → Nat → Bool) → (levels: List Nat) → everyAdjacentPair holds levels = True → everyAdjacentPair holds (shrink levels) = True)
    (levels: List Nat) (wasSafe: safe { levels } = True): safe { levels = shrink levels } = True :=
  let differences := keeps differByOneToThree levels (Bool.andRight _ _ wasSafe)
  match increasing: allIncreasing levels with
    | True =>
      let stillIncreasing := keeps (level next => level < next) levels increasing
      cases
    | False =>
      let stillDecreasing := keeps (level next => level > next) levels (cases)
      cases

-- Removing the first level of a safe report leaves it safe.
theorem safeWithoutFirst (level: Nat) (rest: List Nat) (wasSafe: safe { levels = Cons level rest } = True): safe { levels = rest } = True :=
  safeKept List.tailOf adjacentWithoutFirst (Cons level rest) wasSafe

-- Removing the last level of a safe report leaves it safe.
theorem safeWithoutLast (report: Report) (wasSafe: safe report = True):
    safe { levels = report.levels.removeAt (report.levels.length - 1) } = True :=
  safeKept (levels => levels.removeAt (levels.length - 1)) adjacentWithoutLast report.levels wasSafe

-- So the dampener alone finds every report that was safe already: for a
-- report with any levels, "safe, or safe with one level removed" is just "safe
-- with one level removed".
theorem dampenerAloneSuffices (level: Nat) (rest: List Nat):
    safeWithDampener { levels = Cons level rest } =
      (List.range (Succ rest.length) |> .any (index => safe { levels = (Cons level rest).removeAt index })) :=
  match wasSafe: safe { levels = Cons level rest } with
    | True =>
      let kept := safeWithoutFirst level rest wasSafe
      cases
    | False => rfl

-- Counting what passes a weaker check counts at least as many.
theorem countAtLeast (p: a → Bool) (q: a → Bool) (weaker: (x: a) → p x = True → q x = True): (xs: List a) → xs.count p ≤ xs.count q
  | Nil => Nat.leRefl 0
  | Cons x rest =>
    let below := countAtLeast p q weaker rest
    rewrite List.countCons rest x p, List.countCons rest x q in
    match passes: p x with
      | True => rewrite weaker x passes in omega
      | False => omega

-- The dampener only adds safe reports: part 2's answer is at least part 1's.
theorem part2AtLeastPart1 (reports: List Report): solvePart1 reports ≤ solvePart2 reports :=
  countAtLeast isSafe isSafeWithDampener (report wasSafe => rewrite wasSafe in rfl) reports
