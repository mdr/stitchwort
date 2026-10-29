-- Part 2 proved: the one-pass check is the spec's "safe, or safe with some
-- one level removed", for every report.

namespace Aoc.Year2024.Day02.Proofs
import Aoc.Year2024.Day02 (..)
import Aoc.Year2024.Day02.Spec (..)
import Std (Bool, Eq, List, Nat)

-- Some one element removed, and `holds` of what is left: the spec's
-- `removals` with `.any`, in a form that unfolds one element at a time.
def anyRemoved (holds: List Nat → Bool): List Nat → Bool
  | Nil => False
  | Cons level rest => holds rest || anyRemoved (levels => holds (Cons level levels)) rest

theorem anyRemovedIsRemovals: (levels: List Nat) → (holds: List Nat → Bool) → anyRemoved holds levels = (removals levels |> .any holds)
  | Nil, holds => rfl
  | Cons level rest, holds =>
    rewrite anyRemovedIsRemovals rest (levels => holds (Cons level levels)), List.anyMap (removals rest) holds (Cons level) in rfl

theorem anyRemovedCong: (levels: List Nat) → (holds1: List Nat → Bool) → (holds2: List Nat → Bool) →
    ((rest: List Nat) → holds1 rest = holds2 rest) → anyRemoved holds1 levels = anyRemoved holds2 levels
  | Nil, holds1, holds2, same => rfl
  | Cons level rest, holds1, holds2, same =>
    rewrite same rest,
      anyRemovedCong rest (levels => holds1 (Cons level levels)) (levels => holds2 (Cons level levels)) (levels => same (Cons level levels)) in
    rfl

theorem anyRemovedNever: (levels: List Nat) → (holds: List Nat → Bool) → ((rest: List Nat) → holds rest = False) → anyRemoved holds levels = False
  | Nil, holds, never => rfl
  | Cons level rest, holds, never =>
    rewrite never rest, anyRemovedNever rest (levels => holds (Cons level levels)) (levels => never (Cons level levels)) in rfl

-- After a good step from `before` to `level`, the one pass is "passes, or
-- passes with one of `level` and the rest removed".
theorem passesDampenedAfterCorrect (ok: Nat → Nat → Bool): (before: Nat) → (level: Nat) → (rest: List Nat) → ok before level = True →
    passesDampenedAfter ok before level rest =
      ((Cons level rest).chain ok || anyRemoved (levels => (Cons before levels).chain ok) (Cons level rest))
  | before, level, Nil, good => rfl
  | before, level, Cons next rest, good =>
    match step: ok level next with
      | True =>
        -- `step` doesn't reach inside these lambdas, so they are rewritten by hand.
        let fromBefore := anyRemovedCong rest (levels => ok before level && List.chain (Cons next levels) ok)
          (levels => List.chain (Cons next levels) ok) (levels => rewrite good in rfl)
        let fromLevel := anyRemovedCong rest (levels => List.chain (Cons level (Cons next levels)) ok)
          (levels => List.chain (Cons next levels) ok) (levels => rewrite step in rfl)
        rewrite passesDampenedAfterCorrect ok level next rest step, fromBefore, fromLevel in cases
      | False => rewrite anyRemovedNever rest (levels => ok before level && False) (levels => cases) in cases

-- The one pass is "passes, or passes with one level removed".
theorem passesDampenedCorrect (ok: Nat → Nat → Bool): (levels: List Nat) →
    passesDampened ok levels = (levels.chain ok || anyRemoved (rest => rest.chain ok) levels)
  | Nil => rfl
  | Cons level Nil => rfl
  | Cons level (Cons next rest) =>
    match step: ok level next with
      | True =>
        let fromLevel := anyRemovedCong rest (levels => List.chain (Cons level (Cons next levels)) ok)
          (levels => List.chain (Cons next levels) ok) (levels => rewrite step in rfl)
        rewrite passesDampenedAfterCorrect ok level next rest step, fromLevel in cases
      | False => rewrite anyRemovedNever rest (levels => False) (levels => rfl) in cases

-- With the dampener, the program's check is the puzzle's rule.
theorem isSafeWithDampenerCorrect (report: Report): report.isSafeWithDampener = safeWithDampener report :=
  rewrite <- isSafeCorrect report,
    List.anyCong (removals report.levels) (levels => safe { levels }) (levels => Report.isSafe { levels }) (levels => Eq.sym (isSafeCorrect { levels })),
    List.anyOr (levels => levels.chain risesGently) (levels => levels.chain (level next => risesGently next level)) (removals report.levels),
    <- anyRemovedIsRemovals report.levels (levels => levels.chain risesGently),
    <- anyRemovedIsRemovals report.levels (levels => levels.chain (level next => risesGently next level)),
    passesDampenedCorrect risesGently report.levels, passesDampenedCorrect (level next => risesGently next level) report.levels in
  cases

-- Part 2 counts the reports that are safe with the dampener.
theorem part2Correct (reports: List Report): solvePart2 reports = safeReportsWithDampener reports :=
  List.countCongMem reports Report.isSafeWithDampener safeWithDampener (report _ => isSafeWithDampenerCorrect report)
