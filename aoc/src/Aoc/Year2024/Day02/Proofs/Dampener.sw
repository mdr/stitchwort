--| Part 2 proved: the one-pass check is the spec's "safe, or safe with some
--| one level removed", for every report.

namespace Aoc.Year2024.Day02.Proofs
import Aoc.Year2024.Day02 (..)
import Aoc.Year2024.Day02.Spec (..)
import Std (Bool, Eq, List, Nat)

--| Some one element removed, and `holds` of what is left: the spec's
--| `removals` with `.any`, in a form that unfolds one element at a time.
def anyRemoved (holds: List Nat → Bool): List Nat → Bool
  | [] => False
  | [level, ..rest] => holds rest || anyRemoved (levels => holds [level, ..levels]) rest

theorem anyRemovedIsRemovals ∀ (levels: List Nat) (holds: List Nat → Bool):
    anyRemoved holds levels = (removals levels |> .any holds) :=
  match levels with
    | [] => byComputing
    | [level, ..rest] =>
      rewrite anyRemovedIsRemovals rest (levels => holds [level, ..levels]),
          List.anyMap (removals rest) holds (Cons level)

theorem anyRemovedNever ∀ (levels: List Nat) (holds: List Nat → Bool)
    (never: ∀ (rest: List Nat) => holds rest = False):
    anyRemoved holds levels = False :=
  match levels with
    | [] => byComputing
    | [level, ..rest] =>
      rewrite never rest, anyRemovedNever rest (levels => holds [level, ..levels]) (levels => never [level, ..levels])

--| After a good step from `before` to `level`, the one pass is "passes, or
--| passes with one of `level` and the rest removed".
theorem passesDampenedAfterCorrect ∀ (ok: Nat → Nat → Bool) (before level: Nat) (rest: List Nat)
    (good: ok before level = True):
    passesDampenedAfter ok before level rest
      = ([level, ..rest].chain ok || anyRemoved (levels => [before, ..levels].chain ok) [level, ..rest]) :=
  match rest with
    | [] => byComputing
    | [next, ..rest] =>
      match step: ok level next with
        | True => rewrite passesDampenedAfterCorrect ok level next rest step, step, good then cases
        | False => rewrite anyRemovedNever rest (levels => ok before level && False) (levels => cases) then cases

--| The one pass is "passes, or passes with one level removed".
theorem passesDampenedCorrect ∀ (ok: Nat → Nat → Bool) (levels: List Nat):
    passesDampened ok levels = (levels.chain ok || anyRemoved (rest => rest.chain ok) levels) :=
  match levels with
    | [] => byComputing
    | [level] => byComputing
    | [level, next, ..rest] =>
      match step: ok level next with
        | True => rewrite passesDampenedAfterCorrect ok level next rest step, step then cases
        | False => rewrite anyRemovedNever rest (levels => False) (levels => byComputing) then cases

--| With the dampener, the program's check is the puzzle's rule.
theorem isSafeWithDampenerCorrect ∀ (report: Report): report.isSafeWithDampener = safeWithDampener report :=
  rewrite <- isSafeCorrect report,
      List.anyCong (removals report.levels) (levels => safe { levels }) (levels => Report.isSafe { levels }) (levels =>
        Eq.flipped (isSafeCorrect { levels })),
      List.anyOr
        (levels => levels.chain risesGently)
        (levels => levels.chain (level next => risesGently next level))
        (removals report.levels),
      <- anyRemovedIsRemovals report.levels (levels => levels.chain risesGently),
      <- anyRemovedIsRemovals report.levels (levels => levels.chain (level next => risesGently next level)),
      passesDampenedCorrect risesGently report.levels,
      passesDampenedCorrect (level next => risesGently next level) report.levels then
    cases

--| Part 2 counts the reports that are safe with the dampener.
theorem part2Correct ∀ (reports: List Report): solvePart2 reports = safeReportsWithDampener reports :=
  List.countCongMem _ Report.isSafeWithDampener safeWithDampener (report _ => isSafeWithDampenerCorrect report)
