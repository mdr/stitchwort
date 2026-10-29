-- Day 2 part 2 in linear time, proved equal to the puzzle's rule (the spec
-- of the time, which tried every `removeAt index`; copied below as
-- `safeWithDampenerByIndex`). Since SW-881 this check is the program in
-- aoc/src/Aoc/Year2024/Day02, proved there against a `removals` spec. One pass per direction: on the
-- first bad step, only its two levels can be the one to remove.
--
--   $ stitchwort run Scratch.LinearProved.main < inputs/2024/day02.txt

namespace Scratch.LinearProved
import Aoc.Year2024.Day02 (..)
import Aoc.Year2024.Day02.Spec (..)
import Aoc.Year2024.Day02.Proofs (isSafeCorrect)
import Std (Bool, Eq, Fail, IO, List, Nat)

-- After `before` and `level` (a good step), the rest passes `ok` once at most
-- one of `level` and the rest is removed.
def tolerates (ok: Nat → Nat → Bool) (before: Nat) (level: Nat): List Nat → Bool
  | Nil => True
  | Cons next rest =>
    if ok level next then tolerates ok level next rest
    else (Cons level rest).chain ok || (ok before next && (Cons next rest).chain ok)

-- The whole report passes `ok` once at most one level is removed.
def toleratesOne (ok: Nat → Nat → Bool): List Nat → Bool
  | Nil => True
  | Cons level Nil => True
  | Cons level (Cons next rest) =>
    if ok level next then tolerates ok level next rest
    else (Cons level rest).chain ok || (Cons next rest).chain ok

def Report.isSafeLinear (report: Report): Bool :=
  toleratesOne risesGently report.levels || toleratesOne (level next => risesGently next level) report.levels

def main(): {IO, Fail} () :=
  let reports := parseReports IO.readAll()
  IO.print "Part 2 (linear, proved): ${reports.count .isSafeLinear}"

-- The spec this was proved against: safe, or safe with some `removeAt index`.
def safeWithDampenerByIndex (report: Report): Bool :=
  safe report || (List.range report.levels.length |> .any (index => safe { levels = report.levels.removeAt index }))

-- The brute force without indices: `holds` of the list with some one element
-- removed.
def anyRemoved (holds: List Nat → Bool): List Nat → Bool
  | Nil => False
  | Cons x xs => holds xs || anyRemoved (ys => holds (Cons x ys)) xs

theorem anyRemovedCong: (xs: List Nat) → (holds1: List Nat → Bool) → (holds2: List Nat → Bool) →
    ((ys: List Nat) → holds1 ys = holds2 ys) → anyRemoved holds1 xs = anyRemoved holds2 xs
  | Nil, holds1, holds2, same => rfl
  | Cons x xs, holds1, holds2, same =>
    rewrite same xs, anyRemovedCong xs (ys => holds1 (Cons x ys)) (ys => holds2 (Cons x ys)) (ys => same (Cons x ys)) in rfl

theorem anyRemovedNever: (xs: List Nat) → (holds: List Nat → Bool) → ((ys: List Nat) → holds ys = False) → anyRemoved holds xs = False
  | Nil, holds, never => rfl
  | Cons x xs, holds, never =>
    rewrite never xs, anyRemovedNever xs (ys => holds (Cons x ys)) (ys => never (Cons x ys)) in rfl

theorem anyRemovedOr: (xs: List Nat) → (holds1: List Nat → Bool) → (holds2: List Nat → Bool) →
    anyRemoved (ys => holds1 ys || holds2 ys) xs = (anyRemoved holds1 xs || anyRemoved holds2 xs)
  | Nil, holds1, holds2 => rfl
  | Cons x xs, holds1, holds2 =>
    rewrite anyRemovedOr xs (ys => holds1 (Cons x ys)) (ys => holds2 (Cons x ys)) in cases

-- Counting from `Succ start` is counting from `start` with each index moved on.
theorem anyRangeSucc (holds: Nat → Bool): (count: Nat) → (start: Nat) →
    (List.rangeFrom count (Succ start)).any holds = (List.rangeFrom count start).any (index => holds (Succ index))
  | Zero, start => rfl
  | Succ count, start => rewrite anyRangeSucc holds count (Succ start) in rfl

-- `anyRemoved` is the spec's "some `removeAt index`".
theorem anyRemovedRange: (xs: List Nat) → (holds: List Nat → Bool) →
    anyRemoved holds xs = (List.range xs.length |> .any (index => holds (xs.removeAt index)))
  | Nil, holds => rfl
  | Cons x xs, holds =>
    rewrite anyRemovedRange xs (ys => holds (Cons x ys)), anyRangeSucc (index => holds ((Cons x xs).removeAt index)) xs.length 0 in rfl

-- After a good step from `before` to `level`, `tolerates` is "passes, or
-- passes with one of `level` and the rest removed".
theorem toleratesCorrect (ok: Nat → Nat → Bool): (before: Nat) → (level: Nat) → (rest: List Nat) → ok before level = True →
    tolerates ok before level rest = ((Cons level rest).chain ok || anyRemoved (ys => (Cons before ys).chain ok) (Cons level rest))
  | before, level, Nil, good => rfl
  | before, level, Cons next rest, good =>
    match step: ok level next with
      | True =>
        let fromBefore := anyRemovedCong rest (ys => ok before level && List.chain (Cons next ys) ok)
          (ys => List.chain (Cons next ys) ok) (ys => rewrite good in rfl)
        let fromLevel := anyRemovedCong rest (ys => List.chain (Cons level (Cons next ys)) ok) (ys => List.chain (Cons next ys) ok)
          (ys => rewrite step in rfl)
        rewrite toleratesCorrect ok level next rest step, fromBefore, fromLevel in cases
      | False => rewrite anyRemovedNever rest (ys => ok before level && False) (ys => cases) in cases

-- `toleratesOne` is "passes, or passes with one level removed".
theorem toleratesOneCorrect (ok: Nat → Nat → Bool): (levels: List Nat) →
    toleratesOne ok levels = (levels.chain ok || anyRemoved (ys => ys.chain ok) levels)
  | Nil => rfl
  | Cons level Nil => rfl
  | Cons level (Cons next rest) =>
    match step: ok level next with
      | True =>
        let fromLevel := anyRemovedCong rest (ys => List.chain (Cons level (Cons next ys)) ok) (ys => List.chain (Cons next ys) ok)
          (ys => rewrite step in rfl)
        rewrite toleratesCorrect ok level next rest step, fromLevel in cases
      | False => rewrite anyRemovedNever rest (ys => False) (ys => rfl) in cases

-- The linear check is the puzzle's rule with the dampener.
theorem isSafeLinearCorrect (report: Report): report.isSafeLinear = safeWithDampenerByIndex report :=
  rewrite <- isSafeCorrect report,
    List.anyCong (List.range report.levels.length) (index => safe { levels = report.levels.removeAt index })
      (index => Report.isSafe { levels = report.levels.removeAt index }) (index => Eq.sym (isSafeCorrect { levels = report.levels.removeAt index })),
    <- anyRemovedRange report.levels (ys => Report.isSafe { levels = ys }),
    anyRemovedOr report.levels (ys => ys.chain risesGently) (ys => ys.chain (level next => risesGently next level)),
    toleratesOneCorrect risesGently report.levels, toleratesOneCorrect (level next => risesGently next level) report.levels in
  cases

-- Part 2 by the linear check counts the reports the puzzle calls safe.
theorem part2LinearCorrect (reports: List Report): reports.count .isSafeLinear = reports.count safeWithDampenerByIndex :=
  List.countCongMem reports Report.isSafeLinear safeWithDampenerByIndex (report _ => isSafeLinearCorrect report)
