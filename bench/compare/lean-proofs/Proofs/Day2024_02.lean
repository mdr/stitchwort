import Lib

/-! 2024 day 2, ported from aoc/src/Aoc/Year2024/Day02 (program, Spec/, Proofs/).
The parser is left out: the proofs are about the reports, as in Stitchwort's. -/

namespace Day2024_02

structure Report where
  levels : List Nat

def risesGently (lower higher : Nat) : Bool := decide (lower < higher ∧ higher ≤ lower + 3)

def Report.isSafe (report : Report) : Bool :=
  report.levels.chain risesGently || report.levels.chain (fun level next => risesGently next level)

def passesDampenedAfter (ok : Nat → Nat → Bool) (before level : Nat) : List Nat → Bool
  | [] => true
  | next :: rest =>
    if ok level next then passesDampenedAfter ok level next rest
    else (level :: rest).chain ok || (ok before next && (next :: rest).chain ok)

def passesDampened (ok : Nat → Nat → Bool) : List Nat → Bool
  | [] => true
  | [_] => true
  | level :: next :: rest =>
    if ok level next then passesDampenedAfter ok level next rest
    else (level :: rest).chain ok || (next :: rest).chain ok

def Report.isSafeWithDampener (report : Report) : Bool :=
  passesDampened risesGently report.levels ||
    passesDampened (fun level next => risesGently next level) report.levels

def solvePart1 (reports : List Report) : Nat := reports.countP Report.isSafe

def solvePart2 (reports : List Report) : Nat := reports.countP Report.isSafeWithDampener

-- Spec

def allIncreasing (levels : List Nat) : Bool := levels.chain (fun level next => decide (level < next))

def allDecreasing (levels : List Nat) : Bool := levels.chain (fun level next => decide (level > next))

def differByOneToThree (level next : Nat) : Bool :=
  decide (1 ≤ (level - next) + (next - level) ∧ (level - next) + (next - level) ≤ 3)

def adjacentDifferByOneToThree (levels : List Nat) : Bool := levels.chain differByOneToThree

def safe (report : Report) : Bool :=
  (allIncreasing report.levels || allDecreasing report.levels) && adjacentDifferByOneToThree report.levels

def removals : List Nat → List (List Nat)
  | [] => []
  | level :: rest => rest :: (removals rest).map (List.cons level)

def safeWithDampener (report : Report) : Bool :=
  safe report || (removals report.levels).any (fun levels => safe { levels })

def safeReports (reports : List Report) : Nat := reports.countP safe

def safeReportsWithDampener (reports : List Report) : Nat := reports.countP safeWithDampener

-- Proofs: Proofs/Proofs.sw

theorem risesGentlyUp (level next : Nat) :
    risesGently level next = (decide (level < next) && differByOneToThree level next) := by
  rw [Bool.eq_iff_iff]
  simp only [risesGently, differByOneToThree, Bool.and_eq_true, decide_eq_true_eq]
  omega

theorem risesGentlyDown (level next : Nat) :
    risesGently next level = (decide (level > next) && differByOneToThree level next) := by
  rw [Bool.eq_iff_iff]
  simp only [risesGently, differByOneToThree, Bool.and_eq_true, decide_eq_true_eq]
  omega

theorem allRiseGently (levels : List Nat) :
    levels.chain risesGently = (allIncreasing levels && adjacentDifferByOneToThree levels) :=
  Eq.trans
    (List.chain_cong levels risesGently (fun level next => decide (level < next) && differByOneToThree level next) risesGentlyUp)
    (List.chain_and levels (fun level next => decide (level < next)) differByOneToThree)

theorem allFallGently (levels : List Nat) :
    levels.chain (fun level next => risesGently next level) = (allDecreasing levels && adjacentDifferByOneToThree levels) :=
  Eq.trans
    (List.chain_cong levels (fun level next => risesGently next level) (fun level next => decide (level > next) && differByOneToThree level next) risesGentlyDown)
    (List.chain_and levels (fun level next => decide (level > next)) differByOneToThree)

theorem isSafeCorrect (report : Report) : report.isSafe = safe report := by
  rw [Report.isSafe, allRiseGently report.levels, allFallGently report.levels, safe]
  cases allIncreasing report.levels <;> cases allDecreasing report.levels <;>
    cases adjacentDifferByOneToThree report.levels <;> rfl

theorem part1Correct (reports : List Report) : solvePart1 reports = safeReports reports :=
  List.count_cong_mem _ Report.isSafe safe (fun report _ => isSafeCorrect report)

theorem safeKept (shrink : List Nat → List Nat)
    (keeps : ∀ (levels : List Nat) (holds : Nat → Nat → Bool), levels.chain holds = true → (shrink levels).chain holds = true)
    (levels : List Nat) (wasSafe : safe { levels } = true) : safe { levels := shrink levels } = true := by
  have differences := keeps levels differByOneToThree (by simp only [safe] at wasSafe; exact (Bool.and_eq_true_iff.mp wasSafe).2)
  cases increasing : allIncreasing levels
  · have stillDecreasing := keeps levels (fun level next => decide (level > next))
      (by simp only [safe, increasing, Bool.false_or] at wasSafe; exact (Bool.and_eq_true_iff.mp wasSafe).1)
    simp only [safe, allDecreasing, adjacentDifferByOneToThree] at *
    simp [stillDecreasing, differences]
  · have stillIncreasing := keeps levels (fun level next => decide (level < next)) increasing
    simp only [safe, allIncreasing, adjacentDifferByOneToThree] at *
    simp [stillIncreasing, differences]

theorem safeWithoutFirst (level : Nat) (rest : List Nat) (wasSafe : safe { levels := level :: rest } = true) :
    safe { levels := rest } = true :=
  safeKept List.tail (fun xs h c => List.chain_tail xs h c) (level :: rest) wasSafe

theorem safeWithoutLast (report : Report) (wasSafe : safe report = true) :
    safe { levels := report.levels.dropLast } = true :=
  safeKept List.dropLast List.chain_dropLast report.levels wasSafe

theorem dampenerAloneSuffices (level : Nat) (rest : List Nat) :
    safeWithDampener { levels := level :: rest } =
      ((removals (level :: rest)).any (fun levels => safe { levels })) := by
  cases wasSafe : safe { levels := level :: rest }
  · simp [safeWithDampener, wasSafe]
  · have kept := safeWithoutFirst level rest wasSafe
    simp [safeWithDampener, wasSafe, removals, kept]

-- Part 2

def anyRemoved (holds : List Nat → Bool) : List Nat → Bool
  | [] => false
  | level :: rest => holds rest || anyRemoved (fun levels => holds (level :: levels)) rest

theorem anyRemovedIsRemovals : ∀ (levels : List Nat) (holds : List Nat → Bool),
    anyRemoved holds levels = (removals levels).any holds
  | [], _ => rfl
  | level :: rest, holds => by
    rw [anyRemoved, anyRemovedIsRemovals rest (fun levels => holds (level :: levels)), removals,
      List.any_cons, List.any_map]
    rfl

theorem anyRemovedNever : ∀ (levels : List Nat) (holds : List Nat → Bool),
    (∀ rest, holds rest = false) → anyRemoved holds levels = false
  | [], _, _ => rfl
  | level :: rest, holds, never => by
    rw [anyRemoved, never rest,
      anyRemovedNever rest (fun levels => holds (level :: levels)) (fun levels => never (level :: levels))]
    rfl

theorem passesDampenedAfterCorrect (ok : Nat → Nat → Bool) :
    ∀ (before level : Nat) (rest : List Nat), ok before level = true →
      passesDampenedAfter ok before level rest =
        ((level :: rest).chain ok || anyRemoved (fun levels => (before :: levels).chain ok) (level :: rest))
  | before, level, [], good => by
    simp [passesDampenedAfter, anyRemoved, List.chain]
  | before, level, next :: rest, good => by
    cases step : ok level next
    · have never := anyRemovedNever rest (fun levels => (before :: level :: next :: levels).chain ok)
        (fun levels => by simp [List.chain, step])
      simp only [passesDampenedAfter, step, anyRemoved, never]
      simp [List.chain, good, step]
      cases List.chain ok (level :: rest) <;> cases List.chain ok (next :: rest) <;> simp
    · have ih := passesDampenedAfterCorrect ok level next rest step
      simp only [passesDampenedAfter, step, ih, anyRemoved]
      have same : ∀ levels, (before :: level :: levels).chain ok = (level :: levels).chain ok := by
        intro levels; simp [List.chain, good]
      simp only [same]
      simp [List.chain, step]
      cases ok before next <;> cases (next :: rest).chain ok <;> simp

theorem passesDampenedCorrect (ok : Nat → Nat → Bool) : ∀ (levels : List Nat),
    passesDampened ok levels = (levels.chain ok || anyRemoved (fun rest => rest.chain ok) levels)
  | [] => rfl
  | [level] => rfl
  | level :: next :: rest => by
    cases step : ok level next
    · have never := anyRemovedNever rest (fun levels => (level :: next :: levels).chain ok)
        (fun levels => by simp [List.chain, step])
      simp only [passesDampened, step, anyRemoved, never]
      simp [List.chain, step]
      cases List.chain ok (level :: rest) <;> cases List.chain ok (next :: rest) <;> simp
    · simp only [passesDampened, step, passesDampenedAfterCorrect ok level next rest step, anyRemoved]
      simp [List.chain, step]

theorem isSafeWithDampenerCorrect (report : Report) :
    report.isSafeWithDampener = safeWithDampener report := by
  have congr : (fun levels => safe { levels := levels }) = fun levels => Report.isSafe { levels := levels } :=
    funext fun levels => (isSafeCorrect { levels := levels }).symm
  rw [safeWithDampener, ← isSafeCorrect report, congr]
  simp only [Report.isSafe, List.any_or]
  rw [← anyRemovedIsRemovals report.levels (fun levels => levels.chain risesGently),
    ← anyRemovedIsRemovals report.levels (fun levels => levels.chain (fun level next => risesGently next level))]
  rw [Report.isSafeWithDampener, passesDampenedCorrect risesGently report.levels,
    passesDampenedCorrect (fun level next => risesGently next level) report.levels]
  cases report.levels.chain risesGently <;>
    cases report.levels.chain (fun level next => risesGently next level) <;>
    cases anyRemoved (fun levels => levels.chain risesGently) report.levels <;>
    cases anyRemoved (fun levels => levels.chain (fun level next => risesGently next level)) report.levels <;> rfl

theorem part2Correct (reports : List Report) : solvePart2 reports = safeReportsWithDampener reports :=
  List.count_cong_mem _ Report.isSafeWithDampener safeWithDampener (fun report _ => isSafeWithDampenerCorrect report)

theorem part2AtLeastPart1 (reports : List Report) : solvePart1 reports ≤ solvePart2 reports := by
  rw [part1Correct reports, part2Correct reports]
  exact List.count_le_mem reports safe safeWithDampener (fun report _ wasSafe => by
    simp [safeWithDampener, wasSafe])

end Day2024_02
