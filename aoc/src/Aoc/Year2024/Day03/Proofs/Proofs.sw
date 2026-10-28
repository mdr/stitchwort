-- Day 3 proved, for every list of instructions: part 2's fold adds up just
-- the results the puzzle calls enabled; without a `don't()` it is part 1;
-- and it is never more than part 1.

namespace Aoc.Year2024.Day03.Proofs
import Aoc.Year2024.Day03 (..)
import Aoc.Year2024.Day03.Spec (..)
import Std (Bool, Eq, List, Nat, Void)

-- A `mul` leaves `mul` enabled or disabled, as it was.
theorem enabledAfterMul (earlier: List Instruction) (left: Nat) (right: Nat):
    enabledAfter (List.append earlier [Mul left right]) = enabledAfter earlier :=
  rewrite List.filterMapAppend earlier [Mul left right] setting, List.appendNil (List.filterMap earlier setting) in rfl

theorem enabledAfterDo (earlier: List Instruction): enabledAfter (List.append earlier [Do]) = True :=
  rewrite List.filterMapAppend earlier [Do] setting, List.lastSnoc True (List.filterMap earlier setting) in rfl

theorem enabledAfterDont (earlier: List Instruction): enabledAfter (List.append earlier [Dont]) = False :=
  rewrite List.filterMapAppend earlier [Dont] setting, List.lastSnoc False (List.filterMap earlier setting) in rfl

-- One step of the fold, from a tally that agrees with the spec on the
-- instructions before.
theorem stepAgrees (earlier: List Instruction) (total: Nat): (instruction: Instruction) →
    step { enabled = enabledAfter earlier, total } instruction =
      { enabled = enabledAfter (List.append earlier [instruction]), total = total + (if enabledAfter earlier then result instruction else 0) }
  | Mul left right =>
    rewrite enabledAfterMul earlier left right in
      match enabled: enabledAfter earlier with
        | True => cases
        | False => rewrite Nat.addZero total in cases
  | Do =>
    rewrite enabledAfterDo earlier in
      match enabled: enabledAfter earlier with
        | True => rewrite Nat.addZero total in cases
        | False => rewrite Nat.addZero total in cases
  | Dont =>
    rewrite enabledAfterDont earlier in
      match enabled: enabledAfter earlier with
        | True => rewrite Nat.addZero total in cases
        | False => rewrite Nat.addZero total in cases

-- What the instruction at `index` adds, by the spec.
def enabledResult (instructions: List Instruction) (index: Nat): Nat :=
  if enabledAfter (instructions.take index) then result (instructions.getOr index Do) else 0

-- After the first k instructions, the fold's tally is the spec's: enabled
-- as the most recent do() or don't() says, and the enabled results so far.
theorem tallyAfter (instructions: List Instruction): (k: Nat) → k ≤ instructions.length →
    List.foldLeft (instructions.take k) ({ enabled = True, total = 0 }: Tally) step =
      { enabled = enabledAfter (instructions.take k), total = List.range k |> .sumBy (enabledResult instructions) }
  | Zero, inRange => rfl
  | Succ k, inRange =>
    let before := tallyAfter instructions k (Nat.leTrans k (Succ k) instructions.length (Nat.leSucc k) inRange)
    rewrite List.foldLeftTakeSucc step Do instructions ({ enabled = True, total = 0 }: Tally) k inRange,
      before,
      stepAgrees (instructions.take k) (List.range k |> .sumBy (enabledResult instructions)) (instructions.getOr k Do),
      List.takeSucc Do instructions k inRange,
      List.sumRangeLast (enabledResult instructions) k in
      rfl

-- The spec's sum, by index.
theorem enabledResultsByIndex (instructions: List Instruction):
    enabledResults instructions = List.range instructions.length |> .sumBy (enabledResult instructions) :=
  let counted := ((index, instruction)) => if enabledAfter (instructions.take index) then result instruction else 0
  Eq.trans
    (Eq.cong (pairs => List.sumBy pairs counted) (List.withIndexRange instructions Do))
    (List.sumByMap (List.range instructions.length) counted (index => (index, instructions.getOr index Do)))

-- Part 2 adds up just the enabled results.
theorem part2Correct (instructions: List Instruction): solvePart2 instructions = enabledResults instructions :=
  let start: Tally := { enabled = True, total = 0 }
  let all := instructions.length
  calc solvePart2 instructions
    _ = (List.foldLeft (instructions.take all) start step).total :=
      Eq.cong (taken => (List.foldLeft taken start step).total) (Eq.sym (List.takeAll instructions all (Nat.leRefl all)))
    _ = List.sumBy (List.range all) (enabledResult instructions) := Eq.cong Tally.total (tallyAfter instructions all (Nat.leRefl all))
    _ = enabledResults instructions := Eq.sym (enabledResultsByIndex instructions)

-- With `mul` enabled and no `don't()` to come, the fold adds every result.
theorem foldWithoutDont: (instructions: List Instruction) → (total: Nat) → instructions.any isDont = False →
    List.foldLeft instructions ({ enabled = True, total }: Tally) step = { enabled = True, total = total + instructions.sumBy result }
  | Nil, total, noDont => rewrite Nat.addZero total in rfl
  | Cons (Mul left right) rest, total, noDont =>
    rewrite foldWithoutDont rest (total + left * right) noDont, List.sumByCons rest (Mul left right) result,
      Nat.addAssoc total (left * right) (rest.sumBy result) in
      rfl
  | Cons Do rest, total, noDont =>
    rewrite foldWithoutDont rest total noDont, List.sumByCons rest Do result in rfl
  | Cons Dont rest, total, noDont => Void.exfalso (Bool.trueNotFalse noDont)

-- Without a `don't()`, part 2 is part 1.
theorem part2WithoutDont (instructions: List Instruction) (noDont: instructions.any isDont = False):
    solvePart2 instructions = solvePart1 instructions :=
  rewrite foldWithoutDont instructions 0 noDont in cases

-- One step adds at most the instruction's result.
theorem stepAtMost (tally: Tally): (instruction: Instruction) → (step tally instruction).total ≤ tally.total + result instruction
  | Mul left right =>
    match enabled: tally.enabled with
      | True => cases
      | False => cases
  | Do => cases
  | Dont => cases

-- The fold adds at most every result.
theorem foldAtMost: (instructions: List Instruction) → (tally: Tally) →
    (List.foldLeft instructions tally step).total ≤ tally.total + instructions.sumBy result
  | Nil, tally => cases
  | Cons instruction rest, tally =>
    let afterRest := foldAtMost rest (step tally instruction)
    let afterFirst := stepAtMost tally instruction
    rewrite List.sumByCons rest instruction result in omega

-- Part 2 is never more than part 1.
theorem part2AtMostPart1 (instructions: List Instruction): solvePart2 instructions ≤ solvePart1 instructions :=
  let bound := foldAtMost instructions ({ enabled = True, total = 0 }: Tally)
  omega
