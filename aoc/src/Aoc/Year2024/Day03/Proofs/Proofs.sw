--| Day 3 proved, for every list of instructions: part 2's fold adds up just
--| the results the puzzle calls enabled; without a `don't()` it is part 1;
--| and it is never more than part 1.

namespace Aoc.Year2024.Day03.Proofs
import Aoc.Year2024.Day03 (..)
import Aoc.Year2024.Day03.Spec (..)
import Std (Bool, Eq, List, Nat, Void)

--| A `mul` leaves `mul` enabled or disabled, as it was.
theorem enabledAfterMul ∀ (earlier: List Instruction) (left right: Nat):
    enabledAfter (earlier.append [Mul left right]) = enabledAfter earlier :=
  rewrite List.filterMapAppend earlier [Mul left right] setting, List.appendNil (List.filterMap earlier setting) in rfl

theorem enabledAfterDo ∀ (earlier: List Instruction): enabledAfter (earlier.append [Do]) = True :=
  rewrite List.filterMapAppend earlier [Do] setting, List.lastSnoc True (List.filterMap earlier setting) in rfl

theorem enabledAfterDont ∀ (earlier: List Instruction): enabledAfter (earlier.append [Dont]) = False :=
  rewrite List.filterMapAppend earlier [Dont] setting, List.lastSnoc False (List.filterMap earlier setting) in rfl

--| One step of the fold, from a tally that agrees with the spec on the
--| instructions before.
theorem stepAgrees ∀ (earlier: List Instruction) (total: Nat) (instruction: Instruction):
    Tally.step { enabled = enabledAfter earlier, total } instruction
      = {
        enabled = enabledAfter (earlier.append [instruction]),
        total = total + (if enabledAfter earlier then instruction.result else 0)
      } :=
  match instruction with
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

--| What the instruction at `index` adds, by the spec.
def enabledResult (instructions: List Instruction) (index: Nat): Nat :=
  if enabledAfter (instructions.take index) then (instructions.getOr index Do).result else 0

--| After the first k instructions, the fold's tally is the spec's: enabled
--| as the most recent do() or don't() says, and the enabled results so far.
theorem tallyAfter ∀ (instructions: List Instruction) (k: Nat)
    (inRange: k ≤ instructions.length):
    List.foldLeft (instructions.take k) Tally.start Tally.step
      = {
        enabled = enabledAfter (instructions.take k),
        total = List.range 0 k |> .sumBy (enabledResult instructions)
      } :=
  match k with
    | Zero => rfl
    | Succ k =>
      let before := tallyAfter instructions k (Nat.leTrans k (Succ k) instructions.length (Nat.leSucc k) inRange)
      rewrite List.foldLeftTakeSucc Tally.step Do instructions Tally.start k inRange,
          before,
          stepAgrees
            (instructions.take k)
            (List.range 0 k |> .sumBy (enabledResult instructions))
            (instructions.getOr k Do),
          List.takeSucc Do instructions k inRange,
          List.sumRangeLast (enabledResult instructions) k in
        rfl

--| The spec's sum, by index.
theorem enabledResultsByIndex ∀ (instructions: List Instruction):
    enabledResults instructions = List.range 0 instructions.length |> .sumBy (enabledResult instructions) :=
  let counted := ((index, instruction): (Nat, Instruction)) =>
    if enabledAfter (instructions.take index) then instruction.result else 0
  Eq.trans
    (Eq.cong (pairs => List.sumBy pairs counted) (List.withIndexRange instructions Do))
    (List.sumByMap (List.range 0 instructions.length) counted (index => (index, instructions.getOr index Do)))

--| Part 2 adds up just the enabled results.
theorem part2Correct ∀ (instructions: List Instruction): solvePart2 instructions = enabledResults instructions :=
  let start := Tally.start
  let all := instructions.length
  calc solvePart2 instructions
    _ = (List.foldLeft (instructions.take all) start Tally.step).total :=
      Eq.cong
        (taken => (List.foldLeft taken start Tally.step).total)
        (Eq.sym (List.takeAll instructions all (Nat.leRefl all)))
    _ = List.sumBy (List.range 0 all) (enabledResult instructions) :=
      Eq.cong Tally.total (tallyAfter instructions all (Nat.leRefl all))
    _ = enabledResults instructions := Eq.sym (enabledResultsByIndex instructions)

--| With `mul` enabled and no `don't()` to come, the fold adds every result.
theorem foldWithoutDont ∀ (instructions: List Instruction) (total: Nat)
    (noDont: instructions.any isDont = False):
    instructions.foldLeft ({ enabled = True, total }: Tally) Tally.step
      = { enabled = True, total = total + instructions.sumBy Instruction.result } :=
  match instructions with
    | [] => rewrite Nat.addZero total in rfl
    | [Mul left right, ..rest] =>
      rewrite foldWithoutDont rest (total + left * right) noDont,
          List.sumByCons rest (Mul left right) Instruction.result,
          Nat.addAssoc total (left * right) (rest.sumBy Instruction.result) in
        rfl
    | [Do, ..rest] => rewrite foldWithoutDont rest total noDont, List.sumByCons rest Do Instruction.result in rfl

--| Without a `don't()`, part 2 is part 1.
theorem part2WithoutDont ∀ (instructions: List Instruction)
    (noDont: instructions.any isDont = False):
    solvePart2 instructions = solvePart1 instructions :=
  rewrite foldWithoutDont instructions 0 noDont in cases

--| One step adds at most the instruction's result.
theorem stepAtMost ∀ (tally: Tally) (instruction: Instruction):
    (Tally.step tally instruction).total ≤ tally.total + instruction.result :=
  match instruction with
    | Mul left right =>
      match enabled: tally.enabled with
        | True => cases
        | False => cases
    | Do => cases
    | Dont => cases

--| The fold adds at most every result.
theorem foldAtMost ∀ (instructions: List Instruction) (tally: Tally):
    (instructions.foldLeft tally Tally.step).total ≤ tally.total + instructions.sumBy Instruction.result :=
  match instructions with
    | [] => cases
    | [instruction, ..rest] =>
      let afterRest := foldAtMost rest (Tally.step tally instruction)
      let afterFirst := stepAtMost tally instruction
      rewrite List.sumByCons rest instruction Instruction.result in omega

--| Part 2 is never more than part 1.
theorem part2AtMostPart1 ∀ (instructions: List Instruction): solvePart2 instructions ≤ solvePart1 instructions :=
  let bound := foldAtMost instructions Tally.start
  omega
