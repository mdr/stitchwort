--| The parser keeps the promise the answers' theorems assume: a target it
--| reads is right of the start and below it, so both answers' theorems
--| hold of whatever `parseTarget` reads, with no hypothesis left.
-- (D2108)

namespace Aoc.Year2021.Day17.Proofs
import Aoc.Year2021.Day17 (..)
import Aoc.Year2021.Day17.Spec (..)
import Std (Bool, Eq, Fail, Result, Void)

--| `checkTarget` passes its target on unchanged, and only if it is right
--| of the start and below it.
theorem checkTargetOk ∀ (target checked: Target)
    (h: Fail.toResult (() => checkTarget target) = Ok checked):
    0 < checked.left ∧ checked.top < 0 :=
  match e: placed target with | True => rewrite <- Result.okInjective h in omega

--| Whatever reads the target, `checkTarget` passes on only placed ones.
theorem checkedPlaced ∀ (read: () → {Fail} Target) (target: Target)
    (parsed: Fail.toResult (() => checkTarget (read ())) = Ok target):
    0 < target.left ∧ target.top < 0 :=
  let split := rewrite Fail.toResultThen read checkTarget at parsed
  Result.flatMapEqOk (Fail.toResult read) (x => Fail.toResult (() => checkTarget x)) target split (u _ checked =>
    checkTargetOk u target checked)

theorem parseTargetPlaced ∀ (input: Text) (target: Target)
    (parsed: Fail.toResult (() => parseTarget input) = Ok target):
    0 < target.left ∧ target.top < 0 :=
  checkedPlaced _ target parsed

--| Both answers from the input text: if `parseTarget` reads `input` as
--| `target`, part 2 is the number of distinct hitting velocities, and part
--| 1 the highest y any of them reaches (or none hits).
theorem part2FromInput ∀ (input: Text) (target: Target)
    (parsed: Fail.toResult (() => parseTarget input) = Ok target):
    HittingCount target (solvePart2 target) :=
  let placedOk := parseTargetPlaced input target parsed
  part2Correct target placedOk.left placedOk.right

theorem part1FromInput ∀ (input: Text) (target: Target)
    (parsed: Fail.toResult (() => parseTarget input) = Ok target) (height: Nat)
    (found: solvePart1 target = Some height):
    Highest target height.toInt :=
  let placedOk := parseTargetPlaced input target parsed
  part1Correct target placedOk.left placedOk.right height found

theorem part1NoneFromInput ∀ (input: Text) (target: Target)
    (parsed: Fail.toResult (() => parseTarget input) = Ok target)
    (found: solvePart1 target = None) (velocity: Velocity):
    ¬(Hits target velocity) :=
  let placedOk := parseTargetPlaced input target parsed
  part1None target placedOk.left placedOk.right found velocity
