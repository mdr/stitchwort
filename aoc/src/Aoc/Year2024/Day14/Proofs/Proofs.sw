-- Day 14 proved, for every list of robots that start inside the space:
-- part 1 is the spec's safety factor after 100 seconds of one-tile moves
-- (`part1Correct`); part 2's answer is the first second at which the spec's
-- robots are all on different tiles (`part2First`), and when it finds none,
-- no second ever has them so (`part2Never`), because every robot is back
-- where it started after `width * height` seconds (`periodic`, Moves.sw).

namespace Aoc.Year2024.Day14.Proofs
import Aoc.Year2024.Day14 (..)
import Aoc.Year2024.Day14.Spec (..)
import Std (And, Bool, Eq, Iff, List, Nat, Option, Void)

-- Every robot starts inside the space.
def StartInside (space: Space) (robots: List Robot): Prop := (robot: Robot) → robot ∈ robots → space.contains robot.position = True

-- The spec's positions are the program's.
theorem positionsCorrect (space: Space) (robots: List Robot) (inside: StartInside space robots) (seconds: Nat):
    robots.map (after space seconds) = space.positionsAfter seconds robots :=
  List.mapCongMem robots (after space seconds) (space.positionAfter seconds) (robot member => afterCorrect space seconds robot (inside robot member))

-- Part 1: the program's safety factor is the spec's, for spaces of odd
-- width and height as the puzzle's are.
theorem part1Correct (space: Space) (robots: List Robot) (inside: StartInside space robots)
    (oddWidth: space.width % 2 = 1) (oddHeight: space.height % 2 = 1): solvePart1 space robots = part1 space robots :=
  rewrite positionsCorrect space robots inside 100 in Eq.sym (safetyFactorCorrect space oddWidth oddHeight (space.positionsAfter 100 robots))

-- After any number of laps of `width * height` seconds, every robot is
-- where it was.
theorem periodicLaps (space: Space) (seconds: Nat) (robot: Robot):
    (laps: Nat) → space.positionAfter (seconds + laps * space.period) robot = space.positionAfter seconds robot
  | Zero => rewrite Nat.addZero seconds in rfl
  | Succ laps =>
    rewrite (omega: seconds + Succ laps * space.period = seconds + laps * space.period + space.period),
      periodic space (seconds + laps * space.period) robot
    in periodicLaps space seconds robot laps

theorem periodPositive (space: Space): space.period ≠ 0 := mulNeZero space.width space.height space.widthPositive space.heightPositive

-- Only the seconds modulo the period matter.
theorem positionsModPeriod (space: Space) (robots: List Robot) (seconds: Nat) (ok: space.period ≠ 0):
    space.positionsAfter seconds robots = space.positionsAfter (seconds % space.period) robots :=
  Eq.trans
    (Eq.cong (time => space.positionsAfter time robots)
      (omega [Nat.divModEq seconds space.period ok]: seconds = seconds % space.period + seconds / space.period * space.period))
    (List.mapCong robots (space.positionAfter (seconds % space.period + seconds / space.period * space.period)) (space.positionAfter (seconds % space.period))
      (robot => periodicLaps space (seconds % space.period) robot (seconds / space.period)))

theorem pictureAllDistinct (space: Space) (robots: List Robot) (inside: StartInside space robots) (seconds: Nat)
    (picture: isPicture space robots seconds): List.allDistinct (space.positionsAfter seconds robots) = True :=
  (List.allDistinctCorrect (space.positionsAfter seconds robots)).backward (rewrite <- positionsCorrect space robots inside seconds in picture)

-- Part 2's answer is a picture, and no earlier second is.
theorem part2First (space: Space) (robots: List Robot) (inside: StartInside space robots) (found: Nat)
    (h: solvePart2 space robots = Some found):
    And (isPicture space robots found) ((earlier: Nat) → earlier < found → Not (isPicture space robots earlier)) :=
  match List.findRangeSome (seconds => List.allDistinct (space.positionsAfter seconds robots)) space.period found h with
    | Both passes (Both below first) =>
      Both (rewrite positionsCorrect space robots inside found in (List.allDistinctCorrect (space.positionsAfter found robots)).forward passes)
        (earlier before picture => Bool.trueNotFalse (Eq.trans (Eq.sym (pictureAllDistinct space robots inside earlier picture)) (first earlier before)))

-- When part 2 finds nothing, no second is a picture.
theorem part2Never (space: Space) (robots: List Robot) (inside: StartInside space robots) (h: solvePart2 space robots = None)
    (seconds: Nat): Not (isPicture space robots seconds) :=
  picture =>
    let ok: space.period ≠ 0 := periodPositive space
    Bool.trueNotFalse
      (Eq.trans
        (Eq.sym (rewrite <- positionsModPeriod space robots seconds ok in pictureAllDistinct space robots inside seconds picture))
        (List.findRangeNone (later => List.allDistinct (space.positionsAfter later robots)) space.period h (seconds % space.period)
          (Nat.modLess seconds space.period ok)))
