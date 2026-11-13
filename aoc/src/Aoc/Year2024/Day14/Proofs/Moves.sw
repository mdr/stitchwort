--| Moving: the spec's robots move one tile at a time and one second at a
--| time; the program jumps straight to `position + seconds * velocity`,
--| wrapped. They agree for every robot that starts inside the space
--| (`afterCorrect`), and every robot is back where it started after
--| `width * height` seconds (`periodic`).

namespace Aoc.Year2024.Day14.Proofs
import Aoc.Common (Offset, Position)
import Aoc.Common.Proofs (positionExt, wrapIterate, wrapWithin)
import Aoc.Year2024.Day14 (..)
import Aoc.Year2024.Day14.Spec (..)
import Std (Eq, Int, Nat)

theorem negSuccIs ∀ (steps: Nat): NegSucc steps = (Succ steps).toInt * -1 := rewrite Nat.mulOne steps in rfl

--| Moving `tiles` tiles one at a time is adding `tiles` and wrapping.
theorem moveWrap ∀ (size: Nat) (x: Nat) (inside: x < size)
    (tiles: Int): move size tiles x = Int.modNat (x.toInt + tiles) size := match tiles with
      | OfNat steps =>
        rewrite iterateWrap size 1 (forward size) (y below => Int.modNatSuccWrap size y below) steps x inside,
          (ring: x.toInt + steps.toInt * 1 = x.toInt + OfNat steps)
      | NegSucc steps =>
        Eq.trans (iterateWrap size (-1) (backward size) (y below => Int.modNatPredWrap size y below) (Succ steps) x inside)
          (Eq.cong (distance => Int.modNat (x.toInt + distance) size) (Eq.sym (negSuccIs steps)))

--| One second, tile by tile, is the velocity's offset, wrapped.
theorem secondWrap ∀ (space: Space) (velocity: Offset) (position: Position) (inside: space.contains position = True):
    second space velocity position = space.wrap position velocity :=
  positionExt (second space velocity position) (space.wrap position velocity)
    (moveWrap space.height position.row (omega) velocity.rows)
    (moveWrap space.width position.column (omega) velocity.columns)

--| Seconds one at a time are wraps one at a time.
theorem iterateSecond ∀ (space: Space) (velocity: Offset)
    (seconds: Nat) (position: Position) (inside: space.contains position = True):
    seconds.iterate (second space velocity) position = seconds.iterate (here => space.wrap here velocity) position :=
  match seconds with
    | Zero => rfl
    | Succ seconds =>
      rewrite secondWrap space velocity position inside in
        iterateSecond space velocity seconds (space.wrap position velocity)
          (wrapWithin position velocity space.height space.width [tall := space.heightPositive] [wide := space.widthPositive])

--| The program's jump is the spec's seconds, one tile at a time.
theorem afterCorrect ∀ (space: Space) (seconds: Nat) (robot: Robot) (inside: space.contains robot.position = True):
    after space seconds robot = space.positionAfter seconds robot :=
  Eq.trans (iterateSecond space robot.velocity seconds robot.position inside)
    (wrapIterate robot.velocity space.height space.width [tall := space.heightPositive] [wide := space.widthPositive] seconds robot.position inside)

--| After `width * height` more seconds, every robot is where it was.
theorem periodic ∀ (space: Space) (seconds: Nat) (robot: Robot):
    space.positionAfter (seconds + space.period) robot = space.positionAfter seconds robot :=
  positionExt (space.positionAfter (seconds + space.period) robot) (space.positionAfter seconds robot)
    (rewrite Nat.mulComm space.width space.height in
      Int.modNatPeriodic space.height space.width robot.position.row.toInt seconds robot.velocity.rows)
    (Int.modNatPeriodic space.width space.height robot.position.column.toInt seconds robot.velocity.columns)
