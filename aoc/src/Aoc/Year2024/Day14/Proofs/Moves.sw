-- Moving: the spec's robots move one tile at a time and one second at a
-- time; the program jumps straight to `position + seconds * velocity`,
-- wrapped. They agree for every robot that starts inside the space
-- (`afterCorrect`), and every robot is back where it started after
-- `width * height` seconds (`periodic`).

namespace Aoc.Year2024.Day14.Proofs
import Aoc.Year2024.Day14 (..)
import Aoc.Year2024.Day14.Spec (..)
import Std (Eq, Int, Nat)

theorem negSuccIs (steps: Nat): NegSucc steps = (Succ steps).toInt * -1 := rewrite Nat.mulOne steps in rfl

-- Moving `tiles` tiles one at a time is adding `tiles` and wrapping.
theorem moveWrap (size: Nat) (ok: size ≠ 0) (x: Nat) (inside: x < size):
    (tiles: Int) → move size tiles x = Int.modNat (x.toInt + tiles) size [ok := ok]
  | OfNat steps =>
    rewrite iterateWrap size ok 1 (forward size) (y below => forwardWrap size ok y below) steps x inside,
      (ring: x.toInt + steps.toInt * 1 = x.toInt + OfNat steps)
  | NegSucc steps =>
    Eq.trans (iterateWrap size ok (-1) (backward size) (y below => backwardWrap size ok y below) (Succ steps) x inside)
      (Eq.cong (distance => Int.modNat (x.toInt + distance) size [ok := ok]) (Eq.sym (negSuccIs steps)))

-- Seconds one at a time move each coordinate on its own.
theorem iterateSecond (space: Space) (velocity: Velocity):
    (seconds: Nat) → (position: Position) →
    seconds.iterate (second space velocity) position = {
      x = seconds.iterate (move space.width velocity.x) position.x,
      y = seconds.iterate (move space.height velocity.y) position.y
    }
  | Zero, { x, y } => rfl
  | Succ seconds, { x, y } => iterateSecond space velocity seconds (second space velocity { x, y })

-- The program's jump is the spec's seconds, one tile at a time.
theorem afterCorrect (space: Space) (seconds: Nat) (robot: Robot) (inside: space.contains robot.position = True):
    after space seconds robot = space.positionAfter seconds robot :=
  rewrite iterateSecond space robot.velocity seconds robot.position,
    iterateWrap space.width space.widthPositive robot.velocity.x (move space.width robot.velocity.x)
      (x below => moveWrap space.width space.widthPositive x below robot.velocity.x) seconds robot.position.x omega,
    iterateWrap space.height space.heightPositive robot.velocity.y (move space.height robot.velocity.y)
      (y below => moveWrap space.height space.heightPositive y below robot.velocity.y) seconds robot.position.y omega

-- After `width * height` more seconds, every robot is where it was.
theorem periodic (space: Space) (seconds: Nat) (robot: Robot):
    space.positionAfter (seconds + space.period) robot = space.positionAfter seconds robot :=
  rewrite wrapPeriodic space.width space.widthPositive space.height robot.position.x.toInt seconds robot.velocity.x,
    Nat.mulComm space.width space.height,
    wrapPeriodic space.height space.heightPositive space.width robot.position.y.toInt seconds robot.velocity.y
  in rfl

-- On a line of `size` tiles, `size * laps` more seconds change nothing.
theorem wrapPeriodic (size: Nat) (ok: size ≠ 0) (laps: Nat) (start: Int) (seconds: Nat) (velocity: Int):
    wrap size [ok := ok] (start + (seconds + size * laps).toInt * velocity) = wrap size [ok := ok] (start + seconds.toInt * velocity) :=
  rewrite (ring: start + (seconds + size * laps).toInt * velocity = start + seconds.toInt * velocity + size.toInt * (laps.toInt * velocity))
  in Int.modNatAddMulInt (start + seconds.toInt * velocity) size [ok := ok] (laps.toInt * velocity)
