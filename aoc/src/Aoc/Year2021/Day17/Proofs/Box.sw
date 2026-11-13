--| Where hitting velocities are. For a target right of the start and below
--| it, a velocity that puts the probe in the target after `n` steps has
--| `1 ≤ dx ≤ right` and `bottom ≤ dy < -bottom`, and `n ≤ -2 * bottom`.

namespace Aoc.Year2021.Day17.Proofs
import Aoc.Year2021.Day17 (..)
import Std (Bool, Eq, Int, Nat, Void)

--| A probe past the target doesn't hit it.
theorem neverHits (target: Target) (probe: Probe) (gone: past target probe = True) (n: Nat) (h: inTarget target (Nat.iterate n step probe) = True): Void :=
  Bool.falseNotTrue (Eq.trans (Eq.sym (pastNever target probe gone n)) h)

--| Each bound is a way of being past the target: at the launch (too slow
--| to the right), or after the first step (too fast right, or too fast
--| down). The launch itself, at y = 0, isn't in a target below the start.
theorem dxAtLeastOne (target: Target) (right: 0 < target.left) (velocity: Velocity) (n: Nat) (h: inTarget target (flight n velocity) = True): 1 ≤ velocity.x :=
  match e: Int.leq 1 velocity.x with
    | True => rfl
    | False =>
      let slow: short target (launch velocity) = True := omega
      Void.exfalso (neverHits target (launch velocity) (Inr (Inl slow)) n h)

theorem dxAtMostRight (target: Target) (right: 0 < target.left) (velocity: Velocity) (n: Nat) (h: inTarget target (flight n velocity) = True):
    velocity.x ≤ target.right := match n with
      | 0 => omega
      | Succ m =>
        match e: Int.leq velocity.x target.right with
          | True => rfl
          | False =>
            let fast: overshot target (step (launch velocity)) = True := omega [Int.signCases velocity.x]
            Void.exfalso (neverHits target (step (launch velocity)) (Inl fast) m h)

theorem dyAtLeastBottom (target: Target) (below: target.top < 0) (velocity: Velocity) (n: Nat) (h: inTarget target (flight n velocity) = True):
    target.bottom ≤ velocity.y := match n with
      | 0 => omega
      | Succ m =>
        match e: Int.leq target.bottom velocity.y with
          | True => rfl
          | False =>
            let down: fallen target (step (launch velocity)) = True := omega
            Void.exfalso (neverHits target (step (launch velocity)) (Inr (Inr down)) m h)

--| Twice the y position after `n` steps is `n * (2 * dy + 1 - n)`.
theorem yFlight (velocity: Velocity) (n: Nat): 2 * (flight n velocity).position.y = n.toInt * (2 * velocity.y + 1 - n.toInt) :=
  rewrite yAfter n (launch velocity) in ring

--| A probe launched at `dy` is at y = 0 or above for the first `2 * dy + 1`
--| steps; from then on it is at least `n / 2` below y = 0.
theorem aboveAtFirst (velocity: Velocity) (n: Nat) (early: n.toInt ≤ 2 * velocity.y + 1): 0 ≤ (flight n velocity).position.y :=
  omega [yFlight velocity n, Int.mulNonneg n.toInt (2 * velocity.y + 1 - n.toInt) (omega) (omega)]

theorem belowLater (velocity: Velocity) (n: Nat) (late: 2 * velocity.y + 2 ≤ n.toInt): 2 * (flight n velocity).position.y ≤ -n.toInt :=
  let split: n.toInt * (2 * velocity.y + 1 - n.toInt) = -n.toInt - n.toInt * (n.toInt - 2 * velocity.y - 2) := ring
  omega [yFlight velocity n, split, Int.mulNonneg n.toInt (n.toInt - 2 * velocity.y - 2) (omega) (omega)]

--| So a hit below y = 0 comes late, and no later than `-2 * bottom`.
theorem hitLate (target: Target) (below: target.top < 0) (velocity: Velocity) (n: Nat) (h: inTarget target (flight n velocity) = True):
    2 * velocity.y + 2 ≤ n.toInt ≤ -2 * target.bottom := match e: Int.leq n.toInt (2 * velocity.y + 1) with
      | True => Void.exfalso (omega [aboveAtFirst velocity n (omega)])
      | False => Both (omega) (omega [belowLater velocity n (omega)])
