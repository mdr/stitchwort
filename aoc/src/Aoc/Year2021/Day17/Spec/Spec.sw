--| Day 17 as the puzzle states it, over every whole-number velocity and
--| every number of steps. The target, velocity and probe types are the
--| program's; nothing else is shared with it. The proofs (Proofs/) show the
--| program's answers are these.

namespace Aoc.Year2021.Day17.Spec
import Aoc.Year2021.Day17 (Probe, Target, Velocity)
import Std (List, Nat)

--| Drag: the x velocity moves 1 toward 0, and stays at 0 once there.
def drag (dx: Int): Int := if 0 < dx then dx - 1 else if dx < 0 then dx + 1 else 0

--| One step: the probe moves by its velocity, drag acts on the x velocity,
--| and gravity lowers the y velocity by 1.
def move (probe: Probe): Probe := {
  position = { x = probe.position.x + probe.velocity.x, y = probe.position.y + probe.velocity.y },
  velocity = { x = drag probe.velocity.x, y = probe.velocity.y - 1 }
}

--| The probe after `n` steps, launched from (0, 0) with `velocity`.
def after (n: Nat) (velocity: Velocity): Probe := Nat.iterate n move { position = { x = 0, y = 0 }, velocity }

--| The probe is within the target area, edges included.
def Within (target: Target) (probe: Probe): Prop :=
  target.low.x ≤ probe.position.x ≤ target.high.x ∧ target.low.y ≤ probe.position.y ≤ target.high.y

--| A velocity hits if the probe is within the target after some step.
def Hits (target: Target) (velocity: Velocity): Prop := ∃ (n: Nat) => Within target (after n velocity)

--| Part 1: `height` is the highest y position reached on the trajectory of
--| any hitting velocity: some hitting velocity reaches it, at some step,
--| and none goes higher, at any step.
def Highest (target: Target) (height: Int): Prop :=
  (∃ (velocity: Velocity) => Hits target velocity ∧ (∃ (n: Nat) => (after n velocity).position.y = height))
    ∧ (∀ (velocity: Velocity) (n: Nat) => Hits target velocity → (after n velocity).position.y ≤ height)

--| Part 2: there are `count` distinct velocities that hit, and no others.
def HittingCount (target: Target) (count: Nat): Prop :=
  ∃ (velocities: List Velocity) => List.Distinct velocities
    ∧ (∀ (velocity: Velocity) => Hits target velocity ↔ velocity ∈ velocities)
    ∧ velocities.length = count
