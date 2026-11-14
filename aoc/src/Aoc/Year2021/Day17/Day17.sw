--| Advent of Code 2021, day 17: a probe is launched from (0, 0) with a
--| whole-number velocity. Each step it moves by its velocity, drag moves its
--| x velocity one toward 0, and gravity lowers its y velocity by one. The
--| input is one line naming a target area, a range of x and a range of y.
--| A velocity hits if the probe is in the area after some step. Part 1 is
--| the highest y any hitting velocity reaches; part 2 counts the hitting
--| velocities.
--|
--|   $ cd aoc && stitchwort run Aoc.Year2021.Day17.main < inputs/2021/day17.txt
--|
--| The puzzle input is committed in aoc/inputs/2021/. Positions and
--| velocities are `Coords YUp` (Aoc.Common): `y` goes up, so gravity lowers
--| it; `dx` and `dy` in the comments are a velocity's `x` and `y`.
--|
--| The program tries every velocity in a box and simulates each for a
--| bounded number of steps, stopping early once the probe is past the target
--| for good. The box and the bound come from the target, which the parser
--| checks is right of the start and below it, as every puzzle input is. The
--| proofs (Proofs/) show that no velocity outside the box hits, that the
--| bounded simulation decides hitting, and so that both answers are the
--| puzzle's, over every whole-number velocity and every number of steps. The
--| tests are in `Aoc.Year2021.Day17.Tests` (Tests/). `run` checks neither.

namespace Aoc.Year2021.Day17
import Aoc.Common (Box, Coords, YUp)
import Std (Fail, IO, Int, List, Nat, Parse)
import Std.Parse (int, text)

def main(): {IO, Fail} () :=
  let target := parseTarget IO.readAll()
  IO.print "Part 1: ${solvePart1 target |> .orFail "no velocity hits the target"}"
  IO.print "Part 2: ${solvePart2 target}"

--| The target area: x from `left` to `right`, y from `bottom` to `top`,
--| each end included. `y` goes up, so the top has the larger `y`.
type Target = Box YUp

--| A launch velocity: `x` to the right and `y` up, a step per second.
type Velocity = Coords YUp

--| The probe: where it is, and its velocity.
type Probe = { position: Coords YUp, velocity: Velocity }

--| `target area: x=20..30, y=-10..-5`. Fails unless the target is right of
--| the start and below it (`0 < left`, `top < 0`), as the puzzle's targets
--| are: the search box depends on it.
def parseTarget (input: Text): {Fail} Target := checkTarget (Parse.line input readTarget)

def readTarget(): {Parse} Target :=
  text "target area: x="
  let left := int()
  text ".."
  let right := int()
  text ", y="
  let bottom := int()
  text ".."
  let top := int()
  { low = { x = left, y = bottom }, high = { x = right, y = top } }

def checkTarget (target: Target): {Fail} Target :=
  if placed target then target else Fail.fail "the target must be right of the start and below it"

def placed (target: Target): Bool := 0 < target.left ∧ target.top < 0

def launch (velocity: Velocity): Probe := { position = Coords.zero, velocity }

def step (probe: Probe): Probe := {
  position = probe.position.plus probe.velocity,
  velocity = { x = probe.velocity.x - probe.velocity.x.sign, y = probe.velocity.y - 1 }
}

def inTarget (target: Target) (probe: Probe): Bool := target.contains probe.position

--| Past the target for good: right of it and not moving left, left of it
--| and not moving right, or below it and falling.
def past (target: Target) (probe: Probe): Bool := overshot target probe ∨ short target probe ∨ fallen target probe

def overshot (target: Target) (probe: Probe): Bool := target.right < probe.position.x ∧ 0 ≤ probe.velocity.x

def short (target: Target) (probe: Probe): Bool := probe.position.x < target.left ∧ probe.velocity.x ≤ 0

def fallen (target: Target) (probe: Probe): Bool := probe.position.y < target.bottom ∧ probe.velocity.y < 0

--| Whether the probe is in the target within `steps` more steps.
def hitsWithin (target: Target): Nat → Probe → Bool
  | 0, probe => inTarget target probe
  | Succ steps, probe =>
    if inTarget target probe then True else if past target probe then False else hitsWithin target steps (step probe)

--| A hitting velocity is in the target within `2 * |bottom|` steps (a probe
--| thrown up comes back down through y = 0 a step faster than it left, and
--| from there needs fewer than `|bottom|` steps to pass `bottom`).
def steps (target: Target): Nat := Int.toNat (-2 * target.bottom)

--| The velocities that can hit: x from 1 to `right` (any more overshoots on
--| the first step) and y from `bottom` (any less falls past on the first
--| step) to `-bottom - 1` (any more comes down through y = 0 too fast).
def candidates (target: Target): List Velocity :=
  List.range 0 target.right.toNat |> .flatMap (i => List.range 0 (steps target) |> .map (aimed target i))

--| The `i`th x velocity from 1 and the `j`th y velocity from `bottom`.
def aimed (target: Target) (i j: Nat): Velocity := { x = i.toInt + 1, y = target.bottom + j.toInt }

def hitting (target: Target): List Velocity :=
  candidates target |> .filter (v => hitsWithin target (steps target) (launch v))

--| 1 + 2 + … + n.
def triangle: Nat → Nat
  | 0 => 0
  | Succ n => Succ n + triangle n

--| The highest y a velocity reaches: thrown up at `dy`, the probe climbs
--| `dy`, then `dy - 1`, …, then 1; thrown flat or down, it never rises.
def peak (velocity: Velocity): Nat := triangle velocity.y.toNat

def solvePart1 (target: Target): Option Nat := (hitting target).maximumOf peak

def solvePart2 (target: Target): Nat := (hitting target).length
