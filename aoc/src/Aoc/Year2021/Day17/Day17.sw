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
--| The puzzle input is committed in aoc/inputs/2021/.
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
import Std (Fail, IO, Int, List, Nat, Parse)
import Std.Parse (int, text)

def main(): {IO, Fail} () :=
  let target := parseTarget IO.readAll()
  match solvePart1 target with
    | Some height => IO.print "Part 1: ${height}"
    | None => IO.print "Part 1: no velocity hits"
  IO.print "Part 2: ${solvePart2 target}"

--| The target area: x from `left` to `right`, y from `bottom` to `top`,
--| each end included.
type Target = { left: Int, right: Int, bottom: Int, top: Int }

--| A launch velocity.
type Velocity = { dx: Int, dy: Int }

--| The probe: where it is, and its velocity.
type Probe = { x: Int, y: Int, dx: Int, dy: Int }

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
  { left, right, bottom, top }

def checkTarget (target: Target): {Fail} Target :=
  if placed target then target else Fail.fail "the target must be right of the start and below it"

def placed (target: Target): Bool := 0 < target.left ∧ target.top < 0

def launch (velocity: Velocity): Probe := { x = 0, y = 0, dx = velocity.dx, dy = velocity.dy }

def step (probe: Probe): Probe :=
  { x = probe.x + probe.dx, y = probe.y + probe.dy, dx = probe.dx - Int.sign probe.dx, dy = probe.dy - 1 }

def inTarget (target: Target) (probe: Probe): Bool :=
  target.left ≤ probe.x ∧ probe.x ≤ target.right ∧ target.bottom ≤ probe.y ∧ probe.y ≤ target.top

--| Past the target for good: right of it and not moving left, left of it
--| and not moving right, or below it and falling.
def past (target: Target) (probe: Probe): Bool := overshot target probe ∨ short target probe ∨ fallen target probe

def overshot (target: Target) (probe: Probe): Bool := target.right < probe.x ∧ 0 ≤ probe.dx

def short (target: Target) (probe: Probe): Bool := probe.x < target.left ∧ probe.dx ≤ 0

def fallen (target: Target) (probe: Probe): Bool := probe.y < target.bottom ∧ probe.dy < 0

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
  List.range (Int.toNat target.right)
    |> .flatMap (i => List.range (steps target) |> .map (aimed target i))

--| The `i`th x velocity from 1 and the `j`th y velocity from `bottom`.
def aimed (target: Target) (i: Nat) (j: Nat): Velocity := { dx = i.toInt + 1, dy = target.bottom + j.toInt }

def hitting (target: Target): List Velocity := candidates target |> .filter (v => hitsWithin target (steps target) (launch v))

--| 1 + 2 + … + n.
def triangle: Nat → Nat
  | 0 => 0
  | Succ n => Succ n + triangle n

--| The highest y a velocity reaches: thrown up at `dy`, the probe climbs
--| `dy`, then `dy - 1`, …, then 1; thrown flat or down, it never rises.
def peak (velocity: Velocity): Nat := triangle (Int.toNat velocity.dy)

def solvePart1 (target: Target): Option Nat := (hitting target).maximumOf peak

def solvePart2 (target: Target): Nat := (hitting target).length
