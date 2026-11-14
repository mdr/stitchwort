--| Day 17's tests: the puzzle's example and unit tests.
-- Kept apart from the program, so `stitchwort run Aoc.Year2021.Day17.main`
-- doesn't check them.

namespace Aoc.Year2021.Day17.Tests
import Aoc.Year2021.Day17 (..)
import Aoc.Year2021.Day17.Spec (..)
import Std (Fail, List, Nat, Text)

def example: Text := "target area: x=20..30, y=-10..-5\n"

def exampleTarget: Target := { low = { x = 20, y = -10 }, high = { x = 30, y = -5 } }

def parsed (input: Text): Result Target Text := Fail.toResult (() => parseTarget input)

--| The first step, within `steps` steps, at which the spec's probe is in the
--| target.
def firstHit (target: Target) (velocity: Velocity): Option Nat :=
  List.range 0 (steps target + 1) |> .find (n => inTarget target (after n velocity))

test "parse the example" := parsed example == Ok exampleTarget
test "example, part 1" := solvePart1 exampleTarget == Some 45
test "example, part 2" := solvePart2 exampleTarget == 112

--| The puzzle's worked velocities: four hit, after 7, 9, 4 and 20 steps,
--| one misses; 6,9 climbs to 45.
test "example hits" :=
  [(7, 2), (6, 3), (9, 0), (6, 9)].map (((dx, dy)) => firstHit exampleTarget { x = dx, y = dy })
    == [Some 7, Some 9, Some 4, Some 20]
test "example miss" := firstHit exampleTarget { x = 17, y = -4 } == None
test "the program agrees" :=
  ([(7, 2), (6, 3), (9, 0), (6, 9), (17, -4)]: List (Int, Int)).map (((dx, dy)) =>
    hitsWithin exampleTarget (steps exampleTarget) (launch { x = dx, y = dy }))
    == [True, True, True, True, False]
test "6,9 climbs to 45" :=
  (peak { x = 6, y = 9 }, (after 9 { x = 6, y = 9 }).position.y, (after 10 { x = 6, y = 9 }).position.y) == (45, 45, 45)
test "the box and the bound" := ((candidates exampleTarget).length, steps exampleTarget) == (600, 20)

--| Drag stops at 0 and works both ways.
test "drag" := (drag 3, drag 1, drag 0, drag (-1), drag (-3)) == (2, 0, 0, 0, -2)
test "a step" :=
  step { position = { x = 1, y = 2 }, velocity = { x = -3, y = 0 } }
    == { position = { x = -2, y = 2 }, velocity = { x = -2, y = -1 } }

test "a target left of the start" :=
  parsed "target area: x=-30..-20, y=-10..-5" == Err "the target must be right of the start and below it"
test "a target above the start" :=
  parsed "target area: x=20..30, y=5..10" == Err "the target must be right of the start and below it"
test "a missing comma" := parsed "target area: x=20..30 y=-10..-5" == Err "column 22: expected ', y=', got ' y=-'"

--| The examples, proved by computing them.
theorem examplePart1: solvePart1 exampleTarget = Some 45 := rfl
theorem examplePart2: solvePart2 exampleTarget = 112 := rfl

--| `hitsCandidate`'s hypotheses hold: 7,2 is in the example's target
--| after 7 steps.
-- (the audit's random velocities never hit)
theorem exampleHitIsCandidate: { x = 7, y = 2 } ∈ candidates exampleTarget :=
  Aoc.Year2021.Day17.Proofs.hitsCandidate exampleTarget rfl rfl { x = 7, y = 2 } 7 rfl
