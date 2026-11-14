--| Day 6's tests: the example from the puzzle and unit tests.
--
-- Kept apart from the program, so `stitchwort run Aoc.Year2024.Day06.main`
-- doesn't check them.

namespace Aoc.Year2024.Day06.Tests
import Aoc.Year2024.Day06 (..)
import Aoc.Common (Direction, Position)
import Aoc.Year2024.Day06.Spec (after, positions)
import Std (Fail, List, Option, Set, Text)

def example: List Text := """
  ....#.....
  .........#
  ..........
  ..#.......
  .......#..
  ..........
  .#..^.....
  ........#.
  #.........
  ......#...
  """.lines

def labOf (lines: List Text): Result Lab Text := Fail.toResult (() => parseLab lines)

def exampleLab: Result Lab Text := labOf example

--| A function of the example lab, or why it didn't parse: a parse failure fails the test.
def onExample (f: Lab -> a): Result a Text := exampleLab.map f

def at (row column: Nat): Position := { row, column }

def stepsFrom (lab: Lab) (guard: Guard): Nat → List Guard
  | Zero => []
  | Succ count =>
    match lab.step guard with
      | None => []
      | Some next => [next, ..stepsFrom lab next count]

test "example, part 1" := exampleLab.map solvePart1 == Ok (Some 41)
test "example, part 2" := exampleLab.map solvePart2 == Ok (Some 6)
test "the example's size and start" :=
  onExample (lab => lab.height == 10 && lab.width == 10 && lab.start == at 6 4) == Ok True
test "the example's obstructions" :=
  onExample (lab => lab.obstructions.size == 8 && lab.obstructions.contains (at 0 4)) == Ok True
test "the example's guard doesn't loop" := onExample (lab => lab.loops) == Ok False
--| The six positions the puzzle shows for the new obstruction.
test "the example's six trapping positions" :=
  onExample (lab =>
    [at 6 3, at 7 6, at 7 7, at 8 1, at 8 3, at 9 7].all (position => (lab.withObstruction position).loops))
    == Ok True
test "a position off the route doesn't trap" := onExample (lab => (lab.withObstruction (at 0 0)).loops) == Ok False
test "the guard turns at the first obstruction" :=
  onExample (lab => stepsFrom lab lab.startGuard 6 |> .map (guard => (guard.position, guard.facing)))
    == Ok [(at 5 4, Up), (at 4 4, Up), (at 3 4, Up), (at 2 4, Up), (at 1 4, Up), (at 1 4, Right)]
test "the next turn is short of the obstruction ahead" :=
  onExample (lab => (Sightlines.of lab.obstructions).nextTurn lab.startGuard)
    == Ok (Some { position = at 1 4, facing = Right })
test "no next turn with nothing ahead" :=
  onExample (lab => (Sightlines.of lab.obstructions).nextTurn { position = at 9 4, facing = Down }) == Ok None
--| The jumping loop test agrees with the step-by-step walk (still on the map
--| after `stateCount` steps, which `budgetEnough` proves is looping) for
--| every new obstruction in the example.
test "jumps agree with steps on the example" :=
  onExample (lab =>
    positions lab
      |> .all (position =>
        let blocked := lab.withObstruction position
        blocked.loops == (after blocked blocked.stateCount).isSome))
    == Ok True
test "turning right" := [Up, Right, Down, Left].map .turnRight == [Right, Down, Left, Up]

test "a guard on the top row leaves at once" := (labOf ["..^.."]).map solvePart1 == Ok (Some 1)
test "turning at the edge, then leaving to the right" := (labOf ["..#", "...", "..^"]).map solvePart1 == Ok (Some 2)
test "turning at a wall then leaving" := (labOf ["#..", "^.."]).map solvePart1 == Ok (Some 3)
test "boxed in on all four sides loops" := (labOf [".#.", "#^#", ".#."]).map solvePart1 == Ok (None)
test "a box loops in part 2 too" := (labOf [".#.", "#^#", ".#."]).map solvePart2 == Ok (None)
test "a square route loops" := (labOf [".#...", "....#", ".....", "#^...", "...#."]).map (lab => lab.loops) == Ok True
test "one obstruction can close a square" :=
  (labOf [".#...", "....#", ".....", ".^...", "...#."]).map solvePart2 == Ok (Some 1)
test "no obstruction can trap a guard in one column" := (labOf [".", ".", "^"]).map solvePart2 == Ok (Some 0)

test "parse the example's first row" :=
  labOf ["..#^"] == Ok { height = 1, width = 4, obstructions = [at 0 2].toSet, start = at 0 3 }
test "a stray character" := labOf ["..", ".x", "^."] == Err "line 2: expected '.', '#' or '^', got 'x'"
test "a short line" := labOf ["...", "..", "^.."] == Err "line 2: expected 3 characters, as on the first line, got 2"
test "no guard" := labOf ["..", ".."] == Err "expected a guard (^) on the map, found none"
test "two guards" := labOf ["^.", ".^"] == Err "expected one guard (^) on the map, found several"
