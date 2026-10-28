-- Day 6's tests: the example from the puzzle and unit tests. Kept apart from
-- the program, so `stitchwort run Aoc.Year2024.Day06.main` doesn't check them.

namespace Aoc.Year2024.Day06.Tests
import Aoc.Year2024.Day06 (..)
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

def labOf (lines: List Text): Lab :=
  Fail.orElse { height = 0, width = 0, obstructions = Set.empty, start = { row = 0, column = 0 } } (() => parseLab lines)

def exampleLab: Lab := labOf example

def parsed (lines: List Text): Result Lab Text := Fail.toResult (() => parseLab lines)

def at (row: Nat) (column: Nat): Position := { row, column }

-- The guard's state after each of the first steps from the start.
def stepsFrom (lab: Lab) (guard: Guard): Nat → List Guard
  | Zero => []
  | Succ count =>
    match lab.step guard with
      | None => []
      | Some next => Cons next (stepsFrom lab next count)

test "example, part 1" := solvePart1 exampleLab == Some 41
test "example, part 2" := solvePart2 exampleLab == Some 6
test "the example's size and start" := exampleLab.height == 10 && exampleLab.width == 10 && exampleLab.start == at 6 4
test "the example's obstructions" := exampleLab.obstructions.size == 8 && exampleLab.obstructions.contains (at 0 4)
test "the example's guard doesn't loop" := !exampleLab.loops
-- The six positions the puzzle shows for the new obstruction.
test "the example's six trapping positions" :=
  [at 6 3, at 7 6, at 7 7, at 8 1, at 8 3, at 9 7].all (position => (exampleLab.withObstruction position).loops)
test "a position off the route doesn't trap" := !(exampleLab.withObstruction (at 0 0)).loops
test "the guard turns at the first obstruction" :=
  stepsFrom exampleLab exampleLab.startGuard 6 |> .map (guard => (guard.position, guard.facing))
    == [(at 5 4, Up), (at 4 4, Up), (at 3 4, Up), (at 2 4, Up), (at 1 4, Up), (at 1 4, Right)]
test "the next turn is short of the obstruction ahead" :=
  (Sightlines.of exampleLab.obstructions).nextTurn exampleLab.startGuard == Some ({ position = at 1 4, facing = Right })
test "no next turn with nothing ahead" :=
  (Sightlines.of exampleLab.obstructions).nextTurn { position = at 9 4, facing = Down } == None
test "turning right" := [Up, Right, Down, Left].map .turnRight == [Right, Down, Left, Up]

-- Edges of the map, and small labs.
test "a guard on the top row leaves at once" := solvePart1 (labOf ["..^.."]) == Some 1
test "turning at the edge, then leaving to the right" := solvePart1 (labOf ["..#", "...", "..^"]) == Some 2
test "turning at a wall then leaving" := solvePart1 (labOf ["#..", "^.."]) == Some 3
test "boxed in on all four sides loops" := solvePart1 (labOf [".#.", "#^#", ".#."]) == None
test "a box loops in part 2 too" := solvePart2 (labOf [".#.", "#^#", ".#."]) == None
test "a square route loops" := (labOf [".#...", "....#", ".....", "#^...", "...#."]).loops
test "one obstruction can close a square" := solvePart2 (labOf [".#...", "....#", ".....", ".^...", "...#."]) == Some 1
test "no obstruction can trap a guard in one column" := solvePart2 (labOf [".", ".", "^"]) == Some 0

-- Parsing.
test "parse the example's first row" := parsed ["..#^"] == Ok ({ height = 1, width = 4, obstructions = Set.fromList [at 0 2], start = at 0 3 })
test "a stray character" := parsed ["..", ".x", "^."] == Err "line 2: expected '.', '#' or '^', got 'x'"
test "a short line" := parsed ["...", "..", "^.."] == Err "line 2: expected 3 characters, as on the first line, got 2"
test "no guard" := parsed ["..", ".."] == Err "expected a guard (^) on the map, found none"
test "two guards" := parsed ["^.", ".^"] == Err "expected one guard (^) on the map, found several"
