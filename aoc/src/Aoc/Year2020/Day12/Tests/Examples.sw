--| Day 12's puzzle example, each action on its own, and the parser.

namespace Aoc.Year2020.Day12.Tests
import Aoc.Common (Heading)
import Aoc.Year2020.Day12 (..)
import Aoc.Year2020.Day12 (Spec)
import Std (Fail, List, Option, Result, Text)

def parsed (input: Text): Result Route Text := Fail.toResult (() => parseRoute input)

def part1 (input: Text): Result Nat Text := (parsed input).map (.shipDistance)

def part2 (input: Text): Result Nat Text := (parsed input).map (.waypointDistance)

def example: Text := """
  F10
  N3
  F7
  R90
  F11
  """

test "the example, part 1" := part1 example == Ok 25
test "the example, part 2" := part2 example == Ok 286

test "the example's instructions" :=
  (parsed example).map (.instructions)
    == Ok [
      { action = Forward, value = 10 },
      { action = Move North, value = 3 },
      { action = Forward, value = 7 },
      { action = Turn Right, value = 90 },
      { action = Forward, value = 11 }
    ]

test "the ship starts facing east" := part1 "F5" == Ok 5
test "moving doesn't turn the ship" := part1 "N3\nF4" == Ok 7
test "left 90 faces north" := (Ship.start.follow { action = Turn Left, value = 90 }).facing == North
test "left 270 is right 90" := (Ship.start.follow { action = Turn Left, value = 270 }).facing == South
test "a full turn changes nothing" := (Ship.start.follow { action = Turn Right, value = 360 }).facing == East
test "west and south count as distance" := part1 "W3\nS4" == Ok 7

test "the waypoint starts 10 east, 1 north" := part2 "F1" == Ok 11
test "R90 turns the waypoint to 1 east, 10 south" :=
  (WaypointShip.start.follow { action = Turn Right, value = 90 }).waypoint == { x = 1, y = -10 }
test "L90 turns the waypoint to 1 west, 10 north" :=
  (WaypointShip.start.follow { action = Turn Left, value = 90 }).waypoint == { x = -1, y = 10 }
test "R180 turns the waypoint about the ship" :=
  (WaypointShip.start.follow { action = Turn Right, value = 180 }).waypoint == { x = -10, y = -1 }
test "moving the waypoint doesn't move the ship" := part2 "N5" == Ok 0

test "a turn of 45 degrees is rejected" := not (parsed "L45").isOk
test "an unknown action is rejected" := not (parsed "X10").isOk

def instructions (input: Text): List Instruction := (parsed input).map (.instructions) |> .toOption |> .getOrElse []

test "the spec's ship on the example, part 1" :=
  Spec.manhattan ((instructions example).foldLeft Spec.start Spec.navigate).position == 25
test "the spec's ship on the example, part 2" :=
  Spec.manhattan ((instructions example).foldLeft Spec.steeredStart Spec.steer).position == 286
test "the spec's L270 is R90" := Spec.turned Left 270 { x = 10, y = 4 } == Spec.turned Right 90 { x = 10, y = 4 }
