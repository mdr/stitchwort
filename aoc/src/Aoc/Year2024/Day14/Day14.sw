-- Advent of Code 2024, day 14: robots moving in straight lines across a
-- space that wraps round at its edges. Part 1 multiplies the numbers of
-- robots in the four quadrants after 100 seconds, leaving out the middle
-- row and column; part 2 finds the first second at which no two robots
-- share a tile (taken as the sign of the Christmas tree picture).
--
--   $ cd aoc && stitchwort run Aoc.Year2024.Day14.main < inputs/2024/day14.txt
--   $ cd aoc && stitchwort run Aoc.Year2024.Day14.main -- 11 7 < examples/2024/day14.txt
--
-- The proofs are in `Aoc.Year2024.Day14.Proofs` (Proofs/) and the tests in
-- `Aoc.Year2024.Day14.Tests` (Tests/); `run` checks neither.

namespace Aoc.Year2024.Day14
import Std (Fail, IO, Int, List, Nat, Option, Parse, Text)
import Std.Parse (int, nat, text)

-- The space is the puzzle's, 101 tiles wide and 103 tall, unless the
-- arguments give a width and a height: `-- 11 7` for the example's.
def main(): {IO, Fail} () := solveIn (spaceFrom IO.args())

def spaceFrom (args: List Text): {Fail} Space :=
  let usage := "expected no arguments, or a width and a height above 0, such as `11 7`"
  match args with
    | Nil => Space.of 101 103
    | Cons widthText (Cons heightText Nil) =>
      let width := widthText.toNat |> .getOrElse 0
      let height := heightText.toNat |> .getOrElse 0
      if widthPositive: width ≠ 0 then
        if heightPositive: height ≠ 0 then { width, height, widthPositive, heightPositive } else Fail.fail usage
      else Fail.fail usage
    | _ => Fail.fail usage

def solveIn (space: Space): {IO, Fail} () :=
  let robots := parseRobots IO.readAll()
  robots.withIndex
    |> .map (((line, robot)) => Fail.ensure (space.contains robot.position) "line ${line + 1}: the robot starts outside the space")
  IO.print "Part 1: ${solvePart1 space robots}"
  IO.print "Part 2: ${solvePart2 space robots |> .fold "none" Nat.toText}"

-- A tile: `x` tiles from the left wall, `y` from the top.
type Position = { x: Nat, y: Nat }

-- Tiles per second; positive `x` is right, positive `y` down.
type Velocity = { x: Int, y: Int }

type Robot = { position: Position, velocity: Velocity }

-- The space the robots are in, `width` tiles wide and `height` tall.
type Space = { width: Nat, height: Nat, widthPositive: width ≠ 0, heightPositive: height ≠ 0 }

def Space.of (width: Nat) (height: Nat) [auto widthPositive: width ≠ 0] [auto heightPositive: height ≠ 0]: Space :=
  { width, height, widthPositive, heightPositive }

-- One robot: "p=0,4 v=3,-3".
def robotLine(): {Parse} Robot :=
  text "p="
  let x := nat()
  text ","
  let y := nat()
  text " v="
  let dx := int()
  text ","
  let dy := int()
  { position = { x, y }, velocity = { x = dx, y = dy } }

-- One robot per line.
def parseRobots (input: Text): {Fail} (List Robot) := Parse.eachLine input robotLine

-- Whether a tile is inside the space.
def Space.contains (space: Space) (position: Position): Bool := position.x < space.width && position.y < space.height

-- `coordinate` on a line of `size` tiles that wraps round.
def wrap (size: Nat) [auto ok: size ≠ 0] (coordinate: Int): Nat := Int.modNat coordinate size

-- Where `robot` is after `seconds` seconds: each coordinate moves the
-- velocity times the seconds, wrapping round the space.
def Space.positionAfter (space: Space) (seconds: Nat) (robot: Robot): Position := {
  x = wrap space.width [ok := space.widthPositive] (robot.position.x.toInt + seconds.toInt * robot.velocity.x),
  y = wrap space.height [ok := space.heightPositive] (robot.position.y.toInt + seconds.toInt * robot.velocity.y)
}

def Space.positionsAfter (space: Space) (seconds: Nat) (robots: List Robot): List Position := robots.map (space.positionAfter seconds)

type Quadrant =
  | TopLeft
  | TopRight
  | BottomLeft
  | BottomRight

def quadrants: List Quadrant := [TopLeft, TopRight, BottomLeft, BottomRight]

-- The quadrant a tile is in; none on the middle row or column.
def Space.quadrantOf (space: Space) (position: Position): Option Quadrant :=
  let middleColumn := space.width / 2
  let middleRow := space.height / 2
  if position.x == middleColumn || position.y == middleRow then None
  else if position.y < middleRow then Some (if position.x < middleColumn then TopLeft else TopRight)
  else Some (if position.x < middleColumn then BottomLeft else BottomRight)

-- The numbers of robots in the four quadrants, multiplied.
def Space.safetyFactor (space: Space) (positions: List Position): Nat :=
  let inQuadrants := positions.filterMap space.quadrantOf
  quadrants.map (quadrant => inQuadrants.count (== quadrant)) |> .product

def solvePart1 (space: Space) (robots: List Robot): Nat := space.positionsAfter 100 robots |> space.safetyFactor

-- How long the search runs: after `width * height` seconds every robot is
-- back where it started.
def Space.period (space: Space): Nat := space.width * space.height

-- The first second at which no two robots share a tile, if there is one.
def solvePart2 (space: Space) (robots: List Robot): Option Nat :=
  List.range space.period |> .find (seconds => space.positionsAfter seconds robots |> .allDistinct)
