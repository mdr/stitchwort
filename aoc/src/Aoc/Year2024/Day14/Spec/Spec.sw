-- Day 14 as the puzzle states it, over the program's robots and space:
-- robots moving one tile at a time and teleporting at the edges, the
-- quadrants by how many tiles lie on each side, and, for part 2, the
-- criterion this solution takes for the picture. The proofs (Proofs/) show
-- the program computes these, for every list of robots in the space.

namespace Aoc.Year2024.Day14.Spec
import Aoc.Year2024.Day14 (..)
import Std (List, Nat)

-- "When a robot would run into an edge of the space they're in, they
-- instead teleport to the other side, effectively wrapping around the
-- edges": one tile to the right (or down) on a line of `size` tiles, and one
-- to the left (or up).
def forward (size: Nat) (coordinate: Nat): Nat := if coordinate + 1 == size then 0 else coordinate + 1

def backward (size: Nat) (coordinate: Nat): Nat := if coordinate == 0 then size - 1 else coordinate - 1

-- Moving `tiles` tiles along the line, one at a time, backwards when
-- negative.
def move (size: Nat) (tiles: Int) (coordinate: Nat): Nat :=
  match tiles with
    | OfNat steps => steps.iterate (forward size) coordinate
    | NegSucc steps => (Succ steps).iterate (backward size) coordinate

-- "x and y are given in tiles per second": one second moves the robot
-- `velocity.x` tiles across and `velocity.y` tiles down.
def second (space: Space) (velocity: Velocity) (position: Position): Position := {
  x = move space.width velocity.x position.x,
  y = move space.height velocity.y position.y
}

-- Where a robot is after `seconds` seconds, one second at a time.
def after (space: Space) (seconds: Nat) (robot: Robot): Position := seconds.iterate (second space robot.velocity) robot.position

-- "To determine the safest area, count the number of robots in each
-- quadrant after 100 seconds. Robots that are exactly in the middle
-- (horizontally or vertically) don't count as being in any quadrant": a
-- tile is in the left half when more tiles lie to its right than to its
-- left, and in the right half when fewer do; the middle column has as many
-- each side. The same for the top and bottom halves.
def isLeft (space: Space) (position: Position): Bool := position.x < space.width - 1 - position.x

def isRight (space: Space) (position: Position): Bool := space.width - 1 - position.x < position.x

def isTop (space: Space) (position: Position): Bool := position.y < space.height - 1 - position.y

def isBottom (space: Space) (position: Position): Bool := space.height - 1 - position.y < position.y

-- How many of `positions` satisfy both.
def countWhere (positions: List Position) (first: Position → Bool) (second: Position → Bool): Nat :=
  (positions.filter (position => first position && second position)).length

-- "Multiplying these together gives a total safety factor".
def safetyFactor (space: Space) (positions: List Position): Nat :=
  countWhere positions (isTop space) (isLeft space)
    * countWhere positions (isTop space) (isRight space)
    * countWhere positions (isBottom space) (isLeft space)
    * countWhere positions (isBottom space) (isRight space)

-- "What will the safety factor be after exactly 100 seconds have elapsed?"
def part1 (space: Space) (robots: List Robot): Nat := safetyFactor space (robots.map (after space 100))

-- Part 2: "very rarely, most of the robots should arrange themselves into a
-- picture of a Christmas tree. What is the fewest number of seconds that
-- must elapse for the robots to display the Easter egg?" The puzzle doesn't
-- say what the picture looks like. This solution takes the picture to be
-- the robots all on different tiles, a common heuristic: it is a criterion
-- chosen here, not something the puzzle states.
def isPicture (space: Space) (robots: List Robot) (seconds: Nat): Prop := List.Distinct (robots.map (after space seconds))
