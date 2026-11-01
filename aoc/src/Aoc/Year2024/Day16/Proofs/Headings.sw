--| The compass headings and the shared grid code's directions: a heading's
--| direction (`toDirection`) is a bijection, `headingOf` its inverse, and it
--| turns as the heading does (clockwise is a right turn, counterclockwise a
--| left one). The quarter turns undo each other.

namespace Aoc.Year2024.Day16.Proofs
import Aoc.Year2024.Day16 (..)
import Aoc.Common (Direction)

--| The heading of each direction, north being up.
def headingOf: Direction → Heading
  | Up => North
  | Right => East
  | Down => South
  | Left => West

theorem headingOfDirection (heading: Heading): headingOf heading.toDirection = heading := cases

theorem directionOfHeading (direction: Direction): (headingOf direction).toDirection = direction := cases

theorem clockwiseTurnsRight (heading: Heading): heading.clockwise.toDirection = heading.toDirection.turnRight := cases

theorem counterclockwiseTurnsLeft (heading: Heading): heading.counterclockwise.toDirection = heading.toDirection.turnLeft := cases

theorem clockwiseThenCounter (facing: Heading): facing.clockwise.counterclockwise = facing := cases

theorem counterThenClockwise (facing: Heading): facing.counterclockwise.clockwise = facing := cases
