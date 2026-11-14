--| Tests for the plane: turning in each frame, steps, distances, boxes and
--| the conversions to sheets and grids.
-- Kept apart from the code, so that running a day doesn't check them.

namespace Aoc.Common.Tests
import Aoc.Common (..)
import Std (Int, List, Option)

def up (x y: Int): Coords YUp := { x, y }

def north: Heading := North

def east: Heading := East

def south: Heading := South

def west: Heading := West

def down (x y: Int): Coords YDown := { x, y }

test "north is up the page in each frame" :=
  (north.toCoords: Coords YUp) == up 0 1
    ∧ (north.toCoords: Coords YDown) == down 0 (-1)
    ∧ (east.toCoords: Coords YUp) == up 1 0
    ∧ (east.toCoords: Coords YDown) == down 1 0
test "turning right is clockwise as drawn in both frames" :=
  (up 1 0).turnRight == up 0 (-1)
    ∧ (down 1 0).turnRight == down 0 1
    ∧ (north.toCoords: Coords YUp).turnRight == (east.toCoords: Coords YUp)
    ∧ (north.toCoords: Coords YDown).turnRight == (east.toCoords: Coords YDown)
test "turning left" :=
  (up 1 0).turnLeft == up 0 1 ∧ (down 1 0).turnLeft == down 0 (-1) ∧ (up 3 (-2)).turnRight.turnLeft == up 3 (-2)
test "turned by quarters, past a full turn" :=
  (up 10 1).turned 3 == up (-1) 10 ∧ (up 10 1).turned 7 == (up 10 1).turned 3 ∧ (up 10 1).turned 4 == up 10 1
test "headings turn" :=
  north.turnRight == East ∧ north.turnLeft == West ∧ north.opposite == South ∧ west.turned 6 == East
test "a heading converts to a direction and back" :=
  headings.all (heading => heading.toDirection.toHeading == heading)
    ∧ directions.all (direction => direction.toHeading.toDirection == direction)
test "north is up, east is right" :=
  north.toDirection == Up ∧ east.toDirection == Right ∧ Direction.toHeading Down == South
test "step and moved" :=
  (up 1 2).step South == up 1 1 ∧ (up 1 2).moved West 5 == up (-4) 2 ∧ (down 1 2).moved North 5 == down 1 (-3)
test "step then the opposite step returns" :=
  headings.all (heading => (up 4 (-7)).step heading |> .step heading.opposite |> (== up 4 (-7)))
test "arithmetic" :=
  (up 1 2).plus (up 3 (-4)) == up 4 (-2)
    ∧ (up 1 2).minus (up 3 (-4)) == up (-2) 6
    ∧ (up 1 2).negate == up (-1) (-2)
    ∧ (up 1 2).times (-3) == up (-3) (-6)
    ∧ (up 5 5).plus Coords.zero == up 5 5
test "Manhattan length and distance" :=
  (up (-3) 4).manhattan == 7 ∧ (up 1 1).distance (up (-2) 5) == 7 ∧ (up 2 2).distance (up 2 2) == 0
test "a box includes its edges" :=
  let box: Box YUp := { low = up 20 (-10), high = up 30 (-5) }
  box.contains (up 20 (-5)) ∧ box.contains (up 30 (-10)) ∧ !box.contains (up 31 (-7)) ∧ !box.contains (up 25 (-4))
test "a box's top and bottom depend on the frame" :=
  let high: Box YUp := { low = up 20 (-10), high = up 30 (-5) }
  let low: Box YDown := { low = down 20 (-10), high = down 30 (-5) }
  high.top == -5 ∧ high.bottom == -10 ∧ low.top == -10 ∧ low.bottom == -5 ∧ high.left == 20 ∧ high.right == 30
test "a size holds the cells of its board" :=
  let size: Size := { height = 2, width = 3 }
  size.contains (at 1 2) ∧ !size.contains (at 2 0) ∧ !size.contains (at 0 3) ∧ size.area == 6
test "points and coordinates" :=
  let point: Point := { x = 3, y = 4 }
  point.toCoords == down 3 4
    ∧ (down 3 4).toPoint == Some point
    ∧ (down (-1) 4).toPoint == None
    ∧ (down 3 (-1)).toPoint == None
test "offsets and coordinates" := (by 2 (-3)).toCoords == down (-3) 2 ∧ (down (-3) 2).toOffset == by 2 (-3)
test "a heading's step with y down is the grid step" :=
  headings.all (heading => (heading.toCoords: Coords YDown) == heading.toDirection.offset.toCoords)
