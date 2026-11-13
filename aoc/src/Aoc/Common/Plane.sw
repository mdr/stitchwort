--| The plane: whole-number `x` and `y` coordinates that can go negative, for
--| puzzles on a surface with no edge (a ship at sea, a probe in flight, a
--| claw machine's table), and the four compass headings. Rows and columns
--| on a grid are Grid.sw's `Position` and Offset.sw's `Offset`; a sheet
--| printed from `x,y` with no negative values is Point.sw's `Point`. This
--| file is for the `Int` world.
--|
--| Which way `y` grows is a type, so a day says it once and the compiler
--| keeps two frames apart: `Coords YUp` for maps and maths (north is `y`
--| increasing), `Coords YDown` for screens and printed sheets (north is `y`
--| decreasing), and `Coords Unoriented` when the puzzle has no up (two
--| equations in `X` and `Y`). Adding a `Coords YUp` to a `Coords YDown` is a
--| type error, and so is turning or stepping an `Unoriented` one: it has no
--| compass. A day may name its own alias, `type Location = Coords YUp`.
--|
--| `Heading` (north, east, south, west) and Grid.sw's `Direction` (up,
--| right, down, left) are words about the picture and don't depend on the
--| frame; `Heading.toDirection` converts. Only turning a `Coords` and
--| stepping it along a `Heading` ask the frame, and "clockwise" means
--| clockwise as drawn in both. The proofs are in `Aoc.Common.Proofs`
--| (Proofs/Plane.sw), the tests in `Aoc.Common.Tests` (Tests/Plane.sw).

namespace Aoc.Common
import Std (Bool, Int, List, Nat, Option)

--| What a frame of reference says about the plane: which way `y` grows,
--| as `1` (up the page) or `-1` (down it). Its law is all the turning
--| proofs need.
interface Frame (f: Type) = {
  --| `1` if `y` grows up the page, `-1` if it grows down.
  up: Int,
  --| The sign squares to 1.
  unit: up * up = 1
}

--| The frame where `y` grows upwards, as in maths and on a map: north is
--| `y + 1`.
type YUp = | YGrowsUp

--| The frame where `y` grows downwards, as on a screen or a printed sheet:
--| north is `y - 1`.
type YDown = | YGrowsDown

--| No frame: the puzzle has no up. Such coordinates can be added and
--| scaled but not turned, nor stepped north.
type Unoriented = | NoOrientation

instance YUp.instFrame: Frame YUp := { up = 1, unit = rfl }

instance YDown.instFrame: Frame YDown := { up = -1, unit = rfl }

--| A place in the plane, or a step across it, `x` to the right and `y` in
--| the frame `f`'s direction (up for `YUp`). Both are `Int`s, so it can lie
--| left of or below the origin; the same type is a position and a
--| displacement, as with `Offset` on a board with no edge.
type Coords (f: Type) = { x: Int, y: Int }

--| The origin, or no movement.
def Coords.zero: Coords f := { x = 0, y = 0 }

--| Coordinates added: the step `other` taken from `coords`.
def Coords.plus (coords: Coords f) (other: Coords f): Coords f := { x = coords.x + other.x, y = coords.y + other.y }

--| The step from `other` to `coords`, so that `other.plus (coords.minus other)` is `coords`.
def Coords.minus (coords: Coords f) (other: Coords f): Coords f := { x = coords.x - other.x, y = coords.y - other.y }

--| The same distance the other way.
def Coords.negate (coords: Coords f): Coords f := { x = 0 - coords.x, y = 0 - coords.y }

--| `factor` times as far.
def Coords.times (coords: Coords f) (factor: Int): Coords f := { x = coords.x * factor, y = coords.y * factor }

--| The Manhattan (taxicab) length: `|x| + |y|`. This is the distance from
--| the origin; between two places use `Coords.distance`.
def Coords.manhattan (coords: Coords f): Nat := coords.x.natAbs + coords.y.natAbs

--| The Manhattan distance between two places: the length of the step from
--| one to the other.
def Coords.distance (coords: Coords f) (other: Coords f): Nat := (coords.minus other).manhattan

--| A quarter turn clockwise as drawn about the origin, in either frame:
--| with `y` up east becomes south, `(1, 0)` becomes `(0, -1)`; with `y` down
--| it becomes `(0, 1)`, which is also south on the page.
def Coords.turnRight [auto frame: Frame f] (coords: Coords f): Coords f := { x = frame.up * coords.y, y = 0 - frame.up * coords.x }

--| A quarter turn anticlockwise as drawn about the origin.
def Coords.turnLeft [auto frame: Frame f] (coords: Coords f): Coords f := { x = 0 - frame.up * coords.y, y = frame.up * coords.x }

--| `quarters` quarter turns clockwise (a full turn is 4, so any number
--| works but only the remainder matters: `Aoc.Common.Proofs.coordsTurnedMod`).
def Coords.turned [auto frame: Frame f] (coords: Coords f) (quarters: Nat): Coords f := Nat.iterate quarters Coords.turnRight coords

--| The four compass headings, as the puzzle words them: north is towards
--| the top of the picture, whichever way the frame numbers `y`.
type Heading =
  | North
  | East
  | South
  | West

--| The four headings, clockwise from north.
def headings: List Heading := [North, East, South, West]

--| A quarter turn clockwise.
def Heading.turnRight: Heading → Heading
  | North => East
  | East => South
  | South => West
  | West => North

--| A quarter turn anticlockwise.
def Heading.turnLeft: Heading → Heading
  | North => West
  | West => South
  | South => East
  | East => North

--| A half turn.
def Heading.opposite: Heading → Heading
  | North => South
  | East => West
  | South => North
  | West => East

--| `quarters` quarter turns clockwise. A full turn is 4, so any number
--| works but only the remainder matters (`Aoc.Common.Proofs.headingTurnedMod`).
def Heading.turned (heading: Heading) (quarters: Nat): Heading := Nat.iterate quarters Heading.turnRight heading

--| The grid direction that points the same way on the page: north is up,
--| east right.
def Heading.toDirection: Heading → Direction
  | North => Up
  | East => Right
  | South => Down
  | West => Left

--| The compass heading of a grid direction: up is north.
def Direction.toHeading: Direction → Heading
  | Up => North
  | Right => East
  | Down => South
  | Left => West

--| One step of length 1 along the heading, in the frame: north is
--| `(0, 1)` with `y` up and `(0, -1)` with `y` down; east is `(1, 0)` in both.
def Heading.toCoords [auto frame: Frame f]: Heading → Coords f
  | North => { x = 0, y = frame.up }
  | East => { x = 1, y = 0 }
  | South => { x = 0, y = 0 - frame.up }
  | West => { x = -1, y = 0 }

--| One step along `heading`.
def Coords.step [auto frame: Frame f] (coords: Coords f) (heading: Heading): Coords f := coords.plus heading.toCoords

--| `distance` steps along `heading`.
def Coords.moved [auto frame: Frame f] (coords: Coords f) (heading: Heading) (distance: Nat): Coords f :=
  coords.plus (heading.toCoords.times distance.toInt)

--| A rectangle of the plane from corner `low` to corner `high`, both
--| corners included: `low.x ≤ x ≤ high.x` and `low.y ≤ y ≤ high.y`. `low`
--| is the one with the smaller coordinates, so with `y` up it is the
--| bottom left and with `y` down the top left. A box with `high` below
--| `low` in either coordinate is empty.
type Box (f: Type) = { low: Coords f, high: Coords f }

--| Whether the place is in the box, edges included.
def Box.contains (box: Box f) (coords: Coords f): Bool :=
  box.low.x ≤ coords.x ≤ box.high.x ∧ box.low.y ≤ coords.y ≤ box.high.y

--| The smallest `x`, the left edge.
def Box.left (box: Box f): Int := box.low.x

--| The largest `x`, the right edge.
def Box.right (box: Box f): Int := box.high.x

--| The edge nearest the top of the page: the largest `y` with `y` up, the
--| smallest with `y` down.
def Box.top [auto frame: Frame f] (box: Box f): Int := if 0 < frame.up then box.high.y else box.low.y

--| The edge nearest the bottom of the page: the smallest `y` with `y` up,
--| the largest with `y` down.
def Box.bottom [auto frame: Frame f] (box: Box f): Int := if 0 < frame.up then box.low.y else box.high.y

--| The size of a board counted from its top left cell: `height` rows and
--| `width` columns, so its positions are rows `0` to `height - 1` and
--| columns `0` to `width - 1`.
type Size = { height: Nat, width: Nat }

--| Whether the position is a cell of a board this size.
def Size.contains (size: Size) (position: Position): Bool := position.row < size.height ∧ position.column < size.width

--| The cells of a board this size.
def Size.area (size: Size): Nat := size.height * size.width

--| The point of a sheet, as `Coords YDown`: `y` counts down from the top
--| edge, as `Point` does.
def Point.toCoords (point: Point): Coords YDown := { x = point.x.toInt, y = point.y.toInt }

--| The point at these coordinates, or `None` if `x` or `y` is negative:
--| only `YDown` coordinates are a sheet's.
def Coords.toPoint (coords: Coords YDown): Option Point := match coords.x.toNatChecked with
  | None => None
  | Some x =>
    match coords.y.toNatChecked with
      | None => None
      | Some y => Some { x, y }

--| The step across a grid as `Coords YDown`: `x` the columns and `y` the
--| rows, `y` down as rows are.
def Offset.toCoords (offset: Offset): Coords YDown := { x = offset.columns, y = offset.rows }

--| The grid offset of `YDown` coordinates: `x` columns, `y` rows.
def Coords.toOffset (coords: Coords YDown): Offset := { rows = coords.y, columns = coords.x }
