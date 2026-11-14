--| Points and lines, for puzzles that give coordinates: `x` across and `y`
--| down, as the puzzle writes `x,y`. A point is what the text says; to look
--| it up on a grid read from text, whose cells are counted by row and
--| column (`Position`, Grid.sw), convert it with `Point.toPosition`.
--|
--| Coordinates are `Nat`s: every puzzle here counts from a corner of the
--| sheet, floor or ocean floor, so none goes below 0, and a point converts
--| to a `Position` without loss. (A step or a velocity, which can be
--| negative, is an `Offset`, Offset.sw.) The tests are in
--| `Aoc.Common.Tests` (Tests/Point.sw).

namespace Aoc.Common
import Std (Eq, List, Nat, Ord, Pair)

--| A point `x` across from the left edge and `y` down from the top.
type Point = { x: Nat, y: Nat }

--| Ordered by `x`, then `y`, so lists and maps of points can drop repeats
--| and count them.
instance Point.instOrd: Ord Point :=
  Ord.byKey (point => (point.x, point.y)) (a b same => Point.ext a b (Eq.cong Pair.fst same) (Eq.cong Pair.snd same))

--| The position on a grid drawn with `x` as the column and `y` as the row:
--| row = `y`, column = `x`.
def Point.toPosition (point: Point): Position := { row = point.y, column = point.x }

--| A line from one point to another, both ends included. A line of one
--| point has both ends the same.
type Line = { from: Point, to: Point }

--| Both ends are in the same row: the same `y`.
def Line.isHorizontal (line: Line): Bool := line.from.y == line.to.y

--| Both ends are in the same column: the same `x`.
def Line.isVertical (line: Line): Bool := line.from.x == line.to.x

--| Horizontal or vertical (a line of one point is both).
def Line.isStraight (line: Line): Bool := line.isVertical ∨ line.isHorizontal

--| Diagonal at 45 degrees: as far across as down.
def Line.isDiagonal (line: Line): Bool := line.from.x.absDiff line.to.x == line.from.y.absDiff line.to.y

--| The coordinate `step` steps from `start` towards `stop`, one at a time.
def towards (start stop step: Nat): Nat :=
  if start < stop then start + step else if stop < start then start - step else start

--| The points a horizontal, vertical or diagonal line covers: from the
--| first end, a step at a time in each direction the line goes, to the
--| other end. (A line at another angle has grid points between its ends
--| that this misses.)
def Line.points (line: Line): List Point :=
  let steps := Nat.max (line.from.x.absDiff line.to.x) (line.from.y.absDiff line.to.y)
  List.range 0 (steps + 1)
    |> .map (step => { x = towards line.from.x line.to.x step, y = towards line.from.y line.to.y step })
