--| Day 9 as the puzzle states it, over the red tiles, for the proofs in
--| Proofs/. The tiles are the parsed input, in order.
--|
--| In plain words:
--|   - "The largest area of any rectangle you can make using two red tiles
--|     as opposite corners": the rectangles are each red tile with each
--|     later one (`rectangles`), and a rectangle's area is the number of
--|     tiles in it, both corners included (`Rectangle.area`, shared with the program:
--|     (|dx| + 1) * (|dy| + 1)).
--|   - The largest: no rectangle's area is larger, and some rectangle has it
--|     (`Largest`; 0 when there is no rectangle, with fewer than two red
--|     tiles).
--|   - Part 2: "every red tile is connected to the red tile before and after
--|     it by a straight line of green tiles", the first and the last too
--|     (`connections`), and "all of the tiles inside this loop of red and
--|     green tiles are also green". A tile on one of the straight lines is
--|     red or green (`onLoop`). A tile off them is inside the loop when a
--|     ray from it to the right crosses the loop an odd number of times
--|     (`insideLoop`): the usual test for a point inside a polygon, where a
--|     crossing is a straight line down a column right of the tile that
--|     spans its row, the line's upper end counted and its lower end not,
--|     so a ray running along a horizontal stretch of the loop counts right.
--|   - The rectangle "can only include red or green tiles": every tile of
--|     it, every row and column from one corner to the other
--|     (`allRedOrGreen`).

namespace Aoc.Year2025.Day09.Spec
import Aoc.Common (Line, Point)
import Aoc.Year2025.Day09 (Rectangle)
import Std (List, Nat)

--| `answer` is the largest of the areas: none is larger, and it is one of
--| them, or 0 if there are none.
def Largest (areas: List Nat) (answer: Nat): Prop :=
  (∀ (other: Nat) => List.Mem other areas → other ≤ answer) ∧ ((List.Mem answer areas) ∨ ((areas = []) ∧ (answer = 0)))

--| Every rectangle with two red tiles as opposite corners: each red tile
--| with each later one.
def rectangles (tiles: List Point): List Rectangle := tiles.pairs |> .map Rectangle.ofPair

--| Part 1's answer is the largest area of these rectangles.
def Part1 (tiles: List Point) (answer: Nat): Prop := Largest (rectangles tiles |> .map .area) answer

--| Each red tile with the next, and the last with the first: the straight
--| lines of the loop run between them.
def connections (tiles: List Point): List Line :=
  tiles.zip (tiles.drop 1 |> .append (tiles.take 1)) |> .map (ends => { from = ends.fst, to = ends.snd })

--| `value` is from `one` to `other` (either may be the larger).
def from (one other value: Nat): Bool := (one ≤ value ≤ other) ∨ (other ≤ value ≤ one)

--| The tile is on the straight line between two red tiles, which share a
--| column or a row: in the rectangle between them, a line one tile wide.
def onStraightLine (tile: Point) (ends: Line): Bool :=
  from ends.from.x ends.to.x tile.x ∧ from ends.from.y ends.to.y tile.y

def onLoop (tiles: List Point) (tile: Point): Bool := connections tiles |> .any (onStraightLine tile)

--| The straight line runs down a column right of the tile, and spans the
--| tile's row: its upper end is at or above the row, its lower end below.
def crossesRay (tile: Point) (ends: Line): Bool :=
  ends.from.x == ends.to.x
    ∧ tile.x < ends.from.x
    ∧ ((ends.from.y ≤ tile.y < ends.to.y) ∨ (ends.to.y ≤ tile.y < ends.from.y))

def insideLoop (tiles: List Point) (tile: Point): Bool := List.count (connections tiles) (crossesRay tile) % 2 == 1

def redOrGreen (tiles: List Point) (tile: Point): Bool := onLoop tiles tile ∨ insideLoop tiles tile

--| Every tile of the rectangle is red or green.
def allRedOrGreen (tiles: List Point) (rectangle: Rectangle): Bool :=
  List.range (Nat.min rectangle.corner.y rectangle.opposite.y) (Nat.max rectangle.corner.y rectangle.opposite.y + 1)
    |> .all (y =>
      List.range (Nat.min rectangle.corner.x rectangle.opposite.x) (Nat.max rectangle.corner.x rectangle.opposite.x + 1)
        |> .all (x => redOrGreen tiles { x, y }))

--| Part 2's answer is the largest area of the rectangles that are all red
--| and green.
def Part2 (tiles: List Point) (answer: Nat): Prop :=
  Largest (rectangles tiles |> .filter (allRedOrGreen tiles) |> .map .area) answer
