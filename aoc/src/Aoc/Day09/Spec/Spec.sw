-- Day 9 as the puzzle states it, over the red tiles, for the proofs in
-- Proofs/. The tiles are the parsed input, in order.
--
-- In plain words:
--   - "The largest area of any rectangle you can make using two red tiles
--     as opposite corners": the rectangles are each red tile with each
--     later one (`rectangles`), and a rectangle's area is the number of
--     tiles in it, both corners included (`area`, shared with the program:
--     (|dx| + 1) * (|dy| + 1)).
--   - The largest: no rectangle's area is larger, and some rectangle has it
--     (`Largest`; 0 when there is no rectangle, with fewer than two red
--     tiles).
--   - Part 2: "every red tile is connected to the red tile before and after
--     it by a straight line of green tiles", the first and the last too
--     (`connections`), and "all of the tiles inside this loop of red and
--     green tiles are also green". A tile on one of the straight lines is
--     red or green (`onLoop`). A tile off them is inside the loop when a
--     ray from it to the right crosses the loop an odd number of times
--     (`insideLoop`): the usual test for a point inside a polygon, where a
--     crossing is a straight line down a column right of the tile that
--     spans its row, the line's upper end counted and its lower end not,
--     so a ray running along a horizontal stretch of the loop counts right.
--   - The rectangle "can only include red or green tiles": every tile of
--     it, every row and column from one corner to the other
--     (`allRedOrGreen`).

namespace Aoc.Day09.Spec
import Aoc.Day09 (Tile, area)
import Std (List, Nat)

-- `answer` is the largest of the areas: none is larger, and it is one of
-- them, or 0 if there are none.
def Largest (areas: List Nat) (answer: Nat): Prop :=
  And ((other: Nat) → List.Mem other areas → other ≤ answer) (Or (List.Mem answer areas) (And (areas = Nil) (answer = 0)))

-- Every rectangle with two red tiles as opposite corners: each red tile
-- with each later one.
def rectangles (tiles: List Tile): List (Tile, Tile) := tiles.pairs

-- Part 1's answer is the largest area of these rectangles.
def Part1 (tiles: List Tile) (answer: Nat): Prop := Largest (rectangles tiles |> .map (corners => area corners.fst corners.snd)) answer

-- Each red tile with the next, and the last with the first: the straight
-- lines of the loop run between them.
def connections (tiles: List Tile): List (Tile, Tile) := tiles.zip (tiles.drop 1 |> .append (tiles.take 1))

-- `value` is from `one` to `other` (either may be the larger).
def from (one: Nat) (other: Nat) (value: Nat): Bool := (one ≤ value ∧ value ≤ other) ∨ (other ≤ value ∧ value ≤ one)

-- The tile is on the straight line between two red tiles, which share a
-- column or a row: in the rectangle between them, a line one tile wide.
def onStraightLine (tile: Tile) (ends: (Tile, Tile)): Bool := from ends.fst.x ends.snd.x tile.x ∧ from ends.fst.y ends.snd.y tile.y

def onLoop (tiles: List Tile) (tile: Tile): Bool := connections tiles |> .any (onStraightLine tile)

-- The straight line runs down a column right of the tile, and spans the
-- tile's row: its upper end is at or above the row, its lower end below.
def crossesRay (tile: Tile) (ends: (Tile, Tile)): Bool :=
  ends.fst.x == ends.snd.x ∧ tile.x < ends.fst.x
    ∧ ((ends.fst.y ≤ tile.y ∧ tile.y < ends.snd.y) ∨ (ends.snd.y ≤ tile.y ∧ tile.y < ends.fst.y))

def insideLoop (tiles: List Tile) (tile: Tile): Bool := List.count (connections tiles) (crossesRay tile) % 2 == 1

def redOrGreen (tiles: List Tile) (tile: Tile): Bool := onLoop tiles tile ∨ insideLoop tiles tile

-- Every tile of the rectangle with these corners is red or green.
def allRedOrGreen (tiles: List Tile) (corners: (Tile, Tile)): Bool :=
  List.between (Nat.min corners.fst.y corners.snd.y) (Nat.max corners.fst.y corners.snd.y)
    |> .all (y => List.between (Nat.min corners.fst.x corners.snd.x) (Nat.max corners.fst.x corners.snd.x) |> .all (x => redOrGreen tiles { x, y }))

-- Part 2's answer is the largest area of the rectangles that are all red
-- and green.
def Part2 (tiles: List Tile) (answer: Nat): Prop :=
  Largest (rectangles tiles |> .filter (allRedOrGreen tiles) |> .map (corners => area corners.fst corners.snd)) answer
