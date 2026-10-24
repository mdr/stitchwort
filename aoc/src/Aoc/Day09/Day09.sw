-- Advent of Code 2025, day 9: red tiles on a movie theatre floor. Part 1 is
-- the largest rectangle with two red tiles as opposite corners. Part 2 is
-- the largest such rectangle made only of red and green tiles: joining each
-- red tile to the next (and the last to the first) by a straight line of
-- green tiles makes a loop, and the tiles inside it are green too.
--
--   $ cd aoc && stitchwort run Aoc.Day09.main < inputs/day09.txt
--
-- The puzzle input is committed in aoc/inputs/ (D119).
--
-- Part 1 tries every pair of red tiles. Part 2 does too, but the floor is
-- about 100,000 tiles across, too big to look at tile by tile. Only the
-- columns of red tiles matter, and one column just right of each: the
-- columns in between are all alike, crossing the same lines of the loop, so
-- each looks like the one just right of the red tile's column before it.
-- The same goes for rows. So part 2 looks at the floor through those
-- columns and rows (`Floor.of`, about 500 by 500 tiles), marks the tiles
-- there that are outside the loop, and adds them up over each rectangle in
-- four lookups (`PrefixSums`, a summed-area table): a rectangle is all red
-- and green if no tile of it there is outside.
--
-- The tests are in `Aoc.Day09.Tests` (Tests/); `run` checks none of them.

namespace Aoc.Day09
import Aoc.Common (readLines)
import Std (Fail, IO, List, Nat, PrefixSums, Text)
import Std.Fail (fail)

def main(): {IO, Fail} () :=
  let tiles := parseTiles IO.readAllLines()
  IO.print "Part 1: ${solvePart1 tiles}"
  IO.print "Part 2: ${solvePart2 tiles}"

-- A tile's position: its column and its row.
type Tile = { x: Nat, y: Nat }

-- One red tile per line, in the order the loop joins them. Spaces around a
-- line or a number are allowed; anything else fails, naming the line.
def parseTiles (lines: List Text): {Fail} (List Tile) := readLines readTile lines

-- "7,1" is `{ x = 7, y = 1 }`.
def readTile (line: Text): {Fail} Tile :=
  match line.split ',' |> .map (part => part.trim.toNat) with
    | [Some x, Some y] => { x, y }
    | _ => fail "expected a red tile like 7,1, got '${line}'"

-- The number of tiles in the rectangle with these two tiles as opposite
-- corners, both included.
def area (corner: Tile) (opposite: Tile): Nat := (Nat.absDiff corner.x opposite.x + 1) * (Nat.absDiff corner.y opposite.y + 1)

-- The area of the rectangle with a pair of tiles as opposite corners.
def pairArea (corners: (Tile, Tile)): Nat := area corners.fst corners.snd

-- The largest of some areas, 0 if there are none.
def largest (areas: List Nat): Nat := areas.foldLeft Nat.max 0

-- Part 1: the largest rectangle with two red tiles as opposite corners.
def solvePart1 (tiles: List Tile): Nat := tiles.pairs |> .map pairArea |> largest

-- Part 2 ---------------------------------------------------------------------

-- The lines of the loop: from each red tile to the next, and from the last
-- back to the first.
def loopLines (tiles: List Tile): List (Tile, Tile) := List.zip tiles (List.append (List.drop 1 tiles) (List.take 1 tiles))

-- `value` is from `one` to `other`, in either order.
def isBetween (one: Nat) (other: Nat) (value: Nat): Bool := (one <= value && value <= other) || (other <= value && value <= one)

-- `value` is from `one` to `other`, `other` left out, in either order.
def isBetweenHalfOpen (one: Nat) (other: Nat) (value: Nat): Bool := (one <= value && value < other) || (other <= value && value < one)

-- The tile is on the line (a red tile at either end, or a green tile).
def isOnLine (tile: Tile) (line: (Tile, Tile)): Bool :=
  isBetween line.fst.x line.snd.x tile.x && isBetween line.fst.y line.snd.y tile.y

-- The line runs down a column right of the tile, across the tile's row:
-- from a row at or above it to a row below it, either way round. A tile
-- that isn't on the loop is inside it when an odd number of lines do that
-- (going right from it, a ray crosses the loop an odd number of times).
def crossesRightOf (tile: Tile) (line: (Tile, Tile)): Bool :=
  line.fst.x == line.snd.x && tile.x < line.fst.x && isBetweenHalfOpen line.fst.y line.snd.y tile.y

-- The tile is red or green, if `lines` are the lines of the loop that touch
-- its row (the others are no nearer to it than its row is).
def isRedOrGreen (lines: List (Tile, Tile)) (tile: Tile): Bool :=
  lines.any (isOnLine tile) || lines.count (crossesRightOf tile) % 2 == 1

-- The line touches row y.
def touchesRow (y: Nat) (line: (Tile, Tile)): Bool := isBetween line.fst.y line.snd.y y

-- The columns that matter, from the red tiles' columns: each of them and
-- the one just right of it, in order, each once. (The same for rows.)
def keyLines (values: List Nat): List Nat := List.append values (values.map Succ) |> .sort |> .dedup

-- The floor through the key columns and rows: where each key column and
-- row is (`columns`, `rows`), and how many tiles of each block of them are
-- outside the loop (`outside`: a cell is 1 for a tile outside, 0 for a
-- red or green one).
type Floor = { columns: List Nat, rows: List Nat, outside: PrefixSums }

def Floor.of (tiles: List Tile): Floor :=
  let columns := keyLines (tiles.map (tile => tile.x))
  let rows := keyLines (tiles.map (tile => tile.y))
  let lines := loopLines tiles
  let cells := rows.map (y => Floor.outsideRow (lines.filter (touchesRow y)) columns y)
  { columns, rows, outside = PrefixSums.of cells }

-- One row of the floor: 1 for each tile outside the loop.
def Floor.outsideRow (lines: List (Tile, Tile)) (columns: List Nat) (y: Nat): List Nat :=
  columns.map (x => if isRedOrGreen lines { x, y } then 0 else 1)

-- A red tile, with the positions of its column and row among the key ones.
type Corner = { tile: Tile, column: Nat, row: Nat }

def Floor.corner (floor: Floor) (tile: Tile): Corner :=
  { tile, column = floor.columns.indexOf tile.x, row = floor.rows.indexOf tile.y }

-- Every tile of the rectangle with these corners is red or green: none of
-- its key columns and rows is outside the loop.
def Floor.allRedOrGreen (floor: Floor) (corners: (Corner, Corner)): Bool :=
  let first := corners.fst
  let second := corners.snd
  floor.outside.block
    (Nat.min first.row second.row)
    (Succ (Nat.max first.row second.row))
    (Nat.min first.column second.column)
    (Succ (Nat.max first.column second.column))
    == 0

-- The area of the rectangle with a pair of corners.
def cornersArea (corners: (Corner, Corner)): Nat := area corners.fst.tile corners.snd.tile

-- Part 2: the largest rectangle with two red tiles as opposite corners that
-- is all red and green.
def solvePart2 (tiles: List Tile): Nat :=
  let floor := Floor.of tiles
  tiles.map floor.corner |> .pairs |> .filter floor.allRedOrGreen |> .map cornersArea |> largest
