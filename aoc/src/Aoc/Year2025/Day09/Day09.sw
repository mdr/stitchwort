--| Advent of Code 2025, day 9: red tiles on a movie theatre floor. Part 1 is
--| the largest rectangle with two red tiles as opposite corners. Part 2 is
--| the largest such rectangle made only of red and green tiles: joining each
--| red tile to the next (and the last to the first) by a straight line of
--| green tiles makes a loop, and the tiles inside it are green too.
--|
--|   $ cd aoc && stitchwort run Aoc.Year2025.Day09.main < inputs/2025/day09.txt
--|
--| The puzzle input is committed in aoc/inputs/2025/.
--|
--| Part 1 tries every pair of red tiles. Part 2 does too, but the floor is
--| about 100,000 tiles across, too big to look at tile by tile. Only the
--| columns of red tiles matter, and one column just right of each: the
--| columns in between are all alike, crossing the same lines of the loop, so
--| each looks like the one just right of the red tile's column before it.
--| The same goes for rows. So part 2 looks at the floor through those
--| columns and rows (`Floor.of`, about 500 by 500 tiles), marks the tiles
--| there that are outside the loop, and adds them up over each rectangle in
--| four lookups (`PrefixSums`, a summed-area table): a rectangle is all red
--| and green if no tile of it there is outside.
--|
--| The tests are in `Aoc.Year2025.Day09.Tests` (Tests/); `run` checks none of them.

namespace Aoc.Year2025.Day09
import Aoc.Common (Line, Point, PrefixSums)
import Std (Fail, IO, List, Nat, Parse, Text)
import Std.Parse (char, nat, token)

def main(): {IO, Fail} () :=
  let tiles := parseTiles IO.readAll()
  IO.print "Part 1: ${solvePart1 tiles}"
  IO.print "Part 2: ${solvePart2 tiles}"

--| One red tile per line (a tile is a point: `x` its column, `y` its row), in the order the loop joins them. Spaces around a
--| number are allowed; anything else fails, naming the line and column.
def parseTiles (input: Text): {Fail} List Point := Parse.eachLine input redTile

--| "7,1" is `{ x = 7, y = 1 }`.
def redTile(): {Parse} Point :=
  let x := token nat
  char ','
  let y := token nat
  { x, y }

--| A rectangle on the floor, given by two red tiles at opposite corners
--| (either pair of opposite corners: the order doesn't matter).
type Rectangle = { corner: Point, opposite: Point }

--| The rectangle a pair of red tiles makes.
def Rectangle.ofPair (pair: (Point, Point)): Rectangle := { corner = pair.fst, opposite = pair.snd }

--| The number of tiles in the rectangle, both corners included.
def Rectangle.area (rectangle: Rectangle): Nat :=
  (rectangle.corner.x.absDiff rectangle.opposite.x + 1) * (rectangle.corner.y.absDiff rectangle.opposite.y + 1)

--| The largest of some areas, 0 if there are none.
def largest (areas: List Nat): Nat := areas.foldLeft 0 Nat.max

--| Part 1: the largest rectangle with two red tiles as opposite corners.
def solvePart1 (tiles: List Point): Nat := tiles.pairs |> .map Rectangle.ofPair |> .map .area |> largest

-- Part 2 ---------------------------------------------------------------------

--| The lines of the loop: from each red tile to the next, and from the last
--| back to the first.
def loopLines (tiles: List Point): List Line :=
  tiles.zip (tiles.drop 1 |> .append (tiles.take 1)) |> .map (ends => { from = ends.fst, to = ends.snd })

--| `value` is from `one` to `other`, in either order.
def isBetween (one other value: Nat): Bool := (one ≤ value ≤ other) ∨ (other ≤ value ≤ one)

--| `value` is from `one` to `other`, `other` left out, in either order.
def isBetweenHalfOpen (one other value: Nat): Bool := (one ≤ value < other) ∨ (other ≤ value < one)

--| The tile is on the line (a red tile at either end, or a green tile).
def Point.isOnLine (tile: Point) (line: Line): Bool :=
  isBetween line.from.x line.to.x tile.x ∧ isBetween line.from.y line.to.y tile.y

--| The line runs down a column right of the tile, across the tile's row:
--| from a row at or above it to a row below it, either way round. A tile
--| that isn't on the loop is inside it when an odd number of lines do that
--| (going right from it, a ray crosses the loop an odd number of times).
def crossesRightOf (tile: Point) (line: Line): Bool :=
  line.isVertical ∧ tile.x < line.from.x ∧ isBetweenHalfOpen line.from.y line.to.y tile.y

--| The tile is red or green, if `lines` are the lines of the loop that touch
--| its row (the others are no nearer to it than its row is).
def isRedOrGreen (lines: List Line) (tile: Point): Bool :=
  lines.any tile.isOnLine ∨ lines.count (crossesRightOf tile) % 2 == 1

--| The line touches row y.
def touchesRow (y: Nat) (line: Line): Bool := isBetween line.from.y line.to.y y

--| The columns that matter, from the red tiles' columns: each of them and
--| the one just right of it, in order, each once. (The same for rows.)
def keyLines (values: List Nat): List Nat := values.append (values.map Succ) |> .sort |> .dedup

--| The floor through the key columns and rows: where each key column and
--| row is (`columns`, `rows`), and how many tiles of each block of them are
--| outside the loop (`outside`: a cell is 1 for a tile outside, 0 for a red
--| or green one).
type Floor = { columns: List Nat, rows: List Nat, outside: PrefixSums }

def Floor.of (tiles: List Point): Floor :=
  let columns := keyLines (tiles.map .x)
  let rows := keyLines (tiles.map .y)
  { columns, rows, outside = PrefixSums.of (Floor.outsideCells (loopLines tiles) columns rows) }

--| The floor through the key columns and rows, row by row: 1 for each tile
--| outside the loop. A row's tiles are tested against the lines that touch
--| the row; the others are too far away to matter.
def Floor.outsideCells (lines: List Line) (columns rows: List Nat): List (List Nat) :=
  rows.map (y => Floor.outsideRow (lines.filter (touchesRow y)) columns y)

--| One row of the floor: 1 for each tile outside the loop.
def Floor.outsideRow (lines: List Line) (columns: List Nat) (y: Nat): List Nat :=
  columns.map (x => if isRedOrGreen lines { x, y } then 0 else 1)

--| A red tile, with the positions of its column and row among the key ones.
type Corner = { tile: Point, column: Nat, row: Nat }

def Floor.corner (floor: Floor) (tile: Point): Corner :=
  { tile, column = floor.columns.indexOf tile.x, row = floor.rows.indexOf tile.y }

--| A rectangle whose two corners are red tiles with their positions among
--| the key columns and rows, found once per tile instead of once per
--| rectangle (the floor has about 500 red tiles and 125,000 rectangles).
type FloorRectangle = { corner: Corner, opposite: Corner }

def FloorRectangle.ofPair (pair: (Corner, Corner)): FloorRectangle := { corner = pair.fst, opposite = pair.snd }

def FloorRectangle.area (rectangle: FloorRectangle): Nat :=
  Rectangle.area { corner = rectangle.corner.tile, opposite = rectangle.opposite.tile }

--| Every tile of the rectangle is red or green: none of its key columns
--| and rows is outside the loop.
def Floor.allRedOrGreen (floor: Floor) (rectangle: FloorRectangle): Bool :=
  let first := rectangle.corner
  let second := rectangle.opposite
  floor.outside.block
    (Nat.min first.row second.row)
    (Nat.max first.row second.row + 1)
    (Nat.min first.column second.column)
    (Nat.max first.column second.column + 1)
    == 0

--| Part 2: the largest rectangle with two red tiles as opposite corners that
--| is all red and green.
def solvePart2 (tiles: List Point): Nat :=
  let floor := Floor.of tiles
  tiles.map floor.corner |> .pairs |> .map FloorRectangle.ofPair |> .filter floor.allRedOrGreen |> .map .area |> largest
