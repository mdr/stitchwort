--| Advent of Code 2020, day 20: Jurassic Jigsaw. The input is square
--| tiles of an image, each with an id, every one rotated and flipped at
--| random. Assembled, the tiles fit together where their edges match.
--| Part 1 is the product of the four corner tiles' ids. Part 2 strips each
--| tile's border, finds the sea monsters in the image in the one
--| orientation that has them, and counts the rough water: the `#`s that
--| are part of no monster.
--|
--|   $ cd aoc && stitchwort run Aoc.Year2020.Day20.main < inputs/2020/day20.txt
--|
--| The puzzle promises that the edges that meet in the image match nothing
--| else, so a corner is a tile with exactly two edges matching another
--| tile's, and the image can be assembled one tile at a time from a corner,
--| with no search: each next tile is the only one that fits. Rather than
--| turning the whole image, the monster is turned, and looked for in all
--| eight of its orientations. The proofs are in `Aoc.Year2020.Day20.Proofs`
--| (Proofs/), and the tests in `Aoc.Year2020.Day20.Tests` (Tests/); `run`
--| checks neither.

namespace Aoc.Year2020.Day20
import Std (Bool, Fail, IO, List, Nat, Option, Parse, Set, Text)

def main(): {IO, Fail} () :=
  let jigsaw := parseJigsaw IO.readAll()
  IO.print "Part 1: ${jigsaw.cornerProduct}"
  IO.print "Part 2: ${jigsaw.assemble |> .roughness}"

type Pixel =
  | Rough
  | Calm

--| How the tiles write a pixel.
def Pixel.symbol: Pixel → Text
  | Rough => "#"
  | Calm => "."

def pixel(): {Parse} Pixel := Parse.pick ([Rough, Calm].map (pixel => (pixel.symbol, pixel)))

--| Rows of pixels, top to bottom, each left to right.
type Image = { rows: List (List Pixel) }

--| A quarter turn clockwise: the bottom row becomes the left column.
def Image.rotate (image: Image): Image := { rows = image.rows.reverse.transpose }

--| Left to right, as in a mirror.
def Image.flip (image: Image): Image := { rows = image.rows.map (.reverse) }

--| The image in each of its eight orientations: four turns, then the same
--| four of its mirror image. The first is the image itself.
def Image.orientations (image: Image): List Image :=
  let turns := (one: Image) => [one, one.rotate, one.rotate.rotate, one.rotate.rotate.rotate]
  turns image ++ turns image.flip

def Image.columns (image: Image): List (List Pixel) := image.rows.transpose

--| The pixels along one side of a tile, left to right or top to bottom.
type Edge = { pixels: List Pixel }

def Image.top (image: Image): Edge := { pixels = image.rows.headOr [] }
def Image.bottom (image: Image): Edge := { pixels = image.rows.last.getOrElse [] }
def Image.left (image: Image): Edge := { pixels = image.rows.map (row => row.headOr Calm) }
def Image.right (image: Image): Edge := { pixels = image.rows.map (row => row.last.getOrElse Calm) }

--| Clockwise from the top.
def Image.edges (image: Image): List Edge := [image.top, image.right, image.bottom, image.left]

--| The image without its outer rows and columns.
def Image.interior (image: Image): Image := { rows = image.rows.drop 1 |> .init |> .map (row => row.drop 1 |> .init) }

--| Whether one tile's edge can meet another's when the tiles are turned
--| or flipped: the same pixels, in the same order or reversed.
def Edge.fits (edge: Edge) (other: Edge): Bool := edge.pixels == other.pixels || edge.pixels == other.pixels.reverse

type Tile = { id: Nat, image: Image }

--| The tile turned or flipped: its eight orientations, itself first.
def Tile.orientations (tile: Tile): List Tile := tile.image.orientations.map (image => { id = tile.id, image })

--| The tiles, as the input lists them.
type Jigsaw = { tiles: List Tile }

--| At least one row, a first row with a pixel, and every row as long as
--| the first: what turning and flipping need (`Proofs.Rectangle`).
def Image.isRectangle (image: Image): Bool := match image.rows with
  | [] => False
  | [first, ..rest] => first.length != 0 && image.rows.all (row => row.length == first.length)

def Jigsaw.rectangular (jigsaw: Jigsaw): Bool := jigsaw.tiles.all (tile => tile.image.isRectangle)

-- The format

def tile(): {Parse} Tile :=
  Parse.text "Tile "
  let id := Parse.nat()
  Parse.char ':'
  Parse.newline()
  let rows := Parse.lines pixelRow
  { id, image = { rows = rows.toList } }

def pixelRow(): {Parse} List Pixel :=
  let pixels := Parse.many1 pixel
  pixels.toList

def jigsaw(): {Parse} Jigsaw :=
  let tiles := Parse.sections tile
  { tiles = tiles.toList }

def parseJigsaw (input: Text): {Fail} Jigsaw := Parse.all input jigsaw

-- Part 1

--| Whether `edge`, of `tile`, fits an edge of some other tile.
def Jigsaw.matches (jigsaw: Jigsaw) (tile: Tile) (edge: Edge): Bool :=
  jigsaw.tiles.any (other => other.id != tile.id && other.image.edges.any edge.fits)

--| How many of the tile's edges fit another tile's.
def Jigsaw.matchedEdges (jigsaw: Jigsaw) (tile: Tile): Nat := tile.image.edges.count (jigsaw.matches tile)

--| The tiles with only two edges that fit another's: the image's corners,
--| when edges that don't meet don't fit.
def Jigsaw.corners (jigsaw: Jigsaw): List Tile := jigsaw.tiles.filter (tile => jigsaw.matchedEdges tile == 2)

def Jigsaw.cornerProduct (jigsaw: Jigsaw): Nat := jigsaw.corners.map (.id) |> .product

-- Part 2: assembling the image

--| The tile, of those other than `tile`, turned so that `placed` says it
--| meets `tile` on `edge`; none when no other tile's edge fits `edge`.
def Jigsaw.neighbour (jigsaw: Jigsaw) (tile: Tile) (edge: Edge) (placed: Tile → Bool): Option Tile :=
  jigsaw.tiles.filter (other => other.id != tile.id && other.image.edges.any edge.fits)
    |> .flatMap (.orientations)
    |> .find placed

def Jigsaw.rightOf (jigsaw: Jigsaw) (tile: Tile): Option Tile :=
  jigsaw.neighbour tile tile.image.right (next => next.image.left == tile.image.right)

def Jigsaw.below (jigsaw: Jigsaw) (tile: Tile): Option Tile :=
  jigsaw.neighbour tile tile.image.bottom (next => next.image.top == tile.image.bottom)

--| The tiles to the right of `tile`, in order, until one has nothing to
--| its right; `fuel` bounds how many.
def Jigsaw.rowAfter (jigsaw: Jigsaw) (tile: Tile): (fuel: Nat) → List Tile
  | Zero => []
  | Succ fuel =>
    match jigsaw.rightOf tile with
      | Some next => [next, ..jigsaw.rowAfter next fuel]
      | None => []

--| The rows from the one starting with `first` down, until a row's first
--| tile has nothing below it; `fuel` bounds how many.
def Jigsaw.rowsFrom (jigsaw: Jigsaw) (first: Tile): (fuel: Nat) → List (List Tile)
  | Zero => []
  | Succ fuel =>
    let below :=
      match jigsaw.below first with
        | Some next => jigsaw.rowsFrom next fuel
        | None => []
    [[first, ..jigsaw.rowAfter first jigsaw.tiles.length], ..below]

--| A corner, turned so that its top and left edges fit no other tile's:
--| the image's top left tile.
def Jigsaw.topLeft (jigsaw: Jigsaw): {Fail} Tile :=
  let corner := jigsaw.corners.headOr { id = 0, image = { rows = [] } }
  corner.orientations.find (tile => not (jigsaw.matches tile tile.image.top) && not (jigsaw.matches tile tile.image.left))
    |> .orFail "no corner tile"

--| The tiles in place, row by row.
type Arrangement = { rows: List (List Tile) }

def Jigsaw.arrange (jigsaw: Jigsaw): {Fail} Arrangement := { rows = jigsaw.rowsFrom jigsaw.topLeft jigsaw.tiles.length }

--| The image the tiles make together, each without its border.
def Arrangement.image (arrangement: Arrangement): Image :=
  let band := (row: List Tile) => row.map (tile => tile.image.interior.rows) |> .transpose |> .map (.concat)
  { rows = arrangement.rows.flatMap band }

def Jigsaw.assemble (jigsaw: Jigsaw): {Fail} Image := jigsaw.arrange.image

-- Part 2: sea monsters

--| The puzzle's picture of a sea monster.
def seaMonster: Image :=
  { rows = ["                  # ", "#    ##    ##    ###", " #  #  #  #  #  #   "].map (line => line.toList.map (char => if char == '#' then Rough else Calm)) }

--| Where the rough pixels are, as `[row, column]`, counting from the top
--| left: a `List Nat` rather than a `Position`, which has no order for a `Set`.
def Image.roughAt (image: Image): List (List Nat) :=
  image.rows.withIndex.flatMap (((row, pixels)) =>
    pixels.withIndex.filterMap (match some | (column, Rough) => [row, column]))

--| `at` moved down and right by `by`.
def shift (by: List Nat) (at: List Nat): List Nat := List.zipWith by at (a b => a + b)

--| Where a copy of `monster`, as drawn (not turned), has its top left in
--| `image`: every rough pixel of the copy on a rough pixel of the image.
def Image.monsterStarts (image: Image) (monster: Image): List (List Nat) :=
  let rough := image.roughAt.toSet
  let height := image.rows.length
  let width := image.rows.headOr [] |> .length
  let monsterHeight := monster.rows.length
  let monsterWidth := monster.rows.headOr [] |> .length
  let starts := List.range 0 (height + 1 - monsterHeight) |> .flatMap (row => List.range 0 (width + 1 - monsterWidth) |> .map (column => [row, column]))
  starts.filter (start => monster.roughAt.all (at => rough.contains (shift start at)))

--| The rough pixels of `image` that are part of a copy of `monster`, as
--| drawn (not turned).
def Image.monsterPixels (image: Image) (monster: Image): Set (List Nat) :=
  image.monsterStarts monster |> .flatMap (start => monster.roughAt.map (shift start)) |> .toSet

--| The rough pixels in no copy of `monster`, as drawn.
def Image.roughnessWith (image: Image) (monster: Image): Nat := image.roughAt.toSet.size - (image.monsterPixels monster).size

--| The sea monster turned the way the image has them: the first of its
--| orientations of which the image has a copy (the puzzle's image has
--| copies in one).
def Image.monsterTurned (image: Image): Option Image := seaMonster.orientations.find (monster => (image.monsterPixels monster).size > 0)

--| The rough pixels in no sea monster, turned as `turned` says; all of
--| them if there are no sea monsters.
def Image.roughnessFor (image: Image): (turned: Option Image) → Nat
  | Some monster => image.roughnessWith monster
  | None => image.roughAt.toSet.size

--| The rough pixels in no sea monster, turned the way the image has them.
def Image.roughness (image: Image): Nat := image.roughnessFor image.monsterTurned
