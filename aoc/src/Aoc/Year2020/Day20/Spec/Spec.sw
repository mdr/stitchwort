--| Day 20's puzzle, in its own words, sharing only the data types with the
--| program: the input format, a tile's four edges, which edges match, the
--| corners and part 1, and the eight orientations.

namespace Aoc.Year2020.Day20.Spec
import Aoc.Year2020.Day20 (Image, Jigsaw, Pixel, Tile)
import Std (Char, List, Nat, NonEmptyList, Option, Parse, Text)

-- The format

def PixelWritten (read: List Char) (pixel: Pixel): Prop :=
  (read = ['#'] ∧ pixel = Rough) ∨ (read = ['.'] ∧ pixel = Calm)

def RowWritten (read: List Char) (row: List Pixel): Prop := Parse.Each PixelWritten read row ∧ row ≠ []

--| "Tile 2311:", then the tile's rows, a line each.
def TileWritten (read: List Char) (tile: Tile): Prop :=
  ∃ (idRead: List Char) => ∃ (break: List Char) => ∃ (rowsRead: List Char) => read
    = "Tile ".toList ++ idRead ++ [':'] ++ break ++ rowsRead
    ∧ (idRead ≠ [] ∧ idRead.all Parse.isDigit = True ∧ tile.id = Parse.digitsValue idRead)
    ∧ Parse.LineBreak break
    ∧ (∃ (rows: NonEmptyList (List Pixel)) => Parse.SepBy RowWritten (read u => Parse.LineBreak read) rowsRead rows
      ∧ tile.image.rows = rows.toList)

--| The tiles, a blank line between each two.
def JigsawWritten (read: List Char) (jigsaw: Jigsaw): Prop :=
  ∃ (tiles: NonEmptyList Tile) => Parse.SepBy TileWritten (read u => Parse.BlankLine read) read tiles
    ∧ jigsaw.tiles = tiles.toList

-- Edges

--| A tile's four edges, clockwise from the top: its first row, the last
--| pixel of each row, its last row, and the first pixel of each row. Each
--| is read left to right or top to bottom.
def edges (image: Image): List (List Pixel) := [
  image.rows.headOr [],
  image.rows.map (row => row.last.getOrElse Calm),
  image.rows.last.getOrElse [],
  image.rows.map (row => row.headOr Calm)
]

--| Tiles are rotated and flipped, so two edges can meet when their pixels
--| are the same, in the same order or reversed.
def Fit (edge other: List Pixel): Prop := edge = other ∨ edge = other.reverse

--| `edge`, of `tile`, matches an edge of another tile of the jigsaw.
def Matched (jigsaw: Jigsaw) (tile: Tile) (edge: List Pixel): Prop :=
  ∃ (other: Tile) => other ∈ jigsaw.tiles
    ∧ other.id ≠ tile.id
    ∧ ∃ (otherEdge: List Pixel) => otherEdge ∈ edges other.image ∧ Fit edge otherEdge

--| A corner tile: exactly two of its edges match another tile's. (The
--| puzzle promises that edges on the image's border match nothing, so
--| this is a tile with two border edges.)
def Corner (jigsaw: Jigsaw) (tile: Tile): Prop := List.CountWith (Matched jigsaw tile) (edges tile.image) 2

--| `kept` is the items with `p`, in order.
def Kept (p: a → Prop): (items: List a) → (kept: List a) → Prop
  | [], kept => kept = []
  | [item, ..rest], kept =>
    (p item ∧ ∃ (others: List a) => Kept p rest others ∧ kept = [item, ..others]) ∨ (¬p item ∧ Kept p rest kept)

--| "Multiply the IDs of the four corner tiles together."
def Part1 (jigsaw: Jigsaw) (answer: Nat): Prop :=
  ∃ (corners: List Tile) => Kept (Corner jigsaw) jigsaw.tiles corners ∧ answer = (corners.map (.id)).product

-- Sea monsters

--| The pixel at `row` and `column`, counting from the top left; none off
--| the image.
def pixelAt (image: Image) (row column: Nat): Option Pixel := (image.rows.get row).flatMap (pixels => pixels.get column)

--| A sea monster, as `monster` draws it, with its top left at `row` and
--| `column` of `image`: each `#` of the monster is on a `#` of the image.
def MonsterAt (image monster: Image) (row column: Nat): Prop :=
  ∀ (r c: Nat) => pixelAt monster r c = Some Rough → pixelAt image (row + r) (column + c) = Some Rough

--| `at` is under a `#` of a sea monster, as `monster` draws it, that lies
--| within `image` (its height, and its first row's width).
def Covered (image monster: Image) (at: List Nat): Prop :=
  ∃ (row: Nat) => ∃ (column: Nat) => ∃ (r: Nat) => ∃ (c: Nat) => row + monster.rows.length ≤ image.rows.length
    ∧ column + (monster.rows.headOr []).length ≤ (image.rows.headOr []).length
    ∧ MonsterAt image monster row column
    ∧ pixelAt monster r c = Some Rough
    ∧ at = [row + r, column + c]

--| `cells` lists each `#` of the image once, as `[row, column]`.
def RoughCells (image: Image) (cells: List (List Nat)): Prop :=
  List.Distinct cells
    ∧ (∀ (at: List Nat) => at ∈ cells
      ↔ ∃ (row: Nat) => ∃ (column: Nat) => at = [row, column] ∧ pixelAt image row column = Some Rough)

--| "How many # are not part of a sea monster?", with sea monsters as
--| `monster` draws them, counted over a listing of the image's `#`s.
def Roughness (image monster: Image) (cells: List (List Nat)) (answer: Nat): Prop :=
  List.CountWith (at => ¬Covered image monster at) cells answer
