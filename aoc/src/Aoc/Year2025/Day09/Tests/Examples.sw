--| Day 9's tests: the example from the puzzle and unit tests.
--
-- Kept apart from the program, so `stitchwort run Aoc.Year2025.Day09.main`
-- doesn't check them.

namespace Aoc.Year2025.Day09.Tests
import Aoc.Common (Line, Point, PrefixSums)
import Aoc.Year2025.Day09 (..)
import Std (Fail, List, Nat, Result, Text)

--| The puzzle's eight red tiles (also in aoc/examples/2025/day09.txt).
def example: Result (List Point) Text :=
  Fail.toResult (() => parseTiles (include "../../../../../examples/2025/day09.txt"))

def tile (x y: Nat): Point := { x, y }

def rectangle (corner opposite: Point): Rectangle := { corner, opposite }

def line (from to: Point): Line := { from, to }

def tilesOf (input: Text): Result (List Point) Text := Fail.toResult (() => parseTiles input)

test "parse a tile" := tilesOf """
  7,1
   11 , 1 """ == Ok [tile 7 1, tile 11 1]
test "parse rejects other lines" := tilesOf "7,1\n7;1" == Err "line 2, column 2: expected ',', got ';'"
test "parse rejects too few and too many" :=
  (tilesOf "7", tilesOf "7,1,2")
    == (
      Err "line 1, column 2: expected ',', got the end of the line",
      Err "line 1, column 4: expected the end of the line, got ','"
    )
test "parse rejects a blank line" :=
  tilesOf "7,1\n\n" == Err "line 2, column 1: expected a number, got the end of the line"
test "example has 8 tiles" := example.map (tiles => tiles.length) == Ok 8

test "area counts both corners" :=
  (rectangle (tile 2 5) (tile 9 7)).area == 24
    ∧ (rectangle (tile 9 7) (tile 2 5)).area == 24
    ∧ (rectangle (tile 7 3) (tile 7 3)).area == 1
test "area in a line" := (rectangle (tile 7 3) (tile 2 3)).area == 6

test "example part 1" := example.map solvePart1 == Ok 50
test "example part 2" := example.map solvePart2 == Ok 24
test "no tiles" := (solvePart1 [], solvePart2 []) == (0, 0)
test "one tile" := (solvePart1 [tile 3 4], solvePart2 [tile 3 4]) == (0, 0)
test "two tiles in a row" := (solvePart1 [tile 3 4, tile 8 4], solvePart2 [tile 3 4, tile 8 4]) == (6, 6)

--| A square: every rectangle is inside.
def square: List Point := [tile 1 1, tile 6 1, tile 6 4, tile 1 4]

test "square" := (solvePart1 square, solvePart2 square) == (24, 24)

--| A U: the gap between its arms, columns 3 to 6 above row 6, is outside, so
--| no rectangle across the top of the arms is red and green. The largest
--| that is runs along the bottom, from (2, 6) to (9, 9).
def letterU: List Point := [tile 0 0, tile 2 0, tile 2 6, tile 7 6, tile 7 0, tile 9 0, tile 9 9, tile 0 9]

test "U" := (solvePart1 letterU, solvePart2 letterU) == (100, 32)

--| A slot one tile wide: the lines at columns 2 and 3 run side by side down
--| to row 3 and back, with no tile between them. Every tile of the whole
--| square is red or green (the slot holds no tile), so the largest rectangle
--| is the whole square, although the loop itself doesn't enclose all of it.
def slot: List Point := [tile 0 0, tile 2 0, tile 2 3, tile 3 3, tile 3 0, tile 5 0, tile 5 5, tile 0 5]

test "slot one tile wide" := (solvePart1 slot, solvePart2 slot) == (36, 36)

--| The loop going the other way round gives the same answers.
test "example reversed" := example.map (tiles => (solvePart1 tiles.reverse, solvePart2 tiles.reverse)) == Ok (50, 24)

test "loop lines" :=
  loopLines [tile 1 1, tile 6 1, tile 6 4]
    == [line (tile 1 1) (tile 6 1), line (tile 6 1) (tile 6 4), line (tile 6 4) (tile 1 1)]
test "is between" := isBetween 3 7 5 ∧ isBetween 7 3 5 ∧ isBetween 3 3 3 ∧ ¬(isBetween 3 7 8) ∧ ¬(isBetween 7 3 2)
test "is on line" :=
  (tile 4 1).isOnLine (line (tile 1 1) (tile 6 1))
    ∧ (tile 6 1).isOnLine (line (tile 1 1) (tile 6 1))
    ∧ ¬((tile 4 2).isOnLine (line (tile 1 1) (tile 6 1)))
test "crosses right of" :=
  crossesRightOf (tile 2 2) (line (tile 6 1) (tile 6 4))
    ∧ crossesRightOf (tile 2 1) (line (tile 6 4) (tile 6 1))
    ∧ ¬(crossesRightOf (tile 2 4) (line (tile 6 1) (tile 6 4)))
    ∧ ¬(crossesRightOf (tile 6 2) (line (tile 6 1) (tile 6 4)))
    ∧ ¬(crossesRightOf (tile 2 1) (line (tile 1 1) (tile 6 1)))

--| The example's floor, row by row, # for red or green: as the puzzle draws it.
def drawn (lines: List Line) (width height: Nat): List Text :=
  List.range 0 height
    |> .map (y => List.range 0 width |> .map (x => if isRedOrGreen lines (tile x y) then '#' else '.') |> Text.fromList)

test "red or green" :=
  example.map (tiles => drawn (loopLines tiles) 14 9)
    == Ok ["..............", ".......#####..", ".......#####..", "..##########..", "..##########..", "..##########..",
      ".........###..", ".........###..", ".............."]

test "touches row" :=
  touchesRow 2 (line (tile 6 1) (tile 6 4))
    ∧ touchesRow 4 (line (tile 6 1) (tile 6 4))
    ∧ ¬(touchesRow 5 (line (tile 6 1) (tile 6 4)))
test "key lines" := keyLines [7, 11, 11, 9, 2] == [2, 3, 7, 8, 9, 10, 11, 12]
test "floor" :=
  example.map (tiles => (let floor := Floor.of tiles; (floor.columns, floor.rows)))
    == Ok ([2, 3, 7, 8, 9, 10, 11, 12], [1, 2, 3, 4, 5, 6, 7, 8])
test "floor outside" :=
  example.map (tiles =>
    (
      Floor.outsideRow (loopLines tiles) [2, 3, 7, 8, 9, 10, 11, 12] 1,
      Floor.outsideRow (loopLines tiles) [2, 3, 7, 8, 9, 10, 11, 12] 4
    ))
    == Ok ([1, 1, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 1])
test "corner" :=
  example.map (tiles =>
    (let floor := Floor.of tiles; ((floor.corner (tile 9 5)).column, (floor.corner (tile 9 5)).row)))
    == Ok (4, 4)
test "all red or green" :=
  example.map (tiles =>
    let floor := Floor.of tiles
    let located := (corner opposite: Point) =>
      ({ corner = floor.corner corner, opposite = floor.corner opposite }: FloorRectangle)
    floor.allRedOrGreen (located (tile 9 5) (tile 2 3))
      ∧ ¬(floor.allRedOrGreen (located (tile 11 1) (tile 2 5)))
      ∧ floor.allRedOrGreen (located (tile 7 3) (tile 11 1)))
    == Ok True
