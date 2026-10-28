-- Day 9's tests: the example from the puzzle and unit tests. Kept apart from
-- the program, so `stitchwort run Aoc.Year2025.Day09.main` doesn't check them.

namespace Aoc.Year2025.Day09.Tests
import Aoc.Year2025.Day09 (..)
import Std (Fail, List, Nat, PrefixSums, Result, Text)

-- The puzzle's eight red tiles (also in aoc/examples/2025/day09.txt).
def example: List Tile := Fail.orElse [] (() => parseTiles (include "../../../../../examples/2025/day09.txt"))

def tile (x: Nat) (y: Nat): Tile := { x, y }

def tilesOf (input: Text): Result (List Tile) Text := Fail.toResult (() => parseTiles input)

test "parse a tile" := tilesOf "7,1\n 11 , 1 " == Ok [tile 7 1, tile 11 1]
test "parse rejects other lines" := tilesOf "7,1\n7;1" == Err "line 2, column 2: expected ','"
test "parse rejects too few and too many" :=
  (tilesOf "7", tilesOf "7,1,2") == (Err "line 1, column 2: expected ','", Err "line 1, column 4: expected the end")
test "parse rejects a blank line" := tilesOf "7,1\n\n" == Err "line 2, column 1: expected a number"
test "example has 8 tiles" := example.length == 8

test "area counts both corners" := area (tile 2 5) (tile 9 7) == 24 ∧ area (tile 9 7) (tile 2 5) == 24 ∧ area (tile 7 3) (tile 7 3) == 1
test "area in a line" := area (tile 7 3) (tile 2 3) == 6

test "example part 1" := solvePart1 example == 50
test "example part 2" := solvePart2 example == 24
test "no tiles" := (solvePart1 [], solvePart2 []) == (0, 0)
test "one tile" := (solvePart1 [tile 3 4], solvePart2 [tile 3 4]) == (0, 0)
test "two tiles in a row" := (solvePart1 [tile 3 4, tile 8 4], solvePart2 [tile 3 4, tile 8 4]) == (6, 6)

-- A square: every rectangle is inside.
def square: List Tile := [tile 1 1, tile 6 1, tile 6 4, tile 1 4]

test "square" := (solvePart1 square, solvePart2 square) == (24, 24)

-- A U: the gap between its arms, columns 3 to 6 above row 6, is outside, so
-- no rectangle across the top of the arms is red and green. The largest
-- that is runs along the bottom, from (2, 6) to (9, 9).
def letterU: List Tile := [tile 0 0, tile 2 0, tile 2 6, tile 7 6, tile 7 0, tile 9 0, tile 9 9, tile 0 9]

test "U" := (solvePart1 letterU, solvePart2 letterU) == (100, 32)

-- A slot one tile wide: the lines at columns 2 and 3 run side by side down
-- to row 3 and back, with no tile between them. Every tile of the whole
-- square is red or green (the slot holds no tile), so the largest rectangle
-- is the whole square, although the loop itself doesn't enclose all of it.
def slot: List Tile := [tile 0 0, tile 2 0, tile 2 3, tile 3 3, tile 3 0, tile 5 0, tile 5 5, tile 0 5]

test "slot one tile wide" := (solvePart1 slot, solvePart2 slot) == (36, 36)

-- The loop going the other way round gives the same answers.
test "example reversed" := (solvePart1 example.reverse, solvePart2 example.reverse) == (50, 24)

test "loop lines" := loopLines [tile 1 1, tile 6 1, tile 6 4] == [(tile 1 1, tile 6 1), (tile 6 1, tile 6 4), (tile 6 4, tile 1 1)]
test "is between" := isBetween 3 7 5 ∧ isBetween 7 3 5 ∧ isBetween 3 3 3 ∧ ¬(isBetween 3 7 8) ∧ ¬(isBetween 7 3 2)
test "is on line" := isOnLine (tile 4 1) (tile 1 1, tile 6 1) ∧ isOnLine (tile 6 1) (tile 1 1, tile 6 1) ∧ ¬(isOnLine (tile 4 2) (tile 1 1, tile 6 1))
test "crosses right of" :=
  crossesRightOf (tile 2 2) (tile 6 1, tile 6 4) ∧ crossesRightOf (tile 2 1) (tile 6 4, tile 6 1) ∧ ¬(crossesRightOf (tile 2 4) (tile 6 1, tile 6 4))
    ∧ ¬(crossesRightOf (tile 6 2) (tile 6 1, tile 6 4)) ∧ ¬(crossesRightOf (tile 2 1) (tile 1 1, tile 6 1))

-- The example's floor, row by row, # for red or green: as the puzzle draws it.
def drawn (lines: List (Tile, Tile)) (width: Nat) (height: Nat): List Text :=
  List.range height |> .map (y => List.range width |> .map (x => if isRedOrGreen lines (tile x y) then '#' else '.') |> Text.fromList)

test "red or green" :=
  drawn (loopLines example) 14 9 == [
    "..............",
    ".......#####..",
    ".......#####..",
    "..##########..",
    "..##########..",
    "..##########..",
    ".........###..",
    ".........###..",
    ".............."
  ]

test "touches row" := touchesRow 2 (tile 6 1, tile 6 4) ∧ touchesRow 4 (tile 6 1, tile 6 4) ∧ ¬(touchesRow 5 (tile 6 1, tile 6 4))
test "key lines" := keyLines [7, 11, 11, 9, 2] == [2, 3, 7, 8, 9, 10, 11, 12]
test "floor" :=
  let floor := Floor.of example
  (floor.columns, floor.rows) == ([2, 3, 7, 8, 9, 10, 11, 12], [1, 2, 3, 4, 5, 6, 7, 8])
test "floor outside" :=
  Floor.outsideRow (loopLines example) [2, 3, 7, 8, 9, 10, 11, 12] 1 == [1, 1, 0, 0, 0, 0, 0, 1]
    ∧ Floor.outsideRow (loopLines example) [2, 3, 7, 8, 9, 10, 11, 12] 4 == [0, 0, 0, 0, 0, 0, 0, 1]
test "corner" :=
  let floor := Floor.of example
  (floor.corner (tile 9 5)).column == 4 ∧ (floor.corner (tile 9 5)).row == 4
test "all red or green" :=
  let floor := Floor.of example
  let corner := floor.corner
  floor.allRedOrGreen (corner (tile 9 5), corner (tile 2 3)) ∧ ¬(floor.allRedOrGreen (corner (tile 11 1), corner (tile 2 5)))
    ∧ floor.allRedOrGreen (corner (tile 7 3), corner (tile 11 1))
