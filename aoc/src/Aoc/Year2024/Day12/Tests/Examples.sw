-- Day 12's tests: the examples from the puzzle and unit tests. Kept apart
-- from the program, so `stitchwort run Aoc.Year2024.Day12.main` doesn't
-- check them.

namespace Aoc.Year2024.Day12.Tests
import Aoc.Year2024.Day12 (..)
import Aoc.Year2024.Day12.Spec (isChain, perimeter, sides, totalPrice)
import Std (Char, Fail, List, Map, Nat, Option, Result, Text)

def small: Text := """
  AAAA
  BBCD
  BBCC
  EEEC
  """

-- One O region with four X regions inside it.
def inside: Text := """
  OOOOO
  OXOXO
  OOOOO
  OXOXO
  OOOOO
  """

def larger: Text := """
  RRRRIICCFF
  RRRRIICCCF
  VVRRRCCFFF
  VVRCCCJFFF
  VVVVCJJCFE
  VVIVCCJJEE
  VVIIICJJEE
  MIIIIIJJEE
  MIIISIJEEE
  MMMISSJEEE
  """

def eShaped: Text := """
  EEEEE
  EXXXX
  EEEEE
  EXXXX
  EEEEE
  """

-- Two B regions touching diagonally inside an A region.
def diagonal: Text := """
  AAAAAA
  AAABBA
  AAABBA
  ABBAAA
  ABBAAA
  AAAAAA
  """

def parsed (input: Text): Result Garden Text := Fail.toResult (() => parseGarden input)

def garden (input: Text): Garden := Fail.orElse { plots = Map.empty } (() => parseGarden input)

def at (row: Nat) (column: Nat): Position := { row, column }

-- Each region's plant, area, perimeter and sides, in the program's order.
def summary (input: Text): List (Option Char, Nat, Nat, Nat) :=
  let map := garden input
  map.regions |> .map (region => (region.headOr (at 0 0) |> map.plantAt, region.length, map.perimeter region, map.sides region))

test "small example, part 1" := solvePart1 (garden small) == 140
test "inside example, part 1" := solvePart1 (garden inside) == 772
test "larger example, part 1" := solvePart1 (garden larger) == 1930
test "small example, part 2" := solvePart2 (garden small) == 80
test "inside example, part 2" := solvePart2 (garden inside) == 436
test "E-shaped example, part 2" := solvePart2 (garden eShaped) == 236
test "diagonal example, part 2" := solvePart2 (garden diagonal) == 368
test "larger example, part 2" := solvePart2 (garden larger) == 1206

-- "Regions A through E": areas 4, 4, 4, 1, 3; perimeters 10, 8, 10, 4, 8;
-- sides 4, 4, 8, 4, 4.
test "small example, each region" :=
  summary small == [(Some 'A', 4, 10, 4), (Some 'B', 4, 8, 4), (Some 'C', 4, 10, 8), (Some 'D', 1, 4, 4), (Some 'E', 3, 8, 4)]

test "inside example, the O region" := summary inside |> .headOr (None, 0, 0, 0) == (Some 'O', 21, 36, 20)
test "inside example, five regions" := (garden inside).regions.length == 5

-- "The E-shaped region has an area of 17 and 12 sides".
test "E-shaped region" := summary eShaped |> .headOr (None, 0, 0, 0) == (Some 'E', 17, 36, 12)

-- "4 sides on the outside and 8 more sides on the inside".
test "diagonal example, the A region" := summary diagonal |> .headOr (None, 0, 0, 0) == (Some 'A', 28, 40, 12)

-- The larger example's eleven regions, prices as the puzzle lists them.
test "larger example, eleven regions" :=
  (summary larger |> .map (((plant, area, perimeter, sides)) => (plant, area * perimeter, area * sides)))
    == [
      (Some 'R', 216, 120),
      (Some 'I', 32, 16),
      (Some 'C', 392, 308),
      (Some 'F', 180, 120),
      (Some 'V', 260, 130),
      (Some 'J', 220, 132),
      (Some 'C', 4, 4),
      (Some 'E', 234, 104),
      (Some 'I', 308, 224),
      (Some 'M', 60, 30),
      (Some 'S', 24, 18)
    ]

test "one plot" := solvePart1 (garden "A\n") == 4 && solvePart2 (garden "A\n") == 4
test "one row" := solvePart1 (garden "AAB\n") == 2 * 6 + 4 && solvePart2 (garden "AAB\n") == 2 * 4 + 4
test "one column" := solvePart1 (garden "A\nA\nA\n") == 3 * 8 && solvePart2 (garden "A\nA\nA\n") == 3 * 4

-- The same plant in two places is two regions.
test "same plant apart" := (garden "ABA\n").regions.length == 3 && solvePart1 (garden "ABA\n") == 12

-- Plots touching only at a corner aren't joined.
test "diagonal plots" := (garden "AB\nBA\n").regions.length == 4 && solvePart2 (garden "AB\nBA\n") == 16

-- A ring: 8 plots, perimeter 16, sides 8 (four outside, four inside).
test "a ring" :=
  let loop := garden "AAA\nABA\nAAA\n"
  summary "AAA\nABA\nAAA\n" == [(Some 'A', 8, 16, 8), (Some 'B', 1, 4, 4)] && loop.regions.length == 2

-- An L: six sides.
test "an L" := summary "AB\nAA\n" |> .headOr (None, 0, 0, 0) == (Some 'A', 3, 8, 6)

test "a region covers every plot it touches" := (garden larger).regionOf (at 0 0) |> .length == 12
test "regions cover every plot once" :=
  let map := garden larger
  map.positions.all (position => map.regions.count (region => region.any (plot => plot == position)) == 1) && map.positions.length == 100

test "no plots" := parsed "" == Err "line 1, column 1: expected a letter, got the end of the input"
test "parse" := (parsed "AB\nCD\n" |> .map (map => map.plots.toList)) == Ok [(at 0 0, 'A'), (at 0 1, 'B'), (at 1 0, 'C'), (at 1 1, 'D')]
test "parse without a final line break" := (parsed "AB\nCD" |> .map (map => map.positions.length)) == Ok 4
test "a bad plot" := (parsed "AB\nC.\n" |> .map (map => ())) == Err "line 2, column 2: expected a letter or the end of the line, got '.'"
test "a short row" := (parsed "ABC\nAB\n" |> .map (map => ())) == Err "line 2: expected 3 plots, as on the first line, got 2"

test "steps" :=
  (at 0 0).step Up == None && (at 0 0).step Left == None && (at 0 0).step Down == Some (at 1 0) && (at 2 3).step Right == Some (at 2 4)
    && (at 2 3).step Up == Some (at 1 3) && (at 2 3).step Left == Some (at 2 2)

test "fences and corners of one plot" :=
  let map := garden "AB\nAA\n"
  map.fences (at 1 0) == 2 && map.fences (at 0 1) == 4 && map.cornerCount (at 1 0) == 2
    && map.cornerCount (at 1 1) == 2 && map.cornerCount (at 0 0) == 2

-- The spec runs on the program's regions, and gives the puzzle's prices.
test "the spec's prices" :=
  [larger, diagonal, eShaped, inside, small].all (input =>
    let map := garden input
    totalPrice map.regions perimeter == solvePart1 map && totalPrice map.regions sides == solvePart2 map)
    && totalPrice (garden larger).regions sides == 1206

-- "4 sides on the outside and 8 more sides on the inside".
test "the spec's sides of the A region" := (garden diagonal).regions |> .headOr [] |> sides == 12

test "the spec's chains" :=
  let map := garden small
  isChain map (at 1 2) [at 2 2, at 2 3, at 3 3] (at 3 3) && !isChain map (at 0 0) [at 1 0] (at 1 0) && !isChain map (at 1 2) [at 2 3] (at 2 3)
