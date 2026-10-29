-- The community's speed trick: sort the rectangles by area, largest first,
-- and take the first that passes the test. With the EDGE test (`mainEdge`)
-- and with the program's own summed-area test (`mainOurs`).

namespace Scratch.Sorted
import Aoc.Year2025.Day09 (Corner, Floor, Tile, cornersArea, loopLines, pairArea, parseTiles)
import Scratch.Edge (away)
import Std (Fail, IO, List, Nat, Option)

def byAreaDown (rects: List (a, a)) (size: (a, a) → Nat): List (a, a) := rects.sortBy (p q => Nat.compare (size q) (size p))

def firstArea (found: Option (a, a)) (size: (a, a) → Nat): Nat := match found with
  | Some p => size p
  | None => 0

def edgePart2 (tiles: List Tile): Nat :=
  let lines := loopLines tiles
  firstArea (byAreaDown tiles.pairs pairArea |> .find (p => lines.all (away p.fst p.snd))) pairArea

def oursPart2 (tiles: List Tile): Nat :=
  let floor := Floor.of tiles
  firstArea (byAreaDown (tiles.map floor.corner |> .pairs) cornersArea |> .find floor.allRedOrGreen) cornersArea

def mainEdge(): {IO, Fail} () :=
  let tiles := parseTiles IO.readAll()
  IO.print "Part 2 (EDGE, sorted): ${edgePart2 tiles}"

def mainOurs(): {IO, Fail} () :=
  let tiles := parseTiles IO.readAll()
  IO.print "Part 2 (ours, sorted): ${oursPart2 tiles}"

def mainSortOnly(): {IO, Fail} () :=
  let tiles := parseTiles IO.readAll()
  IO.print "Largest after sort: ${firstArea (byAreaDown tiles.pairs pairArea |> .find (p => True)) pairArea}"
