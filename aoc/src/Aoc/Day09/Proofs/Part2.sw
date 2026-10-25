-- Day 9, part 2, proved for every list of red tiles (`part2Correct`): the
-- program's answer is the largest area of the spec's rectangles that are
-- all red and green. The program pairs up the red tiles with their key
-- positions instead of the tiles themselves, so it has the same rectangles;
-- for each, its test in the summed-area table says that the key tiles are
-- red or green (Floor.sw), which says that every tile is (Compress.sw).

namespace Aoc.Day09.Proofs
import Aoc.Day09 (..)
import Aoc.Day09.Spec (..)
import Std (Eq, List, Nat)

-- A red tile's key positions are inside the floor.
theorem cornerInside (tiles: List Tile) (a: Tile) (b: Tile) (ma: List.Mem a tiles) (mb: List.Mem b tiles):
    Inside (Floor.of tiles) ((Floor.of tiles).corner a) ((Floor.of tiles).corner b) :=
  Both
    (Both (List.indexOfLt (Floor.of tiles).columns a.x (keyLinesHas (columnsOf tiles) a.x (Inl (columnIn tiles a ma))))
      (List.indexOfLt (Floor.of tiles).columns b.x (keyLinesHas (columnsOf tiles) b.x (Inl (columnIn tiles b mb)))))
    (Both (List.indexOfLt (Floor.of tiles).rows a.y (keyLinesHas (rowsOf tiles) a.y (Inl (rowIn tiles a ma))))
      (List.indexOfLt (Floor.of tiles).rows b.y (keyLinesHas (rowsOf tiles) b.y (Inl (rowIn tiles b mb)))))

-- The program's test of the rectangle between two red tiles is the spec's.
theorem programTest (tiles: List Tile) (corners: (Tile, Tile)) (m: List.Mem corners (rectangles tiles)):
    Floor.allRedOrGreen (Floor.of tiles) ((Floor.of tiles).corner corners.fst, (Floor.of tiles).corner corners.snd) = allRedOrGreen tiles corners :=
  match List.memPairs corners tiles m with
    | Both ma mb =>
      Eq.trans
        (allRedOrGreenKeys tiles ((Floor.of tiles).corner corners.fst) ((Floor.of tiles).corner corners.snd) (cornerInside tiles corners.fst corners.snd ma mb))
        (allKeysIsSpec tiles corners.fst corners.snd ma mb)

-- The areas the program compares are the spec's.
theorem programAreas (tiles: List Tile):
    List.map (List.filter (List.pairs (List.map tiles (Floor.of tiles).corner)) (Floor.allRedOrGreen (Floor.of tiles))) cornersArea
      = List.map (List.filter (rectangles tiles) (allRedOrGreen tiles)) (corners => area corners.fst corners.snd) :=
  let floor := Floor.of tiles
  let both := (p: (Tile, Tile)) => (floor.corner p.fst, floor.corner p.snd)
  let keep := (p: (Tile, Tile)) => Floor.allRedOrGreen floor (both p)
  rewrite List.pairsMap tiles floor.corner,
    List.filterOfMap (List.pairs tiles) (Floor.allRedOrGreen floor) both,
    List.mapMap (List.filter (List.pairs tiles) keep) cornersArea both,
    List.filterCongMem (List.pairs tiles) keep (allRedOrGreen tiles) (programTest tiles)

theorem part2Correct (tiles: List Tile): Part2 tiles (solvePart2 tiles) :=
  let areas := List.map (List.filter (rectangles tiles) (allRedOrGreen tiles)) (corners => area corners.fst corners.snd)
  let same: solvePart2 tiles = largest areas := Eq.cong largest (programAreas tiles)
  rewrite same in largestIsLargest areas
