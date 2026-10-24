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
    (Both (List.indexOfLt a.x (Floor.of tiles).columns (keyLinesHas (columnsOf tiles) a.x (Inl (columnIn tiles a ma))))
      (List.indexOfLt b.x (Floor.of tiles).columns (keyLinesHas (columnsOf tiles) b.x (Inl (columnIn tiles b mb)))))
    (Both (List.indexOfLt a.y (Floor.of tiles).rows (keyLinesHas (rowsOf tiles) a.y (Inl (rowIn tiles a ma))))
      (List.indexOfLt b.y (Floor.of tiles).rows (keyLinesHas (rowsOf tiles) b.y (Inl (rowIn tiles b mb)))))

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
    List.map cornersArea (List.filter (Floor.allRedOrGreen (Floor.of tiles)) (List.pairs (List.map (Floor.of tiles).corner tiles)))
      = List.map (corners => area corners.fst corners.snd) (List.filter (allRedOrGreen tiles) (rectangles tiles)) :=
  let floor := Floor.of tiles
  let both := (p: (Tile, Tile)) => (floor.corner p.fst, floor.corner p.snd)
  let keep := (p: (Tile, Tile)) => Floor.allRedOrGreen floor (both p)
  rewrite List.pairsMap floor.corner tiles,
    List.filterOfMap (Floor.allRedOrGreen floor) both (List.pairs tiles),
    List.mapMap cornersArea both (List.filter keep (List.pairs tiles)),
    List.filterCongMem keep (allRedOrGreen tiles) (List.pairs tiles) (programTest tiles)

theorem part2Correct (tiles: List Tile): Part2 tiles (solvePart2 tiles) :=
  let areas := List.map (corners => area corners.fst corners.snd) (List.filter (allRedOrGreen tiles) (rectangles tiles))
  let same: solvePart2 tiles = largest areas := Eq.cong largest (programAreas tiles)
  rewrite same in largestIsLargest areas
