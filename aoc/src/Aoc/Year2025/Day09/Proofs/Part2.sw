--| Day 9, part 2, proved for every list of red tiles (`part2Correct`): the
--| program's answer is the largest area of the spec's rectangles that are
--| all red and green. The program pairs up the red tiles with their key
--| positions instead of the tiles themselves, so it has the same rectangles;
--| for each, its test in the summed-area table says that the key tiles are
--| red or green (Floor.sw), which says that every tile is (Compress.sw).

namespace Aoc.Year2025.Day09.Proofs
import Aoc.Common (Line, Point)
import Aoc.Year2025.Day09 (..)
import Aoc.Year2025.Day09.Spec (..)
import Std (Eq, List, Nat)

--| A red tile's key positions are inside the floor.
theorem cornerInside (tiles: List Point) (a: Point) (b: Point) (ma: List.Mem a tiles) (mb: List.Mem b tiles):
    Inside (Floor.of tiles) ((Floor.of tiles).corner a) ((Floor.of tiles).corner b) :=
  Both
    (Both (List.indexOfLt (Floor.of tiles).columns a.x (keyLinesHas (columnsOf tiles) a.x (Inl (columnIn tiles a ma))))
      (List.indexOfLt (Floor.of tiles).columns b.x (keyLinesHas (columnsOf tiles) b.x (Inl (columnIn tiles b mb)))))
    (Both (List.indexOfLt (Floor.of tiles).rows a.y (keyLinesHas (rowsOf tiles) a.y (Inl (rowIn tiles a ma))))
      (List.indexOfLt (Floor.of tiles).rows b.y (keyLinesHas (rowsOf tiles) b.y (Inl (rowIn tiles b mb)))))

--| The program's test of the rectangle between two red tiles is the spec's.
theorem programTest (tiles: List Point) (pair: (Point, Point)) (m: List.Mem pair tiles.pairs):
    Floor.allRedOrGreen (Floor.of tiles) { corner = (Floor.of tiles).corner pair.fst, opposite = (Floor.of tiles).corner pair.snd }
    = allRedOrGreen tiles (Rectangle.ofPair pair) := match List.memPairs pair tiles m with
      | Both ma mb =>
        Eq.trans
          (allRedOrGreenKeys tiles ((Floor.of tiles).corner pair.fst) ((Floor.of tiles).corner pair.snd) (cornerInside tiles pair.fst pair.snd ma mb))
          (allKeysIsSpec tiles pair.fst pair.snd ma mb)

--| The spec's rectangles that are all red and green, by their areas, as a
--| filter and map over the red tiles' pairs.
theorem specAreas (tiles: List Point):
    ((tiles.pairs.map Rectangle.ofPair).filter (allRedOrGreen tiles)).map Rectangle.area
      = (tiles.pairs.filter (p => allRedOrGreen tiles (Rectangle.ofPair p))).map (p => Rectangle.area (Rectangle.ofPair p)) :=
  rewrite List.filterOfMap (List.pairs tiles) (allRedOrGreen tiles) Rectangle.ofPair,
    List.mapMap (List.filter (List.pairs tiles) (p => allRedOrGreen tiles (Rectangle.ofPair p))) Rectangle.area Rectangle.ofPair
    in rfl

--| The areas the program compares are the spec's.
theorem programAreas (tiles: List Point):
    (((tiles.map (Floor.of tiles).corner).pairs.map FloorRectangle.ofPair).filter (Floor.allRedOrGreen (Floor.of tiles))).map FloorRectangle.area
      = List.map (List.filter (rectangles tiles) (allRedOrGreen tiles)) Rectangle.area :=
  let floor := Floor.of tiles
  let located := (p: (Point, Point)) => FloorRectangle.ofPair (floor.corner p.fst, floor.corner p.snd)
  let keep := (p: (Point, Point)) => Floor.allRedOrGreen floor (located p)
  let programSide:
      List.map (List.filter (List.map (List.pairs (List.map tiles floor.corner)) FloorRectangle.ofPair) (Floor.allRedOrGreen floor)) FloorRectangle.area
        = List.map (List.filter (List.pairs tiles) keep) (p => Rectangle.area (Rectangle.ofPair p)) :=
    calc
      List.map (List.filter (List.map (List.pairs (List.map tiles floor.corner)) FloorRectangle.ofPair) (Floor.allRedOrGreen floor)) FloorRectangle.area
      _ = List.map (List.filter (List.map (List.map (List.pairs tiles) (p => (floor.corner p.fst, floor.corner p.snd))) FloorRectangle.ofPair) (Floor.allRedOrGreen floor)) FloorRectangle.area :=
        rewrite List.pairsMap tiles floor.corner in rfl
      _ = List.map (List.filter (List.map (List.pairs tiles) located) (Floor.allRedOrGreen floor)) FloorRectangle.area :=
        rewrite List.mapMap (List.pairs tiles) FloorRectangle.ofPair (p => (floor.corner p.fst, floor.corner p.snd)) in rfl
      _ = List.map (List.map (List.filter (List.pairs tiles) keep) located) FloorRectangle.area :=
        rewrite List.filterOfMap (List.pairs tiles) (Floor.allRedOrGreen floor) located in rfl
      _ = List.map (List.filter (List.pairs tiles) keep) (p => Rectangle.area (Rectangle.ofPair p)) :=
        List.mapMap (List.filter (List.pairs tiles) keep) FloorRectangle.area located
  rewrite programSide, List.filterCongMem (List.pairs tiles) keep (p => allRedOrGreen tiles (Rectangle.ofPair p)) (programTest tiles)
    in Eq.sym (specAreas tiles)

theorem part2Correct (tiles: List Point): Part2 tiles (solvePart2 tiles) :=
  let areas := List.map (List.filter (rectangles tiles) (allRedOrGreen tiles)) Rectangle.area
  let same: solvePart2 tiles = largest areas := Eq.cong largest (programAreas tiles)
  rewrite same in largestIsLargest areas
