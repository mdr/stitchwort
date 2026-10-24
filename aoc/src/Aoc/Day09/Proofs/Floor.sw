-- The floor through the key columns and rows (`Floor.of`): the program's
-- test of a rectangle, four lookups in the summed-area table, says that
-- every key tile of the rectangle is red or green by the spec
-- (`allRedOrGreenKeys`). Which key tiles those are, and why they are enough,
-- is Compress.sw.
--   1. A tile's test with only the lines that touch its row is the spec's
--      test with all of them (`isRedOrGreenNear`): a line that puts the tile
--      on the loop, or crosses its row, touches the row.
--   2. So a cell of the floor is 0 exactly when its key tile is red or
--      green (`cellAt`).
--   3. The table's block is the sum of its cells (`PrefixSums.blockSum`),
--      and a sum of cells is 0 exactly when each cell is.

namespace Aoc.Day09.Proofs
import Aoc.Day09 (..)
import Aoc.Day09.Spec (..)
import Std (Bool, DecEq, Decidable, Eq, List, Nat, PrefixSums, Void)

-- The key tile at key column c and key row r.
def keyTile (floor: Floor) (c: Nat) (r: Nat): Tile := { x = List.getOr 0 c floor.columns, y = List.getOr 0 r floor.rows }

-- The floor's cells.
def floorCells (tiles: List Tile): List (List Nat) :=
  Floor.outsideCells (loopLines tiles) (Floor.of tiles).columns (Floor.of tiles).rows

-- 1. Only lines that touch a tile's row matter ---------------------------------

theorem halfOpenBetween (one: Nat) (other: Nat) (value: Nat) (h: isBetweenHalfOpen one other value = True): isBetween one other value = True :=
  Bool.orElim _ _ _ h
    (l => Bool.orLeft (one <= value && value <= other) (other <= value && value <= one) (omega))
    (r => Bool.orRight (one <= value && value <= other) (other <= value && value <= one) (omega))

theorem onLineTouches (tile: Tile) (line: (Tile, Tile)) (h: isOnLine tile line = True): touchesRow tile.y line = True :=
  Bool.andRight (isBetween line.fst.x line.snd.x tile.x) (isBetween line.fst.y line.snd.y tile.y) h

theorem crossesTouches (tile: Tile) (line: (Tile, Tile)) (h: crossesRightOf tile line = True): touchesRow tile.y line = True :=
  halfOpenBetween line.fst.y line.snd.y tile.y (Bool.andRight _ _ (Bool.andRight _ _ h))

theorem isRedOrGreenNear (tiles: List Tile) (tile: Tile):
    isRedOrGreen (List.filter (touchesRow tile.y) (loopLines tiles)) tile = redOrGreen tiles tile :=
  rewrite List.anyFilter (isOnLine tile) (touchesRow tile.y) (onLineTouches tile) (loopLines tiles),
    List.countFilter (crossesRightOf tile) (touchesRow tile.y) (crossesTouches tile) (loopLines tiles)
    in rfl

-- 2. The cells -------------------------------------------------------------------

-- 1 outside the loop, 0 for a red or green tile.
def outsideFlag (redOrGreen: Bool): Nat := if redOrGreen then 0 else 1

theorem cellAt (tiles: List Tile) (r: Nat) (c: Nat) (hr: r < List.length (Floor.of tiles).rows) (hc: c < List.length (Floor.of tiles).columns):
    PrefixSums.cell (floorCells tiles) r c = outsideFlag (redOrGreen tiles (keyTile (Floor.of tiles) c r)) :=
  let floor := Floor.of tiles
  let lines := loopLines tiles
  let y := List.getOr 0 r floor.rows
  rewrite List.getOrMapLt (y => Floor.outsideRow (List.filter (touchesRow y) lines) floor.columns y) 0 Nil r floor.rows hr,
    List.getOrMapLt (x => if isRedOrGreen (List.filter (touchesRow y) lines) { x, y } then 0 else 1) 0 0 c floor.columns hc,
    isRedOrGreenNear tiles (keyTile floor c r)
    in rfl

-- A cell is 0 exactly when its tile is red or green.
theorem outsideFlagZero: (b: Bool) -> outsideFlag b = 0 -> b = True
  | True, h => rfl
  | False, h => Void.exfalso (Nat.succNotZero 0 h)

-- Every row of the floor is as long as the key columns.
theorem lengthCellRow (tiles: List Tile) (r: Nat) (hr: r < List.length (Floor.of tiles).rows):
    List.length (List.getOr Nil r (floorCells tiles)) = List.length (Floor.of tiles).columns :=
  let floor := Floor.of tiles
  let lines := loopLines tiles
  rewrite List.getOrMapLt (y => Floor.outsideRow (List.filter (touchesRow y) lines) floor.columns y) 0 Nil r floor.rows hr
    in List.lengthMap _ floor.columns

-- 3. The program's test of a rectangle -----------------------------------------

-- Two corners whose key positions are inside the floor.
def Inside (floor: Floor) (first: Corner) (second: Corner): Prop :=
  And (And (first.column < List.length floor.columns) (second.column < List.length floor.columns))
    (And (first.row < List.length floor.rows) (second.row < List.length floor.rows))

-- Every key tile from one corner's key column and row to the other's.
def allKeys (tiles: List Tile) (first: Corner) (second: Corner): Bool :=
  List.all
    (r => List.all (c => redOrGreen tiles (keyTile (Floor.of tiles) c r)) (List.between (Nat.min first.column second.column) (Nat.max first.column second.column)))
    (List.between (Nat.min first.row second.row) (Nat.max first.row second.row))

theorem allRedOrGreenKeys (tiles: List Tile) (first: Corner) (second: Corner) (inside: Inside (Floor.of tiles) first second):
    Floor.allRedOrGreen (Floor.of tiles) (first, second) = allKeys tiles first second :=
  let floor := Floor.of tiles
  let cells := floorCells tiles
  let top := Nat.min first.row second.row
  let bottom := Nat.max first.row second.row + 1
  let left := Nat.min first.column second.column
  let right := Nat.max first.column second.column + 1
  match inside with
    | Both (Both c1 c2) (Both r1 r2) =>
      let rowsLength: List.length cells = List.length floor.rows := List.lengthMap _ floor.rows
      let widthLe: List.length floor.columns <= List.maxLength cells :=
        rewrite <- lengthCellRow tiles 0 (omega) in List.lengthLeMaxLength 0 cells
      let blockIs: PrefixSums.block floor.outside top bottom left right = PrefixSums.blockSpec cells top bottom left right :=
        PrefixSums.blockSum cells top bottom left right (omega) (omega) (omega) (omega)
      -- The sum of a row of the block.
      let rowSum: Nat -> Nat := r => List.sumBy (c => PrefixSums.cell cells r c) (List.rangeFrom (right - left) left)
      Bool.eqOf (Floor.allRedOrGreen floor (first, second)) (allKeys tiles first second)
        (h =>
          let zero: PrefixSums.blockSpec cells top bottom left right = 0 := rewrite <- blockIs in DecEq.sound _ 0 h
          List.allBetweenIntro _ top (Nat.max first.row second.row) (r rlo rhi =>
            let rowZero: rowSum r = 0 :=
              List.sumByZeroElim rowSum (List.rangeFrom (bottom - top) top) zero r (List.memRangeFromIntro r (bottom - top) top rlo (omega))
            List.allBetweenIntro _ left (Nat.max first.column second.column) (c clo chi =>
              let cellZero: PrefixSums.cell cells r c = 0 :=
                List.sumByZeroElim (c => PrefixSums.cell cells r c) (List.rangeFrom (right - left) left) rowZero c
                  (List.memRangeFromIntro c (right - left) left clo (omega))
              outsideFlagZero (redOrGreen tiles (keyTile floor c r)) (rewrite cellAt tiles r c (omega) (omega) at cellZero))))
        (h =>
          let zero: PrefixSums.blockSpec cells top bottom left right = 0 :=
            List.sumByZeroIntro rowSum (List.rangeFrom (bottom - top) top) (r rm =>
              let rowIn := List.memRangeFrom r (bottom - top) top rm
              let rowAll := List.allBetweenElim _ top (Nat.max first.row second.row) h r (rowIn.left) (omega)
              List.sumByZeroIntro (c => PrefixSums.cell cells r c) (List.rangeFrom (right - left) left) (c cm =>
                let colIn := List.memRangeFrom c (right - left) left cm
                rewrite cellAt tiles r c (omega) (omega), List.allBetweenElim _ left (Nat.max first.column second.column) rowAll c (colIn.left) (omega) in rfl))
          Decidable.toBoolOf (Nat.decEq (PrefixSums.block floor.outside top bottom left right) 0) (Eq.trans blockIs zero))
