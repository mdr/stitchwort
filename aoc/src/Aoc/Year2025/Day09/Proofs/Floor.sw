--| The floor through the key columns and rows (`Floor.of`): the program's
--| test of a rectangle, four lookups in the summed-area table, says that
--| every key tile of the rectangle is red or green by the spec
--| (`allRedOrGreenKeys`). Which key tiles those are, and why they are enough,
--| is Compress.sw.
--
--   1. A tile's test with only the lines that touch its row is the spec's
--      test with all of them (`isRedOrGreenNear`): a line that puts the tile
--      on the loop, or crosses its row, touches the row.
--   2. So a cell of the floor is 0 exactly when its key tile is red or
--      green (`cellAt`).
--   3. The table's block is the sum of its cells (`PrefixSums.blockSum`),
--      and a sum of cells is 0 exactly when each cell is.

namespace Aoc.Year2025.Day09.Proofs
import Aoc.Common (Line, Point, PrefixSums)
import Aoc.Common.Proofs (..)
import Aoc.Year2025.Day09 (..)
import Aoc.Year2025.Day09.Spec (..)
import Std (Bool, DecEq, Decidable, Eq, List, Nat, Void)

--| The key tile at key column c and key row r.
def keyTile (floor: Floor) (c: Nat) (r: Nat): Point := { x = List.getOr floor.columns c 0, y = List.getOr floor.rows r 0 }

--| The floor's cells.
def floorCells (tiles: List Point): List (List Nat) :=
  Floor.outsideCells (loopLines tiles) (Floor.of tiles).columns (Floor.of tiles).rows

-- 1. Only lines that touch a tile's row matter ---------------------------------

theorem halfOpenBetween (one: Nat) (other: Nat) (value: Nat) (h: isBetweenHalfOpen one other value = True): isBetween one other value = True :=
  match h with
    | Inl l => Inl (omega)
    | Inr r => Inr (omega)

theorem onLineTouches (tile: Point) (line: Line) (h: tile.isOnLine line = True): touchesRow tile.y line = True :=
  h.right

theorem crossesTouches (tile: Point) (line: Line) (h: crossesRightOf tile line = True): touchesRow tile.y line = True :=
  let Both _ (Both _ half) := h
  halfOpenBetween line.from.y line.to.y tile.y half

theorem isRedOrGreenNear (tiles: List Point) (tile: Point):
    isRedOrGreen (List.filter (loopLines tiles) (touchesRow tile.y)) tile = redOrGreen tiles tile :=
  rewrite List.anyFilter (loopLines tiles) tile.isOnLine (touchesRow tile.y) (onLineTouches tile),
    List.countFilter (loopLines tiles) (crossesRightOf tile) (touchesRow tile.y) (crossesTouches tile)
    in rfl

-- 2. The cells -------------------------------------------------------------------

--| 1 outside the loop, 0 for a red or green tile.
def outsideFlag (redOrGreen: Bool): Nat := if redOrGreen then 0 else 1

theorem cellAt (tiles: List Point) (r: Nat) (c: Nat) (hr: r < List.length (Floor.of tiles).rows) (hc: c < List.length (Floor.of tiles).columns):
    PrefixSums.cell (floorCells tiles) r c = outsideFlag (redOrGreen tiles (keyTile (Floor.of tiles) c r)) :=
  let floor := Floor.of tiles
  let lines := loopLines tiles
  let y := List.getOr floor.rows r 0
  rewrite List.getOrMapLt floor.rows r 0 [] hr (y => Floor.outsideRow (List.filter lines (touchesRow y)) floor.columns y),
    List.getOrMapLt floor.columns c 0 0 hc (x => if isRedOrGreen (List.filter lines (touchesRow y)) { x, y } then 0 else 1),
    isRedOrGreenNear tiles (keyTile floor c r)
    in rfl

--| A cell is 0 exactly when its tile is red or green.
theorem outsideFlagZero (b: Bool) (h: outsideFlag b = 0): b = True :=
  match b with
    | True => rfl
    | False => Void.exfalso (Nat.succNotZero 0 h)

--| Every row of the floor is as long as the key columns.
theorem lengthCellRow (tiles: List Point) (r: Nat) (hr: r < List.length (Floor.of tiles).rows):
    List.length (List.getOr (floorCells tiles) r []) = List.length (Floor.of tiles).columns :=
  let floor := Floor.of tiles
  let lines := loopLines tiles
  rewrite List.getOrMapLt floor.rows r 0 [] hr (y => Floor.outsideRow (List.filter lines (touchesRow y)) floor.columns y)
    in List.lengthMap floor.columns _

-- 3. The program's test of a rectangle -----------------------------------------

--| Two corners whose key positions are inside the floor.
def Inside (floor: Floor) (first: Corner) (second: Corner): Prop :=
  ((first.column < List.length floor.columns) ∧ (second.column < List.length floor.columns)) ∧ ((first.row < List.length floor.rows) ∧ (second.row < List.length floor.rows))

--| Every key tile from one corner's key column and row to the other's.
def allKeys (tiles: List Point) (first: Corner) (second: Corner): Bool :=
  List.all
    (List.range (Nat.min first.row second.row) (Nat.max first.row second.row + 1))
    (r => List.all (List.range (Nat.min first.column second.column) (Nat.max first.column second.column + 1)) (c => redOrGreen tiles (keyTile (Floor.of tiles) c r)))

theorem allRedOrGreenKeys (tiles: List Point) (first: Corner) (second: Corner) (inside: Inside (Floor.of tiles) first second):
    Floor.allRedOrGreen (Floor.of tiles) { corner = first, opposite = second } = allKeys tiles first second :=
  let floor := Floor.of tiles
  let cells := floorCells tiles
  let top := Nat.min first.row second.row
  let bottom := Nat.max first.row second.row + 1
  let left := Nat.min first.column second.column
  let right := Nat.max first.column second.column + 1
  match inside with
    | Both (Both c1 c2) (Both r1 r2) =>
      let rowsLength: List.length cells = List.length floor.rows := List.lengthMap floor.rows _
      let widthLe: List.length floor.columns ≤ List.maxLength cells :=
        rewrite <- lengthCellRow tiles 0 (omega) in List.lengthLeMaxLength cells 0
      let blockIs: PrefixSums.block floor.outside top bottom left right = PrefixSums.blockSpec cells top bottom left right :=
        PrefixSums.blockSum cells top bottom left right (omega) (omega) (omega) (omega)
      let lastRow := Nat.max first.row second.row
      let lastColumn := Nat.max first.column second.column
      -- The sum of a row of the block.
      let rowSum: Nat → Nat := r => List.sumBy (List.range left (lastColumn + 1)) (c => PrefixSums.cell cells r c)
      Bool.eqOf (Floor.allRedOrGreen floor { corner = first, opposite = second }) (allKeys tiles first second)
        (h =>
          let zero: PrefixSums.blockSpec cells top bottom left right = 0 := rewrite <- blockIs in h.read
          List.allBetweenIntro (r rlo rhi =>
            let rowZero: rowSum r = 0 :=
              List.sumByZeroElim (List.range top (lastRow + 1)) rowSum zero r (((List.memRange r top (lastRow + 1)).backward (Both rlo (Nat.leLessSucc r lastRow rhi))))
            List.allBetweenIntro (c clo chi =>
              let cellZero: PrefixSums.cell cells r c = 0 :=
                List.sumByZeroElim (List.range left (lastColumn + 1)) (c => PrefixSums.cell cells r c) rowZero c
                  (((List.memRange c left (lastColumn + 1)).backward (Both clo (Nat.leLessSucc c lastColumn chi))))
              outsideFlagZero (redOrGreen tiles (keyTile floor c r)) (rewrite cellAt tiles r c (omega) (omega) at cellZero))))
        (h =>
          let zero: PrefixSums.blockSpec cells top bottom left right = 0 :=
            List.sumByZeroIntro (List.range top (lastRow + 1)) rowSum (r rm =>
              let rowIn := ((List.memRange _ _ _).forward rm)
              let rowAll := List.allBetweenElim h rowIn.left rowIn.right
              List.sumByZeroIntro (List.range left (lastColumn + 1)) (c => PrefixSums.cell cells r c) (c cm =>
                let colIn := ((List.memRange _ _ _).forward cm)
                rewrite cellAt tiles r c (omega) (omega), List.allBetweenElim rowAll colIn.left colIn.right in rfl))
          (Nat.decEq (PrefixSums.block floor.outside top bottom left right) 0).complete (Eq.trans blockIs zero))
