--| Widening a warehouse where nothing overlaps gives a wide one where
--| nothing overlaps (`widenSeparate`), so part 2 starts with whole boxes.

namespace Aoc.Year2024.Day15.Proofs
import Aoc.Common (Direction)
import Aoc.Common.Proofs (offsetExt, offsetStepComm, offsetStepInjective, offsetStepOpposite)
import Aoc.Year2024.Day15 (..)
import Aoc.Year2024.Day15.Spec (..)
import Std (And, Bool, Eq, Exists, Iff, List, Map, Nat, Not, Or, Set, Void)

--| Each wall of the wide warehouse is half of a wall of the narrow one.
theorem wideWall ∀ (warehouse: Warehouse) (cell: Cell) (held: warehouse.widen.walls.contains cell = True):
    ∃ (wall: Cell) => warehouse.walls.contains wall = True ∧ cell ∈ cellsOf (Cell.widen wall) :=
  List.anyElim _ _ warehouse.walls.toList
    (List.memFlatMapElim ((wall: Cell) => cellsOf (Cell.widen wall)) cell warehouse.walls.toList
      ((Set.containsFromListIff (warehouse.walls.toList.flatMap (wall => cellsOf (Cell.widen wall))) cell).forward held))
    (wall member half => Witness wall (Both (Iff.forward (Set.memToList warehouse.walls wall) member) half))

--| Each box of the wide warehouse is a box of the narrow one, widened.
theorem wideBox ∀ (warehouse: Warehouse) (box: Cell) (held: warehouse.widen.boxes.contains box = True):
    ∃ (narrow: Cell) => warehouse.boxes.contains narrow = True ∧ (Cell.widen narrow) = box :=
  Iff.forward (Set.containsMap warehouse.boxes Cell.widen box) held

--| The two cells a tile becomes are in its row, at twice its column or one
--| more.
theorem cellOfWide ∀ (position: Cell) (cell: Cell) (half: cell ∈ cellsOf (Cell.widen position)):
    (cell.rows = position.rows) ∧ ((cell.columns = 2 * position.columns) ∨ (cell.columns = 2 * position.columns + 1)) :=
  match half with
    | Inl same => Both (Eq.sym (Eq.cong (here => here.rows) same)) (Inl (Eq.sym (Eq.cong (here => here.columns) same)))
    | Inr (Inl same) => Both (omega [Eq.cong (here => here.rows) same]) (Inr (omega [Eq.cong (here => here.columns) same]))
    | Inr (Inr none) => Void.exfalso none

--| Two tiles whose wide cells meet are the same tile.
theorem sameTile ∀ (position: Cell) (other: Cell) (cell: Cell) (half: cell ∈ cellsOf (Cell.widen position)) (otherHalf: cell ∈ cellsOf (Cell.widen other)):
    position = other :=
  let here := cellOfWide position cell half
  let there := cellOfWide other cell otherHalf
  offsetExt position other (omega) (omega)

--| Widening keeps everything apart.
theorem widenSeparate ∀ (warehouse: Warehouse) (separate: Separate warehouse): WideSeparate warehouse.widen :=
  let boxesOffWalls := And.left separate
  let robotOffWalls := And.left (And.right separate)
  let robotNotBoxed := And.right (And.right separate)
  let robot := warehouse.robot
  Both
    (box held cell own =>
      Bool.falseOfNotTrue _ (wallHeld =>
        match wideWall warehouse cell wallHeld with
          | Witness wall (Both isWall wallHalf) =>
            match wideBox warehouse box held with
              | Witness narrow (Both isBox same) =>
                let atWall := sameTile narrow wall cell (rewrite <- same at own) wallHalf
                Bool.trueNotFalse (Eq.trans (Eq.sym (rewrite <- atWall at isWall)) (boxesOffWalls narrow isBox))))
    (Both
      (box held =>
        Bool.falseOfNotTrue _ (rightHeld =>
          match wideBox warehouse box held with
            | Witness narrow (Both isBox same) =>
              match wideBox warehouse (box.step Right) rightHeld with
                | Witness other (Both otherBox otherSame) =>
                  Void.exfalso (omega [Eq.cong (here => here.columns) same, Eq.cong (here => here.columns) otherSame])))
      (Both
        (Bool.falseOfNotTrue _ (wallHeld =>
          match wideWall warehouse (Cell.widen robot) wallHeld with
            | Witness wall (Both isWall wallHalf) =>
              let atWall := sameTile robot wall (Cell.widen robot) (Inl rfl) wallHalf
              Bool.trueNotFalse (Eq.trans (Eq.sym (rewrite <- atWall at isWall)) robotOffWalls)))
        (Both
          (Bool.falseOfNotTrue _ (boxHeld =>
            match wideBox warehouse (Cell.widen robot) boxHeld with
              | Witness narrow (Both isBox same) =>
                let atRobot :=
                  offsetExt narrow robot (Eq.cong (here => here.rows) same) (omega [Eq.cong (here => here.columns) same])
                Bool.trueNotFalse (Eq.trans (Eq.sym (rewrite atRobot at isBox)) robotNotBoxed)))
          (Bool.falseOfNotTrue _ (leftHeld =>
            match wideBox warehouse ((Cell.widen robot).step Left) leftHeld with
              | Witness narrow (Both isBox same) => Void.exfalso (omega [Eq.cong (here => here.columns) same]))))))

--| Part 2 from a warehouse where nothing overlaps: after every move the
--| robot is on no wall or box, and every box is whole.
theorem part2Whole ∀ (warehouse: Warehouse) (moves: List Direction) (separate: Separate warehouse):
    (WideSeparate (warehouse.widen.moveAllWide moves)) ∧ (Whole (warehouse.widen.moveAllWide moves)) :=
  Both (moveAllWideSeparate warehouse.widen moves (widenSeparate warehouse separate))
    (moveAllWideWhole warehouse.widen moves (widenSeparate warehouse separate))

--| Widening sends different positions to different places.
theorem widenInjective ∀ (position: Cell) (other: Cell) (same: (Cell.widen position) = (Cell.widen other)): position = other :=
  offsetExt position other (Eq.cong (here => here.rows) same) (omega [Eq.cong (here => here.columns) same])

--| Widening keeps the number of boxes, and so does every move after it.
theorem part2Count ∀ (warehouse: Warehouse) (moves: List Direction) (separate: Separate warehouse):
    boxCount (warehouse.widen.moveAllWide moves) = boxCount warehouse :=
  Eq.trans (moveAllWideCount warehouse.widen moves (widenSeparate warehouse separate))
    (Set.sizeMapInjective warehouse.boxes Cell.widen (x y inX inY same => widenInjective x y same))
