-- Widening a warehouse where nothing overlaps gives a wide one where
-- nothing overlaps (`widenSeparate`), so part 2 starts with whole boxes.

namespace Aoc.Year2024.Day15.Proofs
import Aoc.Year2024.Day15 (..)
import Aoc.Year2024.Day15.Spec (..)
import Std (And, Bool, Eq, Exists, Iff, List, Map, Nat, Not, Or, Set, Void)

-- A set built from a list holds only what the list holds.
theorem fromListElim (keys: List Position) (key: Position) (held: (Set.fromList keys).contains key = True): key ∈ keys :=
  List.anyTrueElim keys _ _ (rewrite Set.containsFromList key keys at held)
    (other member same => rewrite Map.Spec.sameKeySound key other same in member)

-- Each wall of the wide warehouse is half of a wall of the narrow one.
theorem wideWall (warehouse: Warehouse) (cell: Position) (held: warehouse.widen.walls.contains cell = True):
    ∃ (wall: Position) => warehouse.walls.contains wall = True ∧ cell ∈ cellsOf wall.widen :=
  List.anyElim _ _ warehouse.walls.toList
    (List.memFlatMapElim ((wall: Position) => cellsOf wall.widen) cell warehouse.walls.toList
      (fromListElim (warehouse.walls.toList.flatMap (wall => cellsOf wall.widen)) cell held))
    (wall member half => Witness wall (Both (Iff.forward (Set.memToList warehouse.walls wall) member) half))

-- Each box of the wide warehouse is a box of the narrow one, widened.
theorem wideBox (warehouse: Warehouse) (box: Position) (held: warehouse.widen.boxes.contains box = True):
    ∃ (narrow: Position) => warehouse.boxes.contains narrow = True ∧ narrow.widen = box :=
  Iff.forward (Set.containsMap warehouse.boxes Position.widen box) held

-- The two cells a tile becomes are in its row, at twice its column or one
-- more.
theorem cellOfWide (position: Position) (cell: Position) (half: cell ∈ cellsOf position.widen):
    And (cell.row = position.row) (Or (cell.column = 2 * position.column) (cell.column = 2 * position.column + 1)) :=
  match half with
    | Inl same => Both (Eq.sym (Eq.cong (here => here.row) same)) (Inl (Eq.sym (Eq.cong (here => here.column) same)))
    | Inr (Inl same) => Both (Eq.sym (Eq.cong (here => here.row) same)) (Inr (Eq.sym (Eq.cong (here => here.column) same)))
    | Inr (Inr none) => Void.exfalso none

-- Two tiles whose wide cells meet are the same tile.
theorem sameTile (position: Position) (other: Position) (cell: Position) (half: cell ∈ cellsOf position.widen) (otherHalf: cell ∈ cellsOf other.widen):
    position = other :=
  let here := cellOfWide position cell half
  let there := cellOfWide other cell otherHalf
  positionEq position other (omega [And.left here, And.left there]) (omega [And.right here, And.right there])

-- Widening keeps everything apart.
theorem widenSeparate (warehouse: Warehouse) (separate: Separate warehouse): WideSeparate warehouse.widen :=
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
                  Void.exfalso (omega [Eq.cong (here => here.column) same, Eq.cong (here => here.column) otherSame])))
      (Both
        (Bool.falseOfNotTrue _ (wallHeld =>
          match wideWall warehouse robot.widen wallHeld with
            | Witness wall (Both isWall wallHalf) =>
              let atWall := sameTile robot wall robot.widen (Inl rfl) wallHalf
              Bool.trueNotFalse (Eq.trans (Eq.sym (rewrite <- atWall at isWall)) robotOffWalls)))
        (Both
          (Bool.falseOfNotTrue _ (boxHeld =>
            match wideBox warehouse robot.widen boxHeld with
              | Witness narrow (Both isBox same) =>
                let atRobot :=
                  positionEq narrow robot (Eq.cong (here => here.row) same) (omega [Eq.cong (here => here.column) same])
                Bool.trueNotFalse (Eq.trans (Eq.sym (rewrite atRobot at isBox)) robotNotBoxed)))
          (Bool.falseOfNotTrue _ (leftHeld =>
            match wideBox warehouse (robot.widen.step Left) leftHeld with
              | Witness narrow (Both isBox same) => Void.exfalso (omega [Eq.cong (here => here.column) same]))))))

-- Part 2 from a warehouse where nothing overlaps: after every move the
-- robot is on no wall or box, and every box is whole.
theorem part2Whole (warehouse: Warehouse) (moves: List Direction) (separate: Separate warehouse):
    And (WideSeparate (warehouse.widen.moveAllWide moves)) (Whole (warehouse.widen.moveAllWide moves)) :=
  Both (moveAllWideSeparate warehouse.widen moves (widenSeparate warehouse separate))
    (moveAllWideWhole warehouse.widen moves (widenSeparate warehouse separate))

-- Widening sends different positions to different places.
theorem widenInjective (position: Position) (other: Position) (same: position.widen = other.widen): position = other :=
  positionEq position other (Eq.cong (here => here.row) same) (omega [Eq.cong (here => here.column) same])

-- Widening keeps the number of boxes, and so does every move after it.
theorem part2Count (warehouse: Warehouse) (moves: List Direction) (separate: Separate warehouse):
    boxCount (warehouse.widen.moveAllWide moves) = boxCount warehouse :=
  Eq.trans (moveAllWideCount warehouse.widen moves (widenSeparate warehouse separate))
    (Set.sizeMapInjective warehouse.boxes Position.widen (x y inX inY same => widenInjective x y same))
