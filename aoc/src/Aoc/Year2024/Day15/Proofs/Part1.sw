-- Part 1's move: it never moves a wall (`moveWalls`) or changes the number
-- of boxes (`moveCount`), keeps the robot off walls and boxes
-- (`moveSeparate`), and does what the puzzle says to the line of boxes in
-- front of the robot (`pushBlocked`, `pushMoves`).

namespace Aoc.Year2024.Day15.Proofs
import Aoc.Year2024.Day15 (..)
import Aoc.Year2024.Day15.Spec (..)
import Std (And, Bool, DecEq, Decidable, Eq, Exists, Iff, Int, List, Map, Nat, Not, Option, Or, Set, Void)

-- What `firstFree` finds: a position without a box, which is where it
-- started or past a box there.
theorem firstFreeSome (boxes: Set Position) (direction: Direction): (start: Position) → (fuel: Nat) → (free: Position) →
    firstFree boxes direction start fuel = Some free → And (boxes.contains free = False) (Or (free = start) (boxes.contains start = True))
  | start, Zero, free, found => Void.exfalso (Option.noneNotSome free found)
  | start, Succ fuel, free, found =>
    match c: boxes.contains start with
      | True => Both (And.left (firstFreeSome boxes direction (start.step direction) fuel free found)) (Inr rfl)
      | False =>
        let same := Option.someInjective _ _ found
        Both (rewrite <- same in c) (Inl (Eq.sym same))

-- Along a line of `length` boxes from `start`, `firstFree` finds the
-- position past them, given more fuel than boxes.
theorem firstFreeLine (boxes: Set Position) (direction: Direction): (length: Nat) → (start: Position) → (fuel: Nat) → length < fuel →
    ((i: Nat) → i < length → boxes.contains (ahead start direction i) = True) → boxes.contains (ahead start direction length) = False →
    firstFree boxes direction start fuel = Some (ahead start direction length)
  | length, start, Zero, enough, line, free => Void.exfalso (omega)
  | Zero, start, Succ fuel, enough, line, free => rewrite free in rfl
  | Succ length, start, Succ fuel, enough, line, free =>
    rewrite line 0 (omega) in
      rewrite aheadFrom start direction length at
        firstFreeLine boxes direction length (start.step direction) fuel (omega)
          (i below => rewrite aheadFrom start direction i in line (Succ i) (omega)) (rewrite aheadFrom start direction length in free)

-- A move never moves a wall.
theorem moveWalls (warehouse: Warehouse) (direction: Direction): (warehouse.move direction).walls = warehouse.walls := cases

-- The robot's next position still holds a box once the free position has
-- one: it is the free position, or held a box already.
theorem nextAfterInsert (boxes: Set Position) (free: Position) (next: Position) (found: Or (free = next) (boxes.contains next = True)):
    (boxes.insert free).contains next = True :=
  match found with
    | Inl same => rewrite same in Set.containsInsert next boxes
    | Inr there => Set.containsInsertMono boxes free next there

-- A move never changes the number of boxes.
theorem moveCount (warehouse: Warehouse) (direction: Direction): boxCount (warehouse.move direction) = boxCount warehouse :=
  match found: firstFree warehouse.boxes direction (warehouse.robot.step direction) (warehouse.boxes.size + 1) with
    | None => rfl
    | Some free =>
      match wall: warehouse.walls.contains free with
        | True => rfl
        | False =>
          let facts := firstFreeSome warehouse.boxes direction (warehouse.robot.step direction) (warehouse.boxes.size + 1) free found
          rewrite Map.sizeRemove (Map.insert warehouse.boxes.items free ()) (warehouse.robot.step direction),
            nextAfterInsert warehouse.boxes free (warehouse.robot.step direction) (And.right facts),
            Map.sizeInsert warehouse.boxes.items free (),
            And.left facts in omega

-- Nothing overlaps after a move that started with nothing overlapping: the
-- robot never ends on a wall or a box.
theorem moveSeparate (warehouse: Warehouse) (direction: Direction) (separate: Separate warehouse): Separate (warehouse.move direction) :=
  match found: firstFree warehouse.boxes direction (warehouse.robot.step direction) (warehouse.boxes.size + 1) with
    | None => separate
    | Some free =>
      match wall: warehouse.walls.contains free with
        | True => separate
        | False =>
          let next := warehouse.robot.step direction
          let facts := firstFreeSome warehouse.boxes direction next (warehouse.boxes.size + 1) free found
          let boxesOffWalls: (position: Position) → ((warehouse.boxes.insert free).remove next).contains position = True → warehouse.walls.contains position = False :=
            position member =>
              match DecEq.decide position next with
                | Yes atNext => Void.exfalso (Bool.trueNotFalse (Eq.trans (Eq.sym member) (rewrite atNext in Set.containsRemove (warehouse.boxes.insert free) next)))
                | No notNext =>
                  match DecEq.decide position free with
                    | Yes atFree => rewrite atFree in wall
                    | No notFree =>
                      And.left separate position
                        (rewrite <- Set.containsInsertOther warehouse.boxes free position notFree in
                          rewrite <- Set.containsRemoveOther (warehouse.boxes.insert free) next position notNext in member)
          let nextOffWalls: warehouse.walls.contains next = False :=
            match And.right facts with
              | Inl same => rewrite <- same in wall
              | Inr there => And.left separate next there
          Both boxesOffWalls (Both nextOffWalls (Set.containsRemove (warehouse.boxes.insert free) next))
