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

-- A line of boxes is no longer than the boxes there are.
theorem lineAtMostBoxes (warehouse: Warehouse) (direction: Direction) (length: Nat) (line: LineOfBoxes warehouse direction length):
    length ≤ warehouse.boxes.size :=
  countAtMostSize (i => ahead warehouse.robot direction (i + 1)) length warehouse.boxes (And.left line)
    (i j below belowJ same => omega [aheadInjective warehouse.robot direction (i + 1) (j + 1) same])

-- With a line of boxes in front of the robot, `firstFree` finds the
-- position past it.
theorem lineFree (warehouse: Warehouse) (direction: Direction) (length: Nat) (line: LineOfBoxes warehouse direction length):
    firstFree warehouse.boxes direction (warehouse.robot.step direction) (warehouse.boxes.size + 1) = Some (pastLine warehouse direction length) :=
  rewrite Nat.addOne length, <- aheadFrom warehouse.robot direction length in
    firstFreeLine warehouse.boxes direction length (warehouse.robot.step direction) (warehouse.boxes.size + 1)
      (omega [lineAtMostBoxes warehouse direction length line])
      (i below => rewrite aheadFrom warehouse.robot direction i in (rewrite Nat.addOne i at And.left line i below))
      (rewrite aheadFrom warehouse.robot direction length in (rewrite Nat.addOne length at And.right line))

-- "If this action would cause the robot or a box to move into a wall (#),
-- nothing moves instead, including the robot."
theorem pushBlocked (warehouse: Warehouse) (direction: Direction) (length: Nat) (line: LineOfBoxes warehouse direction length)
    (wall: warehouse.walls.contains (pastLine warehouse direction length) = True): warehouse.move direction = warehouse :=
  rewrite lineFree warehouse direction length line, wall in rfl

-- The boxes after a push, as the program finds them: the free position
-- past the line gains a box, and the robot's next position loses one.
def pushedBoxes (warehouse: Warehouse) (direction: Direction) (length: Nat): Set Position :=
  (warehouse.boxes.insert (pastLine warehouse direction length)).remove (warehouse.robot.step direction)

-- Each box the program has after a push is one the puzzle has.
theorem pushedForward (warehouse: Warehouse) (direction: Direction) (length: Nat) (line: LineOfBoxes warehouse direction length)
    (position: Position) (member: (pushedBoxes warehouse direction length).contains position = True): BoxAfterPush warehouse direction length position :=
  let next := warehouse.robot.step direction
  let free := pastLine warehouse direction length
  match DecEq.decide position next with
    | Yes atNext =>
      Void.exfalso (Bool.trueNotFalse (Eq.trans (Eq.sym member) (rewrite atNext in Set.containsRemove (warehouse.boxes.insert free) next)))
    | No notNext =>
      let inserted := rewrite Set.containsRemoveOther (warehouse.boxes.insert free) next position notNext at member
      match DecEq.decide position free with
        | Yes atFree =>
          match length with
            | Zero => Void.exfalso (notNext atFree)
            | Succ shorter => Inl (Witness shorter (Both (omega) atFree))
        | No notFree =>
          let boxed := rewrite Set.containsInsertOther warehouse.boxes free position notFree at inserted
          match decideAhead warehouse.robot direction length position with
            | Inl (Witness j (Both below same)) =>
              match j with
                | Zero => Void.exfalso (notNext same)
                | Succ earlier => Inl (Witness earlier (Both (omega) same))
            | Inr notLine => Inr (Both boxed notLine)

-- Each box the puzzle has after a push is one the program has.
theorem pushedBackward (warehouse: Warehouse) (direction: Direction) (length: Nat) (line: LineOfBoxes warehouse direction length)
    (position: Position) (after: BoxAfterPush warehouse direction length position): (pushedBoxes warehouse direction length).contains position = True :=
  let next := warehouse.robot.step direction
  let free := pastLine warehouse direction length
  match after with
    | Inl (Witness i (Both below same)) =>
      let notNext: Not (position = next) := atNext => omega [aheadInjective warehouse.robot direction (Succ (i + 1)) 1 (Eq.trans (Eq.sym same) atNext)]
      rewrite Set.containsRemoveOther (warehouse.boxes.insert free) next position notNext in
        match DecEq.decide (i + 1) length with
          | Yes last =>
            let atFree: position = free := rewrite same, <- last, aheadAddOne warehouse.robot direction (i + 1) in rfl
            rewrite atFree in Set.containsInsert free warehouse.boxes
          | No inside => Set.containsInsertMono warehouse.boxes free position
              (rewrite same, <- aheadAddOne warehouse.robot direction (i + 1) in And.left line (i + 1) (omega))
    | Inr (Both boxed notLine) =>
      match DecEq.decide position next with
        | Yes atNext =>
          match length with
            | Zero => Void.exfalso (Bool.trueNotFalse (Eq.trans (Eq.sym boxed) (rewrite atNext in And.right line)))
            | Succ shorter => Void.exfalso (notLine 0 (omega) atNext)
        | No notNext =>
          rewrite Set.containsRemoveOther (warehouse.boxes.insert free) next position notNext in
            Set.containsInsertMono warehouse.boxes free position boxed

-- "The robot will also attempt to push those boxes": when nothing blocks
-- the line, the robot steps forward, and the boxes are the puzzle's.
theorem pushMoves (warehouse: Warehouse) (direction: Direction) (length: Nat) (line: LineOfBoxes warehouse direction length)
    (open: warehouse.walls.contains (pastLine warehouse direction length) = False):
    And ((warehouse.move direction).robot = warehouse.robot.step direction)
      ((position: Position) → Iff ((warehouse.move direction).boxes.contains position = True) (BoxAfterPush warehouse direction length position)) :=
  rewrite lineFree warehouse direction length line, open in
    Both rfl
      (position => {
        forward = pushedForward warehouse direction length line position,
        backward = pushedBackward warehouse direction length line position
      })

-- From `start`, either the boxes in a line end within `fuel` positions, or
-- all `fuel` positions hold boxes.
theorem boxesEndOrFill (boxes: Set Position) (direction: Direction): (start: Position) → (fuel: Nat) →
    Or (∃ (length: Nat) => length < fuel ∧ ((i: Nat) → i < length → boxes.contains (ahead start direction i) = True) ∧ boxes.contains (ahead start direction length) = False)
      ((i: Nat) → i < fuel → boxes.contains (ahead start direction i) = True)
  | start, Zero => Inr (i below => Void.exfalso (omega))
  | start, Succ fuel =>
    match here: boxes.contains start with
      | False => Inl (Witness 0 (Both (omega) (Both (i below => Void.exfalso (omega)) here)))
      | True =>
        let fromStart: (i: Nat) → (boxes.contains (ahead (start.step direction) direction i) = True) → boxes.contains (ahead start direction (Succ i)) = True :=
          i boxed => rewrite <- aheadFrom start direction i in boxed
        let atOrAfter: (k: Nat) → ((i: Nat) → i < k → boxes.contains (ahead (start.step direction) direction i) = True) → (i: Nat) → i < Succ k →
            boxes.contains (ahead start direction i) = True :=
          k rest i below =>
            match i with
              | Zero => here
              | Succ j => fromStart j (rest j (omega))
        match boxesEndOrFill boxes direction (start.step direction) fuel with
          | Inl (Witness length (Both below (Both boxed free))) =>
            Inl (Witness (Succ length) (Both (omega) (Both (atOrAfter length boxed) (rewrite <- aheadFrom start direction length in free))))
          | Inr full => Inr (atOrAfter fuel full)

-- Every move meets a line of boxes, maybe of none: so `pushBlocked` and
-- `pushMoves` say what every move does.
theorem lineExists (warehouse: Warehouse) (direction: Direction): ∃ (length: Nat) => LineOfBoxes warehouse direction length :=
  let next := warehouse.robot.step direction
  let fromRobot: (i: Nat) → warehouse.boxes.contains (ahead next direction i) = warehouse.boxes.contains (ahead warehouse.robot direction (i + 1)) :=
    i => rewrite aheadFrom warehouse.robot direction i, Nat.addOne i in rfl
  match boxesEndOrFill warehouse.boxes direction next (warehouse.boxes.size + 1) with
    | Inl (Witness length (Both below (Both boxed free))) =>
      Witness length (Both (i before => rewrite <- fromRobot i in boxed i before) (rewrite <- fromRobot length in free))
    | Inr full =>
      Void.exfalso
        (omega [
          countAtMostSize (i => ahead next direction i) (warehouse.boxes.size + 1) warehouse.boxes full
            (i j below belowJ same => aheadInjective next direction i j same)
        ])

-- After every move: the walls are where they were, the number of boxes is
-- the same, and nothing overlaps if nothing did at the start.
theorem moveAllWalls: (warehouse: Warehouse) → (moves: List Direction) → (warehouse.moveAll moves).walls = warehouse.walls
  | warehouse, Nil => rfl
  | warehouse, Cons move rest => Eq.trans (moveAllWalls (warehouse.move move) rest) (moveWalls warehouse move)

theorem moveAllCount: (warehouse: Warehouse) → (moves: List Direction) → boxCount (warehouse.moveAll moves) = boxCount warehouse
  | warehouse, Nil => rfl
  | warehouse, Cons move rest => Eq.trans (moveAllCount (warehouse.move move) rest) (moveCount warehouse move)

theorem moveAllSeparate: (warehouse: Warehouse) → (moves: List Direction) → Separate warehouse → Separate (warehouse.moveAll moves)
  | warehouse, Nil, separate => separate
  | warehouse, Cons move rest, separate => moveAllSeparate (warehouse.move move) rest (moveSeparate warehouse move separate)
