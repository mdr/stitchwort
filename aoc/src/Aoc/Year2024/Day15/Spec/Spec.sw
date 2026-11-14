--| Day 15 as the puzzle states it, over the program's `Warehouse` and
--| `step` (a cell's neighbour). The proofs (Proofs/) show the program's
--| moves do what these say, for every warehouse and every move.

namespace Aoc.Year2024.Day15.Spec
import Aoc.Common (Direction)
import Aoc.Year2024.Day15 (..)
import Std (And, Bool, Exists, Iff, List, Nat, Not, Or, Set)

--| The position `count` steps from `position` in `direction`.
def ahead (position: Cell) (direction: Direction): (count: Nat) → Cell
  | Zero => position
  | Succ count => (ahead position direction count).step direction

--| "If there are any boxes (O) in the way": the `length` positions in front
--| of the robot hold boxes, and the one past them doesn't.
def LineOfBoxes (warehouse: Warehouse) (direction: Direction) (length: Nat): Prop :=
  (∀ (i: Nat) => i < length → warehouse.boxes.contains (ahead warehouse.robot direction (i + 1)) = True)
    ∧ warehouse.boxes.contains (ahead warehouse.robot direction (length + 1)) = False

--| Where the robot or the last box of the line would move to.
def pastLine (warehouse: Warehouse) (direction: Direction) (length: Nat): Cell :=
  ahead warehouse.robot direction (length + 1)

--| "The robot will also attempt to push those boxes": after the push there
--| is a box at `position` when a box of the line moved one step to it, or a
--| box not in the line was already there.
def BoxAfterPush (warehouse: Warehouse) (direction: Direction) (length: Nat) (position: Cell): Prop :=
  (∃ (i: Nat) => i < length ∧ position = (ahead warehouse.robot direction (i + 1)).step direction)
    ∨ (warehouse.boxes.contains position = True
      ∧ (∀ (i: Nat) => i < length → position ≠ ahead warehouse.robot direction (i + 1)))

--| The boxes the puzzle counts.
def boxCount (warehouse: Warehouse): Nat := warehouse.boxes.size

--| Nothing overlaps: no box on a wall, and the robot on neither.
def Separate (warehouse: Warehouse): Prop :=
  (∀ (position: Cell) => warehouse.boxes.contains position = True → warehouse.walls.contains position = False)
    ∧ warehouse.walls.contains warehouse.robot = False
    ∧ warehouse.boxes.contains warehouse.robot = False

-- Part 2. A box is where its `[` is; its `]` is the cell to the right.

--| What one cell of the wide map shows.
type WideTile = | WideWall | BoxLeft | BoxRight | WideRobot | WideFloor

--| The wide map's cell at `position`, as the puzzle draws it.
def wideTile (warehouse: Warehouse) (position: Cell): WideTile :=
  if position == warehouse.robot then WideRobot
  else if warehouse.walls.contains position then WideWall
  else if warehouse.boxes.contains position then BoxLeft
  else if warehouse.boxes.contains (position.step Left) then BoxRight
  else WideFloor

--| "Boxes are now twice as wide": every `[` has its `]` to the right, and
--| every `]` its `[` to the left.
def Whole (warehouse: Warehouse): Prop :=
  ∀ (position: Cell) => (wideTile warehouse position = BoxLeft) ↔ (wideTile warehouse (position.step Right) = BoxRight)

--| A wide warehouse where nothing overlaps: no box covers a wall or another
--| box's cells, and neither covers the robot.
def WideSeparate (warehouse: Warehouse): Prop :=
  (∀ (box: Cell) => warehouse.boxes.contains box = True
    → ∀ (cell: Cell) => cell ∈ cellsOf box → warehouse.walls.contains cell = False)
    ∧ (∀ (box: Cell) => warehouse.boxes.contains box = True → warehouse.boxes.contains (box.step Right) = False)
    ∧ warehouse.walls.contains warehouse.robot = False
    ∧ warehouse.boxes.contains warehouse.robot = False
    ∧ warehouse.boxes.contains (warehouse.robot.step Left) = False

--| `box` covers `cell`: it is one of the box's two cells.
def Covers (box cell: Cell): Prop := cell ∈ cellsOf box

--| `pushed` holds every box that is pushed: those covering the cell the
--| robot moves into, and those covering a cell a pushed box moves into, as
--| boxes can "directly push two other boxes at once".
def Closed (warehouse: Warehouse) (direction: Direction) (pushed: Cell → Bool): Prop :=
  (∀ (box: Cell) => warehouse.boxes.contains box = True
    → Covers box (warehouse.robot.step direction)
    → pushed box = True)
    ∧ (∀ (box: Cell) => pushed box = True
      → ∀ (other: Cell) => warehouse.boxes.contains other = True
        → ∀ (cell: Cell) => cell ∈ cellsOf (box.step direction) → Covers other cell → pushed other = True)

--| The robot's move pushes `box`: it is in every set of pushed boxes.
def MustMove (warehouse: Warehouse) (direction: Direction) (box: Cell): Prop :=
  ∀ (pushed: Cell → Bool) => Closed warehouse direction pushed → pushed box = True

--| "If this action would cause the robot or a box to move into a wall,
--| nothing moves instead": the robot would, or a box that must move would.
def Blocked (warehouse: Warehouse) (direction: Direction): Prop :=
  (warehouse.walls.contains (warehouse.robot.step direction) = True)
    ∨ (∃ (box: Cell) => MustMove warehouse direction box
      ∧ (∃ (cell: Cell) => cell ∈ cellsOf (box.step direction) ∧ warehouse.walls.contains cell = True))
