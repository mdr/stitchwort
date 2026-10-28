namespace Aoc.Year2024.Day15.Proofs
import Aoc.Year2024.Day15 (..)
import Aoc.Year2024.Day15.Spec (..)
import Std (And, Bool, DecEq, Decidable, Eq, Exists, Iff, Int, List, Map, Nat, Not, Option, Or, Set, Void)

-- A cell a box covers after a step is one it moves into, or one of its own.
theorem frontOrOwn (box: Position) (direction: Direction) (cell: Position) (covered: cell ∈ cellsOf (box.step direction)):
    Or (cell ∈ frontOf box direction) (cell ∈ cellsOf box) :=
  match DecEq.decide cell box with
    | Yes atBox => Inr (Inl (Eq.sym atBox))
    | No notBox =>
      match DecEq.decide cell (box.step Right) with
        | Yes atRight => Inr (Inr (Inl (Eq.sym atRight)))
        | No notRight =>
          let notOwn: Not (cell ∈ cellsOf box) := own =>
            match own with
              | Inl same => notBox (Eq.sym same)
              | Inr (Inl same) => notRight (Eq.sym same)
              | Inr (Inr none) => none
          Inl
            (List.memFilterIntro (cellsOf (box.step direction)) (other => other ∉ cellsOf box) cell covered
              (rewrite Decidable.toBoolOfNot (List.decMem cell (cellsOf box)) notOwn in rfl))

-- A cell some boxes move into is free for them: not a wall, and every box
-- covering it is in `group`, so moves too.
def Clear (warehouse: Warehouse) (group: Set Position) (cell: Position): Prop :=
  And (warehouse.walls.contains cell = False) ((box: Position) → warehouse.boxes.contains box = True → Covers box cell → group.contains box = True)

-- `group` is a set of boxes, and every cell one of them moves into is free.
def GroupOk (warehouse: Warehouse) (direction: Direction) (group: Set Position): Prop :=
  (box: Position) → group.contains box = True →
    And (warehouse.boxes.contains box = True) ((cell: Position) → cell ∈ frontOf box direction → Clear warehouse group cell)

-- `gather`'s invariant: every cell a box of `group` moves into is free, or
-- still to be looked at in `pending`.
def GatherInvariant (warehouse: Warehouse) (direction: Direction) (group: Set Position) (pending: List Position): Prop :=
  (box: Position) → group.contains box = True →
    And (warehouse.boxes.contains box = True)
      ((cell: Position) → cell ∈ frontOf box direction → Or (cell ∈ pending) (Clear warehouse group cell))

theorem clearMono (warehouse: Warehouse) (group: Set Position) (larger: Set Position) (cell: Position) (clear: Clear warehouse group cell)
    (grows: (box: Position) → group.contains box = True → larger.contains box = True): Clear warehouse larger cell :=
  Both (And.left clear) (box boxed covers => grows box (And.right clear box boxed covers))

-- `boxesAt` finds every box covering a cell, and nothing else.
theorem coversInBoxesAt (warehouse: Warehouse) (box: Position) (cell: Position) (boxed: warehouse.boxes.contains box = True) (covers: Covers box cell):
    box ∈ warehouse.boxesAt cell :=
  let near: box ∈ [cell, cell.step Left] :=
    match covers with
      | Inl atBox => Inl (Eq.sym atBox)
      | Inr (Inl atRight) => Inr (Inl (rewrite <- atRight in stepRightLeft box))
      | Inr (Inr none) => Void.exfalso none
  List.memFilterIntro [cell, cell.step Left] (other => warehouse.boxes.contains other) box near boxed

theorem inBoxesAtCovers (warehouse: Warehouse) (box: Position) (cell: Position) (found: box ∈ warehouse.boxesAt cell):
    And (warehouse.boxes.contains box = True) (Covers box cell) :=
  match List.memFilter [cell, cell.step Left] (other => warehouse.boxes.contains other) box found with
    | Both near boxed =>
      Both boxed
        (match near with
          | Inl atCell => Inl (Eq.sym atCell)
          | Inr (Inl atLeft) => Inr (Inl (rewrite <- atLeft in stepLeftRight cell))
          | Inr (Inr none) => Void.exfalso none)

-- What `gather` returns holds the group it started with, its boxes move
-- only into free cells, and the cells it was asked to look at are free.
theorem gatherOk (warehouse: Warehouse) (direction: Direction): (fuel: Nat) → (group: Set Position) → (pending: List Position) →
    (result: Set Position) → warehouse.gather direction group pending fuel = Some result → GatherInvariant warehouse direction group pending →
    And ((box: Position) → group.contains box = True → result.contains box = True)
      (And (GroupOk warehouse direction result) ((cell: Position) → cell ∈ pending → Clear warehouse result cell))
  | fuel, group, Nil, result, found, invariant =>
    rewrite <- Option.someInjective _ _ found in
      Both (box held => held)
        (Both
          (box held =>
            Both (And.left (invariant box held))
              (cell front =>
                match And.right (invariant box held) cell front with
                  | Inl none => Void.exfalso none
                  | Inr clear => clear))
          (cell none => Void.exfalso none))
  | Zero, group, Cons cell rest, result, found, invariant => Void.exfalso (Option.noneNotSome result found)
  | Succ fuel, group, Cons cell rest, result, gathered, invariant =>
    match wall: warehouse.walls.contains cell with
      | True => Void.exfalso (Option.noneNotSome result gathered)
      | False =>
        let found := warehouse.boxesAt cell |> .filter (box => !group.contains box)
        let larger := found.foldLeft group Set.insert
        let pending := found.flatMap (box => frontOf box direction) ++ rest
        let grows: (box: Position) → group.contains box = True → larger.contains box = True :=
          box held => Iff.backward (containsFoldInsertMap (x => x) found group box) (Inl held)
        let newOrOld: (box: Position) → larger.contains box = True → Or (group.contains box = True) (box ∈ found) :=
          box held =>
            match Iff.forward (containsFoldInsertMap (x => x) found group box) held with
              | Inl old => Inl old
              | Inr (Witness x (Both member same)) => Inr (rewrite <- same in member)
        let cellClear: Clear warehouse larger cell :=
          Both wall
            (box boxed covers =>
              match held: group.contains box with
                | True => grows box held
                | False =>
                  Iff.backward (containsFoldInsertMap (x => x) found group box)
                    (Inr
                      (Witness box
                        (Both
                          (List.memFilterIntro (warehouse.boxesAt cell) (other => !group.contains other) box
                            (coversInBoxesAt warehouse box cell boxed covers) (rewrite held in rfl))
                          rfl))))
        let invariantAfter: GatherInvariant warehouse direction larger pending :=
          box held =>
            match newOrOld box held with
              | Inl old =>
                Both (And.left (invariant box old))
                  (front inFront =>
                    match And.right (invariant box old) front inFront with
                      | Inl (Inl isCell) => Inr (rewrite <- isCell in cellClear)
                      | Inl (Inr inRest) => Inl (List.memAppendRight front (found.flatMap (box => frontOf box direction)) rest inRest)
                      | Inr clear => Inr (clearMono warehouse group larger front clear grows))
              | Inr isFound =>
                Both (And.left (inBoxesAtCovers warehouse box cell (And.left (List.memFilter (warehouse.boxesAt cell) (other => !group.contains other) box isFound))))
                  (front inFront =>
                    Inl
                      (List.memAppendLeft front (found.flatMap (box => frontOf box direction)) rest
                        (List.memFlatMapIntro (box => frontOf box direction) box front found isFound inFront)))
        let after := gatherOk warehouse direction fuel larger pending result gathered invariantAfter
        Both (box held => And.left after box (grows box held))
          (Both (And.left (And.right after))
            (front member =>
              match member with
                | Inl isCell => rewrite <- isCell in clearMono warehouse larger result cell cellClear (And.left after)
                | Inr inRest => And.right (And.right after) front (List.memAppendRight front (found.flatMap (box => frontOf box direction)) rest inRest)))

-- The group a move gathers: its boxes move only into free cells, and the
-- robot's next cell is free.
theorem gatherStart (warehouse: Warehouse) (direction: Direction) (fuel: Nat) (group: Set Position)
    (gathered: warehouse.gather direction Set.empty [warehouse.robot.step direction] fuel = Some group):
    And (GroupOk warehouse direction group) (Clear warehouse group (warehouse.robot.step direction)) :=
  let after :=
    gatherOk warehouse direction fuel Set.empty [warehouse.robot.step direction] group gathered (box held => Void.exfalso (Bool.falseNotTrue held))
  Both (And.left (And.right after)) (And.right (And.right after) (warehouse.robot.step direction) (Inl rfl))

-- With nothing overlapping, a box covering a cell of another box is that
-- box.
theorem sameBox (warehouse: Warehouse) (separate: WideSeparate warehouse) (box: Position) (other: Position) (cell: Position)
    (boxed: warehouse.boxes.contains box = True) (otherBoxed: warehouse.boxes.contains other = True) (covers: Covers other cell)
    (own: cell ∈ cellsOf box): other = box :=
  let noneRight := And.left (And.right separate)
  match own with
    | Inl atBox =>
      match covers with
        | Inl atOther => Eq.trans atOther (Eq.sym atBox)
        | Inr (Inl rightOfOther) =>
          Void.exfalso
            (Bool.trueNotFalse (Eq.trans (Eq.sym (rewrite Eq.trans rightOfOther (Eq.sym atBox) in boxed)) (noneRight other otherBoxed)))
        | Inr (Inr none) => Void.exfalso none
    | Inr (Inl rightOfBox) =>
      match covers with
        | Inl atOther =>
          Void.exfalso
            (Bool.trueNotFalse (Eq.trans (Eq.sym (rewrite Eq.trans rightOfBox (Eq.sym atOther) in otherBoxed)) (noneRight box boxed)))
        | Inr (Inl rightOfOther) => stepInjective other box Right (Eq.trans rightOfOther (Eq.sym rightOfBox))
        | Inr (Inr none) => Void.exfalso none
    | Inr (Inr none) => Void.exfalso none

-- A box covering a cell a gathered box moves into is gathered too.
theorem gatheredCovers (warehouse: Warehouse) (direction: Direction) (separate: WideSeparate warehouse) (group: Set Position)
    (ok: GroupOk warehouse direction group) (box: Position) (held: group.contains box = True) (other: Position)
    (otherBoxed: warehouse.boxes.contains other = True) (cell: Position) (moved: cell ∈ cellsOf (box.step direction)) (covers: Covers other cell):
    group.contains other = True :=
  match frontOrOwn box direction cell moved with
    | Inl front => And.right (And.right (ok box held) cell front) other otherBoxed covers
    | Inr own => rewrite sameBox warehouse separate box other cell (And.left (ok box held)) otherBoxed covers own in held

-- "If this action would cause the robot or a box to move into a wall,
-- nothing moves instead": with nothing overlapping, a blocked move moves
-- nothing.
theorem blockedMovesNothing (warehouse: Warehouse) (direction: Direction) (separate: WideSeparate warehouse) (blocked: Blocked warehouse direction):
    warehouse.moveWide direction = warehouse :=
  match gathered: warehouse.gather direction Set.empty [warehouse.robot.step direction] (2 * warehouse.boxes.size + 1) with
    | None => rfl
    | Some group =>
      let start := gatherStart warehouse direction (2 * warehouse.boxes.size + 1) group gathered
      let ok := And.left start
      let closed: Closed warehouse direction (box => group.contains box) :=
        Both (box boxed covers => And.right (And.right start) box boxed covers) (gatheredCovers warehouse direction separate group ok)
      Void.exfalso
        (match blocked with
          | Inl wallNext => Bool.trueNotFalse (Eq.trans (Eq.sym wallNext) (And.left (And.right start)))
          | Inr (Witness box (Both must (Witness cell (Both moved wallCell)))) =>
            let held := must (box => group.contains box) closed
            match frontOrOwn box direction cell moved with
              | Inl front => Bool.trueNotFalse (Eq.trans (Eq.sym wallCell) (And.left (And.right (ok box held) cell front)))
              | Inr own => Bool.trueNotFalse (Eq.trans (Eq.sym wallCell) (And.left separate box (And.left (ok box held)) cell own)))
