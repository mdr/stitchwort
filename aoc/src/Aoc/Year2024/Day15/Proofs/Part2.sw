-- Part 2's move: `gather` collects a group of boxes that move only into
-- free cells (`gatherOk`), so a blocked move moves nothing
-- (`blockedMovesNothing`), with nothing overlapping before a move nothing
-- overlaps after it (`moveWideSeparate`), which makes every box whole
-- (`wholeOfSeparate`), and no box moves onto one that stays, so the number
-- of boxes is kept (`moveWideCount`).

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
          box held => Iff.backward (Set.containsFoldInsertMap (x => x) found group box) (Inl held)
        let newOrOld: (box: Position) → larger.contains box = True → Or (group.contains box = True) (box ∈ found) :=
          box held =>
            match Iff.forward (Set.containsFoldInsertMap (x => x) found group box) held with
              | Inl old => Inl old
              | Inr (Witness x (Both member same)) => Inr (rewrite <- same in member)
        let cellClear: Clear warehouse larger cell :=
          Both wall
            (box boxed covers =>
              match held: group.contains box with
                | True => grows box held
                | False =>
                  Iff.backward (Set.containsFoldInsertMap (x => x) found group box)
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

-- The boxes after a move of `group`: each moved box, or a box that stayed.
theorem movedOrStayed (warehouse: Warehouse) (direction: Direction) (group: Set Position) (position: Position)
    (held: ((warehouse.boxes.difference group).union (group.map (box => box.step direction))).contains position = True):
    Or (∃ (box: Position) => group.contains box = True ∧ box.step direction = position)
      (And (warehouse.boxes.contains position = True) (group.contains position = False)) :=
  Bool.orElim ((warehouse.boxes.difference group).contains position) ((group.map (box => box.step direction)).contains position) _
    (Eq.trans (Eq.sym (Set.containsUnion (warehouse.boxes.difference group) position (group.map (box => box.step direction)))) held)
    (stayed => Inr (stayedElim warehouse group position stayed))
    (moved => Inl (Iff.forward (Set.containsMap group (box => box.step direction) position) moved))

-- A box that stayed was a box and wasn't gathered.
theorem stayedElim (warehouse: Warehouse) (group: Set Position) (position: Position) (stayed: (warehouse.boxes.difference group).contains position = True):
    And (warehouse.boxes.contains position = True) (group.contains position = False) :=
  let both: (warehouse.boxes.contains position ∧ ¬(group.contains position)) = True :=
    rewrite <- Set.containsDifference warehouse.boxes position group in stayed
  Both (Bool.andLeft _ _ both)
    (Bool.falseOfNotTrue (group.contains position) (gathered => Bool.falseNotTrue (rewrite gathered at Bool.andRight _ _ both)))

-- "Boxes can be aligned such that they directly push two other boxes at
-- once", but never onto a box that stays: with nothing overlapping, a move
-- keeps the number of boxes.
theorem moveWideCount (warehouse: Warehouse) (direction: Direction) (separate: WideSeparate warehouse):
    boxCount (warehouse.moveWide direction) = boxCount warehouse :=
  match gathered: warehouse.gather direction Set.empty [warehouse.robot.step direction] (2 * warehouse.boxes.size + 1) with
    | None => rfl
    | Some group =>
      let ok := And.left (gatherStart warehouse direction (2 * warehouse.boxes.size + 1) group gathered)
      let moved := group.map (box => box.step direction)
      let stayed := warehouse.boxes.difference group
      let apart: (position: Position) → stayed.contains position = True → moved.contains position = False :=
        position inStayed =>
          Bool.falseOfNotTrue (moved.contains position) (inMoved =>
            match Iff.forward (Set.containsMap group (box => box.step direction) position) inMoved with
              | Witness box (Both held stepped) =>
                match stayedElim warehouse group position inStayed with
                  | Both boxed notGathered =>
                    Bool.trueNotFalse
                      (Eq.trans
                        (Eq.sym (gatheredCovers warehouse direction separate group ok box held position boxed position (Inl stepped) (coversSelf position)))
                        notGathered))
      omega [
        Set.sizeUnionDisjoint stayed moved apart,
        Set.sizeMapInjective group (box => box.step direction) (x y inX inY same => stepInjective x y direction same),
        Set.sizeDifferenceSubset warehouse.boxes group (box held => And.left (ok box held))
      ]

-- A box covers its own cell, and the one to its right.
theorem coversSelf (box: Position): Covers box box := Inl rfl

theorem coversRight (box: Position): Covers box (box.step Right) := Inr (Inl rfl)

-- With nothing overlapping before a move, nothing overlaps after it: no box
-- on a wall or on another box, and the robot never on either.
theorem moveWideSeparate (warehouse: Warehouse) (direction: Direction) (separate: WideSeparate warehouse): WideSeparate (warehouse.moveWide direction) :=
  match gathered: warehouse.gather direction Set.empty [warehouse.robot.step direction] (2 * warehouse.boxes.size + 1) with
    | None => separate
    | Some group =>
      let next := warehouse.robot.step direction
      let start := gatherStart warehouse direction (2 * warehouse.boxes.size + 1) group gathered
      let ok := And.left start
      let clearNext := And.right start
      let offWalls := And.left separate
      let noneRight := And.left (And.right separate)
      let robotNotBoxed := And.left (And.right (And.right (And.right separate)))
      let robotNotRight := And.right (And.right (And.right (And.right separate)))
      let after := (position: Position) => (held: ((warehouse.boxes.difference group).union (group.map (box => box.step direction))).contains position = True) =>
        movedOrStayed warehouse direction group position held
      -- A box that stayed can't cover a cell a gathered box moves into.
      let stayedClear := (box: Position) => (held: group.contains box = True) => (other: Position) => (boxed: warehouse.boxes.contains other = True)
        => (stays: group.contains other = False) => (cell: Position) => (moved: cell ∈ cellsOf (box.step direction)) => (covers: Covers other cell) =>
          Bool.trueNotFalse (Eq.trans (Eq.sym (gatheredCovers warehouse direction separate group ok box held other boxed cell moved covers)) stays)
      Both
        (box held cell own =>
          match after box held with
            | Inl (Witness moved (Both inGroup stepped)) =>
              match frontOrOwn moved direction cell (rewrite stepped in own) with
                | Inl front => And.left (And.right (ok moved inGroup) cell front)
                | Inr ownBefore => offWalls moved (And.left (ok moved inGroup)) cell ownBefore
            | Inr (Both boxed stays) => offWalls box boxed cell own)
        (Both
          (box held =>
            Bool.falseOfNotTrue _ (heldRight =>
              match after box held with
                | Inl (Witness moved (Both inGroup stepped)) =>
                  match after (box.step Right) heldRight with
                    | Inl (Witness movedRight (Both inGroupRight steppedRight)) =>
                      let besides: movedRight = moved.step Right :=
                        stepInjective movedRight (moved.step Right) direction
                          (Eq.trans steppedRight (Eq.trans (rewrite stepped in rfl) (stepRightComm moved direction)))
                      Bool.trueNotFalse
                        (Eq.trans (Eq.sym (rewrite besides at And.left (ok movedRight inGroupRight))) (noneRight moved (And.left (ok moved inGroup))))
                    | Inr (Both boxedRight staysRight) =>
                      stayedClear moved inGroup (box.step Right) boxedRight staysRight (box.step Right) (Inr (Inl (rewrite stepped in rfl)))
                        (coversSelf (box.step Right))
                | Inr (Both boxed stays) =>
                  match after (box.step Right) heldRight with
                    | Inl (Witness movedRight (Both inGroupRight steppedRight)) =>
                      stayedClear movedRight inGroupRight box boxed stays (movedRight.step direction) (Inl rfl)
                        (rewrite steppedRight in coversRight box)
                    | Inr (Both boxedRight staysRight) => Bool.trueNotFalse (Eq.trans (Eq.sym boxedRight) (noneRight box boxed))))
          (Both (And.left clearNext)
            (Both
              (Bool.falseOfNotTrue _ (heldNext =>
                match after next heldNext with
                  | Inl (Witness moved (Both inGroup stepped)) =>
                    let atRobot: moved = warehouse.robot := stepInjective moved warehouse.robot direction stepped
                    Bool.trueNotFalse (Eq.trans (Eq.sym (rewrite atRobot at And.left (ok moved inGroup))) robotNotBoxed)
                  | Inr (Both boxed stays) =>
                    Bool.trueNotFalse (Eq.trans (Eq.sym (And.right clearNext next boxed (coversSelf next))) stays)))
              (Bool.falseOfNotTrue _ (heldLeft =>
                match after (next.step Left) heldLeft with
                  | Inl (Witness moved (Both inGroup stepped)) =>
                    let rightOfMoved: (moved.step Right).step direction = next :=
                      Eq.trans (Eq.sym (stepRightComm moved direction)) (rewrite stepped in stepLeftRight next)
                    let atRobot: moved.step Right = warehouse.robot := stepInjective (moved.step Right) warehouse.robot direction rightOfMoved
                    let leftOfRobot: warehouse.robot.step Left = moved := rewrite <- atRobot in stepRightLeft moved
                    Bool.trueNotFalse (Eq.trans (Eq.sym (rewrite <- leftOfRobot at And.left (ok moved inGroup))) robotNotRight)
                  | Inr (Both boxed stays) =>
                    Bool.trueNotFalse
                      (Eq.trans (Eq.sym (And.right clearNext (next.step Left) boxed (Inr (Inl (stepLeftRight next))))) stays))))))

def tileCode: WideTile → Nat
  | WideWall => 0
  | BoxLeft => 1
  | BoxRight => 2
  | WideRobot => 3
  | WideFloor => 4

-- Different tiles are different.
theorem tilesDiffer (tile: WideTile) (other: WideTile) (same: tile = other) (codes: Not (tileCode tile = tileCode other)): Void :=
  codes (Eq.cong tileCode same)

-- "Boxes are now twice as wide": with nothing overlapping, every `[` has
-- its `]`.
theorem wholeOfSeparate (warehouse: Warehouse) (separate: WideSeparate warehouse): Whole warehouse :=
  position =>
    let offWalls := And.left separate
    let noneRight := And.left (And.right separate)
    let robotNotBoxed := And.left (And.right (And.right (And.right separate)))
    let robotNotRight := And.right (And.right (And.right (And.right separate)))
    let right := position.step Right
    -- The tile right of a box is its `]`.
    let rightOfBox := (boxed: warehouse.boxes.contains position = True) =>
      match atRobot: right == warehouse.robot with
        | True =>
          let leftOfRobot: warehouse.robot.step Left = position := rewrite <- DecEq.sound right warehouse.robot atRobot in stepRightLeft position
          Void.exfalso (Bool.trueNotFalse (Eq.trans (Eq.sym (rewrite <- leftOfRobot at boxed)) robotNotRight))
        | False =>
          (rewrite atRobot, offWalls position boxed right (Inr (Inl rfl)), noneRight position boxed, stepRightLeft position, boxed in rfl: wideTile warehouse right = BoxRight)
    {
      forward = isLeft =>
        match atRobot: position == warehouse.robot with
          | True => Void.exfalso (tilesDiffer _ _ isLeft (omega))
          | False =>
            match wall: warehouse.walls.contains position with
              | True => Void.exfalso (tilesDiffer _ _ isLeft (omega))
              | False =>
                match boxed: warehouse.boxes.contains position with
                  | True => rightOfBox rfl
                  | False =>
                    match boxedLeft: warehouse.boxes.contains (position.step Left) with
                      | True => Void.exfalso (tilesDiffer _ _ isLeft (omega))
                      | False => Void.exfalso (tilesDiffer _ _ isLeft (omega)),
      backward = isRight =>
        match rightAtRobot: right == warehouse.robot with
          | True => Void.exfalso (tilesDiffer _ _ isRight (omega))
          | False =>
            match rightWall: warehouse.walls.contains right with
              | True => Void.exfalso (tilesDiffer _ _ isRight (omega))
              | False =>
                match rightBoxed: warehouse.boxes.contains right with
                  | True => Void.exfalso (tilesDiffer _ _ isRight (omega))
                  | False =>
                    match boxedLeft: warehouse.boxes.contains (right.step Left) with
                      | False => Void.exfalso (tilesDiffer _ _ isRight (omega))
                      | True =>
                        let boxed: warehouse.boxes.contains position = True := rewrite stepRightLeft position at boxedLeft
                        let notRobot: (position == warehouse.robot) = False :=
                          Bool.falseOfNotTrue (position == warehouse.robot) (atRobot =>
                            Bool.trueNotFalse (Eq.trans (Eq.sym (rewrite DecEq.sound position warehouse.robot atRobot at boxed)) robotNotBoxed))
                        rewrite notRobot, offWalls position boxed position (Inl rfl), boxed in rfl
    }

-- A move in the wide warehouse never moves a wall.
theorem moveWideWalls (warehouse: Warehouse) (direction: Direction): (warehouse.moveWide direction).walls = warehouse.walls := cases

-- After every move: the walls are where they were, nothing overlaps if
-- nothing did at the start (so the robot is never on a wall or a box), and
-- every box is whole.
theorem moveAllWideWalls: (warehouse: Warehouse) → (moves: List Direction) → (warehouse.moveAllWide moves).walls = warehouse.walls
  | warehouse, Nil => rfl
  | warehouse, Cons move rest => Eq.trans (moveAllWideWalls (warehouse.moveWide move) rest) (moveWideWalls warehouse move)

theorem moveAllWideSeparate: (warehouse: Warehouse) → (moves: List Direction) → WideSeparate warehouse → WideSeparate (warehouse.moveAllWide moves)
  | warehouse, Nil, separate => separate
  | warehouse, Cons move rest, separate => moveAllWideSeparate (warehouse.moveWide move) rest (moveWideSeparate warehouse move separate)

theorem moveAllWideWhole (warehouse: Warehouse) (moves: List Direction) (separate: WideSeparate warehouse): Whole (warehouse.moveAllWide moves) :=
  wholeOfSeparate (warehouse.moveAllWide moves) (moveAllWideSeparate warehouse moves separate)

theorem moveAllWideCount: (warehouse: Warehouse) → (moves: List Direction) → WideSeparate warehouse → boxCount (warehouse.moveAllWide moves) = boxCount warehouse
  | warehouse, Nil, separate => rfl
  | warehouse, Cons move rest, separate =>
    Eq.trans (moveAllWideCount (warehouse.moveWide move) rest (moveWideSeparate warehouse move separate)) (moveWideCount warehouse move separate)
