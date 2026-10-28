-- The program's sightlines simulate the walk (`sightlinesSimulate`): each
-- row's and column's set has exactly the obstructions on that line
-- (`Represents`), so `Set.below`/`Set.above` find the nearest one ahead
-- (`Set.belowSome` and the rest), and walking there step by step ends in the
-- state `nextTurn` jumps to. `programSimulates` puts these together for
-- the sightlines `solvePart2` builds.

namespace Aoc.Year2024.Day06.Proofs
import Aoc.Year2024.Day06 (..)
import Aoc.Year2024.Day06.Spec (..)
import Std (And, Bool, DecEq, Eq, Exists, List, Map, Nat, Not, Option, Set, Void)

-- Whether `position` is at `row` and `column`.
def isAt (row: Nat) (column: Nat) (position: Position): Bool := position.row == row && position.column == column

-- Each row's set of columns, and each column's set of rows, holds the
-- positions where `has` holds.
def Represents (sightlines: Sightlines) (has: Position → Bool): Prop :=
  (row: Nat) → (column: Nat) →
    And ((sightlines.byRow.getOr row Set.empty).contains column = has { row, column })
      ((sightlines.byColumn.getOr column Set.empty).contains row = has { row, column })

-- The line `key` of `lines` after adding `item` to the line `line`.
theorem lineAfterAdd (lines: Map Nat (Set Nat)) (line: Nat) (item: Nat) (key: Nat) (other: Nat):
    ((lines.insert line (lines.getOr line Set.empty |> .insert item)).getOr key Set.empty).contains other
      = ((key == line && other == item) || (lines.getOr key Set.empty).contains other) :=
  match onLine: key == line with
    | True =>
      rewrite DecEq.sound key line onLine, Map.getInsert line (lines.getOr line Set.empty |> .insert item) lines in
      match isItem: other == item with
        | True => rewrite DecEq.sound other item isItem, Set.containsInsert item (lines.getOr line Set.empty) in rfl
        | False =>
          rewrite Set.containsInsertOther (lines.getOr line Set.empty) item other (DecEq.soundFalse other item isItem) in rfl
    | False => rewrite Map.getInsertOther line (lines.getOr line Set.empty |> .insert item) key (DecEq.soundFalse key line onLine) lines in rfl

-- Adding an obstruction adds it to its row and column.
theorem addRepresents (sightlines: Sightlines) (has: Position → Bool) (represents: Represents sightlines has):
    (added: Position) → Represents (sightlines.add added) (position => isAt added.row added.column position || has position)
  | { row = addedRow, column = addedColumn }, row, column =>
    let before := represents row column
    Both
      (rewrite lineAfterAdd sightlines.byRow addedRow addedColumn row column, And.left before in rfl)
      (rewrite lineAfterAdd sightlines.byColumn addedColumn addedRow column row, And.right before, andComm (column == addedColumn) (row == addedRow) in rfl)

theorem andComm (a: Bool) (b: Bool): (a && b) = (b && a) := cases

theorem orShift (a: Bool) (b: Bool) (c: Bool): ((a || b) || c) = (b || (if a then True else c)) := cases

theorem orFalse (a: Bool): (a || False) = a := cases

-- The same positions, the same representation.
theorem representsCong (sightlines: Sightlines) (has: Position → Bool) (other: Position → Bool) (same: (position: Position) → has position = other position)
    (represents: Represents sightlines has): Represents sightlines other :=
  row column => rewrite <- same { row, column } in represents row column

-- Folding `add` over entries adds each of their keys.
theorem foldRepresents: (entries: List (Position, ())) → (sightlines: Sightlines) → (has: Position → Bool) → Represents sightlines has →
    Represents (Map.Spec.foldLeft (acc key unit => Sightlines.add acc key) sightlines entries)
      (position => has position || entries.any (entry => isAt entry.fst.row entry.fst.column position))
  | Nil, sightlines, has, represents, row, column => representsCong sightlines has _ (position => Eq.sym (orFalse (has position))) represents row column
  | Cons (key, unit) rest, sightlines, has, represents, row, column =>
    let hasRest := (position: Position) => rest.any (entry => isAt entry.fst.row entry.fst.column position)
    representsCong (Map.Spec.foldLeft (acc key unit => Sightlines.add acc key) (sightlines.add key) rest)
      (position => (isAt key.row key.column position || has position) || hasRest position)
      (position => has position || (Cons (key, unit) rest).any (entry => isAt entry.fst.row entry.fst.column position))
      (position => orShift (isAt key.row key.column position) (has position) (hasRest position))
      (foldRepresents rest (sightlines.add key) (position => isAt key.row key.column position || has position) (addRepresents sightlines has represents key))
      row column

-- Positions with the same row and column are the same.
theorem positionExt: (one: Position) → (other: Position) → one.row = other.row → one.column = other.column → one = other
  | { row, column }, { row = otherRow, column = otherColumn }, rows, columns => rewrite rows, columns in rfl

theorem isAtSelf (position: Position): isAt position.row position.column position = True :=
  rewrite DecEq.refl position.row, DecEq.refl position.column in rfl

theorem isAtSound (key: Position) (position: Position) (here: isAt key.row key.column position = True): position = key :=
  positionExt position key (DecEq.sound _ _ (Bool.andLeft _ _ here)) (DecEq.sound _ _ (Bool.andRight _ _ here))

-- A set has a position when one of its entries is at it.
theorem containsEntries (obstructions: Set Position) (position: Position):
    (False || (Map.toList obstructions.items).any (entry => isAt entry.fst.row entry.fst.column position)) = obstructions.contains position :=
  match has: obstructions.contains position with
    | True =>
      List.anyOfMem (Map.toList obstructions.items) (entry => isAt entry.fst.row entry.fst.column position) (position, ()) (isAtSelf position)
        ((Set.containsToList obstructions position).forward has)
    | False =>
      match found: (Map.toList obstructions.items).any (entry => isAt entry.fst.row entry.fst.column position) with
        | False => rfl
        | True =>
          List.anyTrueElim (Map.toList obstructions.items) (entry => isAt entry.fst.row entry.fst.column position) (True = False) found
            (entry inList hit =>
              match entry with
                | (key, unit) =>
                  let entryIs: (key, unit) = (position, ()) := rewrite isAtSound key position hit, Set.unitEq unit () in rfl
                  Eq.sym (Eq.trans (Eq.sym has) ((Set.containsToList obstructions position).backward (rewrite <- entryIs in inList))))

-- No obstructions, no sightlines.
theorem emptyRepresents: Represents ({ byRow = Map.empty, byColumn = Map.empty }: Sightlines) (position => False) := row column => Both rfl rfl

-- The program's sightlines represent its obstructions.
theorem ofRepresents (obstructions: Set Position): Represents (Sightlines.of obstructions) (position => obstructions.contains position) :=
  let folded: Sightlines.of obstructions
      = Map.Spec.foldLeft (acc key unit => Sightlines.add acc key) ({ byRow = Map.empty, byColumn = Map.empty }: Sightlines) (Map.toList obstructions.items) :=
    Map.foldLeftToList (acc key unit => Sightlines.add acc key) ({ byRow = Map.empty, byColumn = Map.empty }: Sightlines) obstructions.items
  rewrite folded in
  representsCong _ _ _ (containsEntries obstructions)
    (foldRepresents (Map.toList obstructions.items) ({ byRow = Map.empty, byColumn = Map.empty }: Sightlines) (position => False) emptyRepresents)

-- One step: turning at an obstruction ahead, and leaving past the edge.
theorem stepTurns (lab: Lab) (guard: Guard) (ahead: Position) (inFront: lab.ahead guard = Some ahead) (blocked: lab.obstructions.contains ahead = True):
    lab.step guard = Some ({ guard | facing = guard.facing.turnRight }) :=
  rewrite inFront, blocked in rfl

theorem stepLeaves (lab: Lab) (guard: Guard) (inFront: lab.ahead guard = None): lab.step guard = None :=
  rewrite inFront in rfl

-- What is ahead in each direction, inside the map and at its edge.
theorem aheadUp (lab: Lab) (row: Nat) (column: Nat) (positive: 0 < row):
    lab.ahead ({ position = { row, column }, facing = Up }: Guard) = Some ({ row = row - 1, column }: Position) := cases

theorem aheadDown (lab: Lab) (row: Nat) (column: Nat) (fits: row + 1 < lab.height):
    lab.ahead ({ position = { row, column }, facing = Down }: Guard) = Some ({ row = row + 1, column }: Position) := cases

theorem aheadDownEdge (lab: Lab) (row: Nat) (column: Nat) (edge: lab.height = row + 1):
    lab.ahead ({ position = { row, column }, facing = Down }: Guard) = None := cases

theorem aheadRight (lab: Lab) (row: Nat) (column: Nat) (fits: column + 1 < lab.width):
    lab.ahead ({ position = { row, column }, facing = Right }: Guard) = Some ({ row, column = column + 1 }: Position) := cases

theorem aheadRightEdge (lab: Lab) (row: Nat) (column: Nat) (edge: lab.width = column + 1):
    lab.ahead ({ position = { row, column }, facing = Right }: Guard) = None := cases

theorem aheadLeft (lab: Lab) (row: Nat) (column: Nat) (positive: 0 < column):
    lab.ahead ({ position = { row, column }, facing = Left }: Guard) = Some ({ row, column = column - 1 }: Position) := cases

-- A first step to `next`, then the rest of the walk from there.
theorem walkFirst (lab: Lab) (guard: Guard) (next: Guard) (stepped: lab.step guard = Some next) (steps: Nat):
    walk lab (Some guard) (Succ steps) = walk lab (Some next) steps :=
  Eq.cong (state => walk lab state steps) stepped

-- Facing up, with an obstruction above in the column and none between: she
-- walks to just below it and turns right.
theorem walkUpTurn (lab: Lab) (column: Nat) (obstruction: Nat) (blocked: lab.obstructions.contains { row = obstruction, column } = True):
    (moves: Nat) → (row: Nat) → obstruction + Succ moves = row →
      ((other: Nat) → obstruction < other → other < row → lab.obstructions.contains { row = other, column } = False) →
      walk lab (Some ({ position = { row, column }, facing = Up })) (Succ moves) = Some ({ position = { row = obstruction + 1, column }, facing = Right })
  | Zero, row, distance, free =>
    rewrite (omega [distance]: obstruction + 1 = row) in
    stepTurns lab { position = { row, column }, facing = Up } { row = row - 1, column } (aheadUp lab row column (omega [distance]))
      (rewrite (omega [distance]: row - 1 = obstruction) in blocked)
  | Succ moves, row, distance, free =>
    Eq.trans
      (walkFirst lab { position = { row, column }, facing = Up } { position = { row = row - 1, column }, facing = Up }
        (stepMoves lab { position = { row, column }, facing = Up } { row = row - 1, column } (aheadUp lab row column (omega [distance]))
          (free (row - 1) (omega [distance]) (omega [distance])))
        (Succ moves))
      (walkUpTurn lab column obstruction blocked moves (row - 1) (omega [distance]) (other above below => free other above (omega [below])))

-- Facing up with nothing above in the column: she walks off the top.
theorem walkUpLeave (lab: Lab) (column: Nat): (row: Nat) → ((other: Nat) → other < row → lab.obstructions.contains { row = other, column } = False) →
    walk lab (Some ({ position = { row, column }, facing = Up })) (Succ row) = None
  | Zero, free => rfl
  | Succ row, free =>
    Eq.trans
      (walkFirst lab { position = { row = Succ row, column }, facing = Up } { position = { row, column }, facing = Up }
        (stepMoves lab { position = { row = Succ row, column }, facing = Up } { row, column } (aheadUp lab (Succ row) column omega) (free row omega))
        (Succ row))
      (walkUpLeave lab column row (other below => free other (omega [below])))

-- Facing down, with an obstruction below in the column and none between:
-- she walks to just above it and turns right.
theorem walkDownTurn (lab: Lab) (column: Nat) (obstruction: Nat) (fits: obstruction < lab.height)
    (blocked: lab.obstructions.contains { row = obstruction, column } = True):
    (moves: Nat) → (row: Nat) → row + Succ moves = obstruction →
      ((other: Nat) → row < other → other < obstruction → lab.obstructions.contains { row = other, column } = False) →
      walk lab (Some ({ position = { row, column }, facing = Down })) (Succ moves) = Some ({ position = { row = obstruction - 1, column }, facing = Left })
  | Zero, row, distance, free =>
    rewrite (omega [distance]: obstruction - 1 = row) in
    stepTurns lab { position = { row, column }, facing = Down } { row = row + 1, column } (aheadDown lab row column (omega [distance, fits]))
      (rewrite (omega [distance]: row + 1 = obstruction) in blocked)
  | Succ moves, row, distance, free =>
    Eq.trans
      (walkFirst lab { position = { row, column }, facing = Down } { position = { row = row + 1, column }, facing = Down }
        (stepMoves lab { position = { row, column }, facing = Down } { row = row + 1, column } (aheadDown lab row column (omega [distance, fits]))
          (free (row + 1) (omega [distance]) (omega [distance])))
        (Succ moves))
      (walkDownTurn lab column obstruction fits blocked moves (row + 1) (omega [distance]) (other above below => free other (omega [above]) below))

-- Facing down with nothing below in the column: she walks off the bottom.
theorem walkDownLeave (lab: Lab) (column: Nat):
    (moves: Nat) → (row: Nat) → row + Succ moves = lab.height →
      ((other: Nat) → row < other → other < lab.height → lab.obstructions.contains { row = other, column } = False) →
      walk lab (Some ({ position = { row, column }, facing = Down })) (Succ moves) = None
  | Zero, row, distance, free => stepLeaves lab { position = { row, column }, facing = Down } (aheadDownEdge lab row column (omega [distance]))
  | Succ moves, row, distance, free =>
    Eq.trans
      (walkFirst lab { position = { row, column }, facing = Down } { position = { row = row + 1, column }, facing = Down }
        (stepMoves lab { position = { row, column }, facing = Down } { row = row + 1, column } (aheadDown lab row column (omega [distance]))
          (free (row + 1) (omega [distance]) (omega [distance])))
        (Succ moves))
      (walkDownLeave lab column moves (row + 1) (omega [distance]) (other above below => free other (omega [above]) below))

-- Facing right, with an obstruction to the right in the row and none
-- between: she walks to just before it and turns right.
theorem walkRightTurn (lab: Lab) (row: Nat) (obstruction: Nat) (fits: obstruction < lab.width)
    (blocked: lab.obstructions.contains { row, column = obstruction } = True):
    (moves: Nat) → (column: Nat) → column + Succ moves = obstruction →
      ((other: Nat) → column < other → other < obstruction → lab.obstructions.contains { row, column = other } = False) →
      walk lab (Some ({ position = { row, column }, facing = Right })) (Succ moves) = Some ({ position = { row, column = obstruction - 1 }, facing = Down })
  | Zero, column, distance, free =>
    rewrite (omega [distance]: obstruction - 1 = column) in
    stepTurns lab { position = { row, column }, facing = Right } { row, column = column + 1 } (aheadRight lab row column (omega [distance, fits]))
      (rewrite (omega [distance]: column + 1 = obstruction) in blocked)
  | Succ moves, column, distance, free =>
    Eq.trans
      (walkFirst lab { position = { row, column }, facing = Right } { position = { row, column = column + 1 }, facing = Right }
        (stepMoves lab { position = { row, column }, facing = Right } { row, column = column + 1 } (aheadRight lab row column (omega [distance, fits]))
          (free (column + 1) (omega [distance]) (omega [distance])))
        (Succ moves))
      (walkRightTurn lab row obstruction fits blocked moves (column + 1) (omega [distance]) (other after before => free other (omega [after]) before))

-- Facing right with nothing to the right in the row: she walks off the
-- right edge.
theorem walkRightLeave (lab: Lab) (row: Nat):
    (moves: Nat) → (column: Nat) → column + Succ moves = lab.width →
      ((other: Nat) → column < other → other < lab.width → lab.obstructions.contains { row, column = other } = False) →
      walk lab (Some ({ position = { row, column }, facing = Right })) (Succ moves) = None
  | Zero, column, distance, free => stepLeaves lab { position = { row, column }, facing = Right } (aheadRightEdge lab row column (omega [distance]))
  | Succ moves, column, distance, free =>
    Eq.trans
      (walkFirst lab { position = { row, column }, facing = Right } { position = { row, column = column + 1 }, facing = Right }
        (stepMoves lab { position = { row, column }, facing = Right } { row, column = column + 1 } (aheadRight lab row column (omega [distance]))
          (free (column + 1) (omega [distance]) (omega [distance])))
        (Succ moves))
      (walkRightLeave lab row moves (column + 1) (omega [distance]) (other after before => free other (omega [after]) before))

-- Facing left, with an obstruction to the left in the row and none between:
-- she walks to just after it and turns right.
theorem walkLeftTurn (lab: Lab) (row: Nat) (obstruction: Nat) (blocked: lab.obstructions.contains { row, column = obstruction } = True):
    (moves: Nat) → (column: Nat) → obstruction + Succ moves = column →
      ((other: Nat) → obstruction < other → other < column → lab.obstructions.contains { row, column = other } = False) →
      walk lab (Some ({ position = { row, column }, facing = Left })) (Succ moves) = Some ({ position = { row, column = obstruction + 1 }, facing = Up })
  | Zero, column, distance, free =>
    rewrite (omega [distance]: obstruction + 1 = column) in
    stepTurns lab { position = { row, column }, facing = Left } { row, column = column - 1 } (aheadLeft lab row column (omega [distance]))
      (rewrite (omega [distance]: column - 1 = obstruction) in blocked)
  | Succ moves, column, distance, free =>
    Eq.trans
      (walkFirst lab { position = { row, column }, facing = Left } { position = { row, column = column - 1 }, facing = Left }
        (stepMoves lab { position = { row, column }, facing = Left } { row, column = column - 1 } (aheadLeft lab row column (omega [distance]))
          (free (column - 1) (omega [distance]) (omega [distance])))
        (Succ moves))
      (walkLeftTurn lab row obstruction blocked moves (column - 1) (omega [distance]) (other after before => free other after (omega [before])))

-- Facing left with nothing to the left in the row: she walks off the left
-- edge.
theorem walkLeftLeave (lab: Lab) (row: Nat): (column: Nat) → ((other: Nat) → other < column → lab.obstructions.contains { row, column = other } = False) →
    walk lab (Some ({ position = { row, column }, facing = Left })) (Succ column) = None
  | Zero, free => rfl
  | Succ column, free =>
    Eq.trans
      (walkFirst lab { position = { row, column = Succ column }, facing = Left } { position = { row, column }, facing = Left }
        (stepMoves lab { position = { row, column = Succ column }, facing = Left } { row, column } (aheadLeft lab row (Succ column) omega) (free column omega))
        (Succ column))
      (walkLeftLeave lab row column (other before => free other (omega [before])))

-- From a guard on the map, `nextTurn` jumps to where the walk turns, and
-- finds nothing exactly when she walks off: the four directions in turn.
theorem simulateAt (lab: Lab) (sightlines: Sightlines) (represents: Represents sightlines (position => lab.obstructions.contains position))
    (mapped: (position: Position) → lab.obstructions.contains position = True → onMap lab position = True):
    (guard: Guard) → onMap lab guard.position = True →
      And
        ((next: Guard) → sightlines.nextTurn guard = Some next → Exists Nat (steps => And (0 < steps) (walk lab (Some guard) steps = Some next)))
        (sightlines.nextTurn guard = None → Exists Nat (steps => walk lab (Some guard) steps = None))
  | { position = { row, column }, facing = Up }, inside =>
    match found: (sightlines.byColumn.getOr column Set.empty).below row with
      | Some obstruction =>
        let nearest := Set.belowSome (sightlines.byColumn.getOr column Set.empty) row obstruction found
        let blocked: lab.obstructions.contains { row = obstruction, column } = True :=
          Eq.trans (Eq.sym (And.right (represents obstruction column))) (And.left nearest)
        let free := (other: Nat) (above: obstruction < other) (below: other < row) =>
          Eq.trans (Eq.sym (And.right (represents other column))) (And.right (And.right nearest) other above below)
        let walked := walkUpTurn lab column obstruction blocked (row - obstruction - 1) row (omega [And.left (And.right nearest)]) free
        Both
          (next turned => Witness (Succ (row - obstruction - 1)) (Both omega (Eq.trans walked turned)))
          (none => Void.exfalso (Option.someNotNone _ none))
      | None =>
        let free := (other: Nat) (below: other < row) =>
          Eq.trans (Eq.sym (And.right (represents other column))) (Set.belowNone (sightlines.byColumn.getOr column Set.empty) row found other below)
        Both
          (next turned => Void.exfalso (Option.noneNotSome next turned))
          (none => Witness (Succ row) (walkUpLeave lab column row free))
  | { position = { row, column }, facing = Right }, inside =>
    match found: (sightlines.byRow.getOr row Set.empty).above column with
      | Some obstruction =>
        let nearest := Set.aboveSome (sightlines.byRow.getOr row Set.empty) column obstruction found
        let blocked: lab.obstructions.contains { row, column = obstruction } = True :=
          Eq.trans (Eq.sym (And.left (represents row obstruction))) (And.left nearest)
        let fits: obstruction < lab.width := omega [mapped { row, column = obstruction } blocked]
        let free := (other: Nat) (after: column < other) (before: other < obstruction) =>
          Eq.trans (Eq.sym (And.left (represents row other))) (And.right (And.right nearest) other after before)
        let walked := walkRightTurn lab row obstruction fits blocked (obstruction - column - 1) column (omega [And.left (And.right nearest)]) free
        Both
          (next turned => Witness (Succ (obstruction - column - 1)) (Both omega (Eq.trans walked turned)))
          (none => Void.exfalso (Option.someNotNone _ none))
      | None =>
        let free := (other: Nat) (after: column < other) (before: other < lab.width) =>
          Eq.trans (Eq.sym (And.left (represents row other))) (Set.aboveNone (sightlines.byRow.getOr row Set.empty) column found other after)
        Both
          (next turned => Void.exfalso (Option.noneNotSome next turned))
          (none => Witness (Succ (lab.width - column - 1)) (walkRightLeave lab row (lab.width - column - 1) column (omega [inside]) free))
  | { position = { row, column }, facing = Down }, inside =>
    match found: (sightlines.byColumn.getOr column Set.empty).above row with
      | Some obstruction =>
        let nearest := Set.aboveSome (sightlines.byColumn.getOr column Set.empty) row obstruction found
        let blocked: lab.obstructions.contains { row = obstruction, column } = True :=
          Eq.trans (Eq.sym (And.right (represents obstruction column))) (And.left nearest)
        let fits: obstruction < lab.height := omega [mapped { row = obstruction, column } blocked]
        let free := (other: Nat) (after: row < other) (before: other < obstruction) =>
          Eq.trans (Eq.sym (And.right (represents other column))) (And.right (And.right nearest) other after before)
        let walked := walkDownTurn lab column obstruction fits blocked (obstruction - row - 1) row (omega [And.left (And.right nearest)]) free
        Both
          (next turned => Witness (Succ (obstruction - row - 1)) (Both omega (Eq.trans walked turned)))
          (none => Void.exfalso (Option.someNotNone _ none))
      | None =>
        let free := (other: Nat) (after: row < other) (before: other < lab.height) =>
          Eq.trans (Eq.sym (And.right (represents other column))) (Set.aboveNone (sightlines.byColumn.getOr column Set.empty) row found other after)
        Both
          (next turned => Void.exfalso (Option.noneNotSome next turned))
          (none => Witness (Succ (lab.height - row - 1)) (walkDownLeave lab column (lab.height - row - 1) row (omega [inside]) free))
  | { position = { row, column }, facing = Left }, inside =>
    match found: (sightlines.byRow.getOr row Set.empty).below column with
      | Some obstruction =>
        let nearest := Set.belowSome (sightlines.byRow.getOr row Set.empty) column obstruction found
        let blocked: lab.obstructions.contains { row, column = obstruction } = True :=
          Eq.trans (Eq.sym (And.left (represents row obstruction))) (And.left nearest)
        let free := (other: Nat) (after: obstruction < other) (before: other < column) =>
          Eq.trans (Eq.sym (And.left (represents row other))) (And.right (And.right nearest) other after before)
        let walked := walkLeftTurn lab row obstruction blocked (column - obstruction - 1) column (omega [And.left (And.right nearest)]) free
        Both
          (next turned => Witness (Succ (column - obstruction - 1)) (Both omega (Eq.trans walked turned)))
          (none => Void.exfalso (Option.someNotNone _ none))
      | None =>
        let free := (other: Nat) (before: other < column) =>
          Eq.trans (Eq.sym (And.left (represents row other))) (Set.belowNone (sightlines.byRow.getOr row Set.empty) column found other before)
        Both
          (next turned => Void.exfalso (Option.noneNotSome next turned))
          (none => Witness (Succ column) (walkLeftLeave lab row column free))

-- Sightlines that represent a lab's obstructions, all on the map, simulate
-- its walk.
theorem sightlinesSimulate (lab: Lab) (sightlines: Sightlines) (represents: Represents sightlines (position => lab.obstructions.contains position))
    (mapped: (position: Position) → lab.obstructions.contains position = True → onMap lab position = True): Simulates sightlines lab :=
  guard inside => simulateAt lab sightlines represents mapped guard inside

-- What a set has after an insert, as `addRepresents` says it.
theorem insertContains (obstructions: Set Position) (added: Position) (position: Position):
    (isAt added.row added.column position || obstructions.contains position) = (obstructions.insert added).contains position :=
  match here: isAt added.row added.column position with
    | True => rewrite isAtSound added position here in Eq.sym (Set.containsInsert added obstructions)
    | False =>
      let other: Not (position = added) := same => Bool.falseNotTrue (Eq.trans (Eq.sym here) (rewrite same in isAtSelf added))
      rewrite Set.containsInsertOther obstructions added position other in rfl

-- The program's sightlines with each new obstruction on the map simulate
-- the walk in the lab with it, when the lab's obstructions are on the map.
theorem programSimulates (lab: Lab) (mapped: (position: Position) → lab.obstructions.contains position = True → onMap lab position = True)
    (blocker: Position) (blockerInside: onMap lab blocker = True):
    Simulates ((Sightlines.of lab.obstructions).add blocker) (lab.withObstruction blocker) :=
  sightlinesSimulate (lab.withObstruction blocker) ((Sightlines.of lab.obstructions).add blocker)
    (representsCong ((Sightlines.of lab.obstructions).add blocker)
      (position => isAt blocker.row blocker.column position || lab.obstructions.contains position)
      (position => (lab.withObstruction blocker).obstructions.contains position)
      (insertContains lab.obstructions blocker)
      (addRepresents (Sightlines.of lab.obstructions) (position => lab.obstructions.contains position) (ofRepresents lab.obstructions) blocker))
    (position has =>
      Bool.orElim (isAt blocker.row blocker.column position) (lab.obstructions.contains position) (onMap lab position = True)
        (Eq.trans (insertContains lab.obstructions blocker position) has)
        (here => rewrite isAtSound blocker position here in blockerInside)
        (mapped position))
