--| Facts about positions and directions: turning, what a step reaches, and
--| the four and eight neighbours (`neighbours` lists exactly the `adjacent`
--| positions, `around` exactly the `touching` ones, each without repeats,
--| at most four and eight of them).

namespace Aoc.Common.Proofs
import Aoc.Common (..)
import Std (Bool, DecEq, Decidable, Eq, Exists, Iff, List, Nat, Option, Void)

-- Turning

theorem turnRightFour (direction: Direction): direction.turnRight.turnRight.turnRight.turnRight = direction := cases

theorem turnLeftRight (direction: Direction): direction.turnRight.turnLeft = direction := cases

theorem turnRightLeft (direction: Direction): direction.turnLeft.turnRight = direction := cases

theorem oppositeTwoTurns (direction: Direction): direction.turnRight.turnRight = direction.opposite := cases

theorem oppositeOpposite (direction: Direction): direction.opposite.opposite = direction := cases

theorem memDirections (direction: Direction): direction ∈ directions := match direction with
  | Up => Inl rfl
  | Right => Inr (Inl rfl)
  | Down => Inr (Inr (Inl rfl))
  | Left => Inr (Inr (Inr (Inl rfl)))

-- Adjacency

theorem equalOf (a: Nat) (b: Nat) (same: a = b): (a == b) = True := rewrite same in DecEq.refl b

theorem upAdjacent (row: Nat) (column: Nat): adjacent { row = Succ row, column } { row, column } = True :=
  Inr (Both (DecEq.refl column) (Inr (equalOf (row + 1) (Succ row) (omega))))

theorem leftAdjacent (row: Nat) (column: Nat): adjacent { row, column = Succ column } { row, column } = True :=
  Inl (Both (DecEq.refl row) (Inr (equalOf (column + 1) (Succ column) (omega))))

theorem rightAdjacent (row: Nat) (column: Nat): adjacent { row, column } { row, column = column + 1 } = True :=
  Inl (Both (DecEq.refl row) (Inl (DecEq.refl (column + 1))))

theorem downAdjacent (row: Nat) (column: Nat): adjacent { row, column } { row = row + 1, column } = True :=
  Inr (Both (DecEq.refl column) (Inl (DecEq.refl (row + 1))))

--| A step reaches an adjacent position...
theorem stepAdjacent (position: Position) (direction: Direction) (next: Position) (stepped: position.step direction = Some next):
    adjacent position next = True := match position, direction with
      | { row = Succ row, column }, Up => rewrite <- Option.someInjective stepped in upAdjacent row column
      | { row, column }, Right => rewrite <- Option.someInjective stepped in rightAdjacent row column
      | { row, column }, Down => rewrite <- Option.someInjective stepped in downAdjacent row column
      | { row, column = Succ column }, Left => rewrite <- Option.someInjective stepped in leftAdjacent row column

--| A step back the opposite way returns to where it started.
theorem stepOpposite (position: Position) (direction: Direction) (next: Position) (stepped: position.step direction = Some next):
    next.step direction.opposite = Some position := match position, direction with
      | { row = Succ row, column }, Up => rewrite <- Option.someInjective stepped in rfl
      | { row, column }, Right => rewrite <- Option.someInjective stepped in rfl
      | { row, column }, Down => rewrite <- Option.someInjective stepped in rfl
      | { row, column = Succ column }, Left => rewrite <- Option.someInjective stepped in rfl

--| ...and each adjacent position is a step away.
theorem adjacentStep (position next: Position) (near: adjacent position next = True):
    ∃ (direction: Direction) => position.step direction = Some next := match position, next with
      | { row, column }, { row = r, column = c } =>
        match near with
          | Inl (Both rows (Inl right)) => rewrite <- rows.read, <- right.read in Witness Right rfl
          | Inl (Both rows (Inr left)) => rewrite <- rows.read, <- left.read in Witness Left rfl
          | Inr (Both columns (Inl down)) => rewrite <- columns.read, <- down.read in Witness Down rfl
          | Inr (Both columns (Inr up)) => rewrite <- columns.read, <- up.read in Witness Up rfl

--| The neighbours are the positions a step away...
theorem memNeighbours (position: Position) (next: Position): (next ∈ position.neighbours) ↔ (∃ (direction: Direction) => position.step direction = Some next) := {
  forward = member =>
    Exists.elim (List.anyMember (direction => position.step direction = Some next) directions (List.memFilterMapElim position.step next directions member))
      (direction both => Witness direction (And.right both)),
  backward = stepped => Exists.elim stepped (direction found => List.memFilterMapIntro position.step direction next directions (memDirections direction) found)
}

--| ...so each is adjacent...
theorem neighbourAdjacent (position: Position) (next: Position) (member: next ∈ position.neighbours): adjacent position next = True :=
  Exists.elim ((memNeighbours position next).forward member) (direction found => stepAdjacent position direction next found)

--| ...and each adjacent position is a neighbour.
theorem adjacentNeighbour (position: Position) (next: Position) (near: adjacent position next = True): next ∈ position.neighbours :=
  (memNeighbours position next).backward (adjacentStep position next near)

--| Which way `next` lies from `position`, for a position a step away.
def directionTo (position: Position) (next: Position): Direction :=
  if next.row < position.row then Up else if position.row < next.row then Down else if position.column < next.column then Right else Left

--| Each step goes the way it says.
theorem directionOfStep (position: Position) (direction: Direction) (next: Position) (stepped: position.step direction = Some next):
    directionTo position next = direction := match position, direction with
      | { row = Succ row, column }, Up => rewrite <- Option.someInjective stepped in cases
      | { row, column }, Right => rewrite <- Option.someInjective stepped in cases
      | { row, column }, Down => rewrite <- Option.someInjective stepped in cases
      | { row, column = Succ column }, Left => rewrite <- Option.someInjective stepped in cases

--| No position is a neighbour twice...
theorem neighboursDistinct (position: Position): List.Distinct position.neighbours :=
  List.distinctOfMap (directionTo position) position.neighbours
    (List.distinctMapFilterMap position.step (direction => direction) (directionTo position)
      (direction next stepped => directionOfStep position direction next stepped) directions directionsDistinct)

--| The four directions are different.
theorem directionsDistinct: List.Distinct (directions.map (direction => direction)) :=
  Both (notMemDirections Up [Right, Down, Left] rfl)
    (Both (notMemDirections Right [Down, Left] rfl) (Both (notMemDirections Down [Left] rfl) (Both (notMemDirections Left [] rfl) ())))

def directionIndex: Direction → Nat
  | Up => 0
  | Right => 1
  | Down => 2
  | Left => 3

--| A direction whose index none of `others` has isn't one of them.
theorem notMemDirections (direction: Direction) (others: List Direction)
    (differ: others.all (other => directionIndex other != directionIndex direction) = True): direction ∉ others :=
  match others with
    | [] => member => member
    | [other, ..rest] => match
      | Inl same => DecEq.neTrue differ.left (rewrite same in rfl)
      | Inr later => notMemDirections direction rest differ.right later

--| ...and there are at most four.
theorem neighboursAtMost4 (position: Position): position.neighbours.length ≤ 4 := List.lengthFilterMapLe position.step directions

-- The eight around

theorem touchingOfBounds (r: Nat) (c: Nat) (a: Nat) (b: Nat) (h1: r - 1 ≤ a) (h2: a ≤ r + 1) (h3: c - 1 ≤ b) (h4: b ≤ c + 1)
    (other: not (a == r && b == c) = True): touching { row = r, column = c } { row = a, column = b } = True :=
  cases

theorem rowAboveOfTouching (r: Nat) (c: Nat) (a: Nat) (b: Nat) (near: touching { row = r, column = c } { row = a, column = b } = True): r - 1 ≤ a := cases
theorem rowBelowOfTouching (r: Nat) (c: Nat) (a: Nat) (b: Nat) (near: touching { row = r, column = c } { row = a, column = b } = True): a ≤ r + 1 := cases
theorem columnLeftOfTouching (r: Nat) (c: Nat) (a: Nat) (b: Nat) (near: touching { row = r, column = c } { row = a, column = b } = True): c - 1 ≤ b := cases
theorem columnRightOfTouching (r: Nat) (c: Nat) (a: Nat) (b: Nat) (near: touching { row = r, column = c } { row = a, column = b } = True): b ≤ c + 1 := cases
theorem otherOfTouching (r: Nat) (c: Nat) (a: Nat) (b: Nat) (near: touching { row = r, column = c } { row = a, column = b } = True):
    not (a == r && b == c) = True :=
  cases

--| The rows and columns `around` takes the positions from.
def aroundBlock (r: Nat) (c: Nat): List Position :=
  List.range (r - 1) (r + 1 + 1) |> .flatMap (row => List.range (c - 1) (c + 1 + 1) |> .map (column => ({ row, column }: Position)))

--| The positions around are touching...
theorem aroundTouching (at other: Position) (member: other ∈ at.around): touching at other = True :=
  match at, other with
    | { row = r, column = c }, { row = a, column = b } =>
      let (Both inBlock other) := List.memFilter (aroundBlock r c) (near => not (near.row == r && near.column == c)) member
      List.anyElim (row => ({ row = a, column = b }: Position) ∈ List.map (List.range (c - 1) (c + 1 + 1)) (column => ({ row, column }: Position)))
        (touching { row = r, column = c } { row = a, column = b } = True) (List.range (r - 1) (r + 1 + 1))
        (List.memFlatMapElim (row => List.map (List.range (c - 1) (c + 1 + 1)) (column => ({ row, column }: Position))) { row = a, column = b }
          (List.range (r - 1) (r + 1 + 1)) inBlock)
        (row inRows inRow =>
          Exists.elim (List.memMapElim (column => ({ row, column }: Position)) { row = a, column = b } (List.range (c - 1) (c + 1 + 1)) inRow)
            (column both =>
              let (Both inColumns same) := both
              let sameRow: row = a := Eq.cong Position.row same
              let sameColumn: column = b := Eq.cong Position.column same
              let (Both rowAbove rowBelow) := ((List.memRange _ _ _).forward inRows)
              let (Both columnLeft columnRight) := ((List.memRange _ _ _).forward inColumns)
              touchingOfBounds r c a b (omega) (omega) (omega) (omega) other))

--| ...and every touching position is around.
theorem touchingAround (at other: Position) (near: touching at other = True): other ∈ at.around :=
  match at, other with
    | { row = r, column = c }, { row = a, column = b } =>
      List.memFilterIntro (aroundBlock r c) (near => not (near.row == r && near.column == c))
        (List.memFlatMapIntro (row => List.map (List.range (c - 1) (c + 1 + 1)) (column => ({ row, column }: Position))) a { row = a, column = b }
          (List.range (r - 1) (r + 1 + 1)) (((List.memRange a (r - 1) (r + 1 + 1)).backward (Both (rowAboveOfTouching r c a b near) (Nat.leLessSucc a (r + 1) (rowBelowOfTouching r c a b near)))))
          (List.memMap (List.range (c - 1) (c + 1 + 1)) b
            (((List.memRange b (c - 1) (c + 1 + 1)).backward (Both (columnLeftOfTouching r c a b near) (Nat.leLessSucc b (c + 1) (columnRightOfTouching r c a b near)))))
            (column => ({ row = a, column }: Position))))
        (otherOfTouching r c a b near)

--| No position is around twice...
theorem aroundDistinct (at: Position): List.Distinct at.around :=
  List.distinctFilter (aroundBlock at.row at.column) (near => not (near.row == at.row && near.column == at.column))
    (List.distinctFlatMap (row => List.map (List.range (at.column - 1) (at.column + 1 + 1)) (column => ({ row, column }: Position))) Position.row
      (List.range (at.row - 1) (at.row + 1 + 1)) (List.distinctRange (at.row - 1) (at.row + 1 + 1))
      (row inRows =>
        List.distinctMap (List.range (at.column - 1) (at.column + 1 + 1)) (List.distinctRange (at.column - 1) (at.column + 1 + 1))
          (column => ({ row, column }: Position)) (x y same => Eq.cong Position.column same))
      (row inRows position inRow =>
        Exists.elim (List.memMapElim (column => ({ row, column }: Position)) position (List.range (at.column - 1) (at.column + 1 + 1)) inRow)
          (column both => rewrite <- And.right both in rfl)))

--| ...and there are at most eight: the block is at most three by three,
--| and holds `at` itself, which isn't around.
theorem aroundAtMost8 (at: Position): at.around.length ≤ 8 :=
  let block := aroundBlock at.row at.column
  let keep := (near: Position) => not (near.row == at.row && near.column == at.column)
  let fewer := List.countLtMem block keep (near => True) (near member kept => rfl) at (atInBlock at) rfl (centreDropped at)
  let all: block.count (near => True) = block.length := Eq.trans (List.countOccurrences block (near => True)) (List.occurrencesTrue block)
  let small := blockAtMost9 at.row at.column
  rewrite List.lengthFilter block keep in omega

theorem centreDropped (centre: Position): not (centre.row == centre.row && centre.column == centre.column) = False :=
  rewrite DecEq.refl centre.row, DecEq.refl centre.column in rfl

theorem atInBlock (centre: Position): centre ∈ aroundBlock centre.row centre.column := match centre with
  | { row = r, column = c } =>
    List.memFlatMapIntro (row => List.map (List.range (c - 1) (c + 1 + 1)) (column => ({ row, column }: Position))) r { row = r, column = c }
      (List.range (r - 1) (r + 1 + 1)) (((List.memRange r (r - 1) (r + 1 + 1)).backward (Both (omega) (Nat.leLessSucc r (r + 1) (omega)))))
      (List.memMap (List.range (c - 1) (c + 1 + 1)) c (((List.memRange c (c - 1) (c + 1 + 1)).backward (Both (omega) (Nat.leLessSucc c (c + 1) (omega))))) (column => ({ row = r, column }: Position)))

theorem blockAtMost9 (r: Nat) (c: Nat): (aroundBlock r c).length ≤ 9 :=
  let columns := List.range (c - 1) (c + 1 + 1)
  let each := (row: Nat) => List.map columns (column => ({ row, column }: Position))
  let rowCount := List.lengthRange (r - 1) (r + 1 + 1)
  let columnCount := List.lengthRange (c - 1) (c + 1 + 1)
  calc (aroundBlock r c).length
    _ = (List.range (r - 1) (r + 1 + 1)).sumBy (row => (each row).length) := List.lengthFlatMap each (List.range (r - 1) (r + 1 + 1))
    _ ≤ (List.range (r - 1) (r + 1 + 1)).sumBy (row => 3) := List.sumByLe _ _ _ (row => rewrite List.lengthMap columns (column => ({ row, column }: Position)) in omega)
    _ = 3 * (List.range (r - 1) (r + 1 + 1)).length := sumByThree (List.range (r - 1) (r + 1 + 1))
    _ ≤ 9 := omega

--| Threes added up over a list.
theorem sumByThree (xs: List a): xs.sumBy (x => 3) = 3 * xs.length := match xs with
  | [] => omega
  | [x, ..rest] => rewrite List.sumByCons rest x (x => 3), sumByThree rest in omega
