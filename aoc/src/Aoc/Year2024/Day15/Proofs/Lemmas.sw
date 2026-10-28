-- Facts the proofs need about positions: steps along a line never revisit
-- a position, and a step is undone by the opposite one.

namespace Aoc.Year2024.Day15.Proofs
import Aoc.Year2024.Day15 (..)
import Aoc.Year2024.Day15.Spec (ahead)
import Std (And, Bool, DecEq, Decidable, Eq, Exists, Int, List, Nat, Not, Or)

-- How far along `direction` a position is.
def progress (direction: Direction) (position: Position): Int :=
  match direction with
    | Up => 0 - position.row
    | Down => position.row
    | Left => 0 - position.column
    | Right => position.column

theorem progressStep (position: Position): (direction: Direction) → progress direction (position.step direction) = progress direction position + 1
  | Up => omega
  | Down => rfl
  | Left => omega
  | Right => rfl

theorem progressAhead (position: Position) (direction: Direction): (count: Nat) → progress direction (ahead position direction count) = progress direction position + count.toInt
  | Zero => omega
  | Succ count => omega [progressStep (ahead position direction count) direction, progressAhead position direction count]

-- Steps along a line never come back.
theorem aheadInjective (position: Position) (direction: Direction) (i: Nat) (j: Nat) (same: ahead position direction i = ahead position direction j): i = j :=
  omega [Eq.cong (progress direction) same, progressAhead position direction i, progressAhead position direction j]

-- Counting from the next position.
theorem aheadFrom (position: Position) (direction: Direction): (count: Nat) → ahead (position.step direction) direction count = ahead position direction (Succ count)
  | Zero => rfl
  | Succ count => Eq.cong (here => here.step direction) (aheadFrom position direction count)

theorem aheadAddOne (position: Position) (direction: Direction) (count: Nat):
    ahead position direction (count + 1) = (ahead position direction count).step direction :=
  rewrite Nat.addOne count in rfl

-- Whether `position` is one of the `count` positions after `start`.
theorem decideAhead (start: Position) (direction: Direction) (count: Nat) (position: Position):
    Or (∃ (j: Nat) => j < count ∧ position = ahead start direction (j + 1))
      ((i: Nat) → i < count → Not (position = ahead start direction (i + 1))) :=
  match found: (List.range count).any (i => position == ahead start direction (i + 1)) with
    | True =>
      List.anyTrueElim (List.range count) _ _ found
        (j member same => Inl (Witness j (Both (omega [List.memRangeFrom j count 0 member]) (DecEq.sound _ _ same))))
    | False =>
      Inr (i below same =>
        Bool.trueNotFalse
          (Eq.trans
            (Eq.sym
              (List.anyOfMem (List.range count) _ i (rewrite same in DecEq.refl (ahead start direction (i + 1)))
                (List.memRangeFromIntro i count 0 (omega) (omega))))
            found))

-- Positions with the same row and column are equal.
theorem positionEq: (position: Position) → (other: Position) → position.row = other.row → position.column = other.column → position = other
  | { row, column }, { row = otherRow, column = otherColumn }, rows, columns => rewrite rows, columns in rfl

theorem stepInjective (position: Position) (other: Position): (direction: Direction) → position.step direction = other.step direction → position = other
  | Up, same => positionEq position other (omega [Eq.cong (here => here.row) same]) (Eq.cong (here => here.column) same)
  | Down, same => positionEq position other (omega [Eq.cong (here => here.row) same]) (Eq.cong (here => here.column) same)
  | Left, same => positionEq position other (Eq.cong (here => here.row) same) (omega [Eq.cong (here => here.column) same])
  | Right, same => positionEq position other (Eq.cong (here => here.row) same) (omega [Eq.cong (here => here.column) same])

theorem stepRightLeft (position: Position): (position.step Right).step Left = position := positionEq ((position.step Right).step Left) position rfl (omega)

theorem stepLeftRight (position: Position): (position.step Left).step Right = position := positionEq ((position.step Left).step Right) position rfl (omega)

-- Steps in two directions can be taken in either order.
theorem stepRightComm (position: Position): (direction: Direction) → (position.step direction).step Right = (position.step Right).step direction
  | Up => rfl
  | Down => rfl
  | Left => positionEq ((position.step Left).step Right) ((position.step Right).step Left) rfl (omega)
  | Right => rfl
