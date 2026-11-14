--| The positions `around` lists are exactly those at most `length` away
--| (`aroundSound`, `aroundComplete`), each once (`distinctAround`).

namespace Aoc.Year2024.Day20.Proofs
import Aoc.Year2024.Day20 (..)
import Aoc.Common (Direction, Position, directions)
import Std (And, Eq, Exists, List, Nat)

--| The row of positions in the diamond, `spare` either side of the column.
def aroundRow (position: Position) (length row: Nat): List Position :=
  let spare := length - Nat.absDiff row position.row
  List.range (position.column - spare) (position.column + spare + 1) |> .map (column => ({ row, column }: Position))

theorem aroundRows ∀ (position: Position) (length: Nat):
    position.diamond length
      = List.range (position.row - length) (position.row + length + 1) |> .flatMap (aroundRow position length) :=
  rfl

--| Every position listed is at most `length` away.
theorem aroundSound ∀ (position: Position) (length: Nat) (other: Position)
    (member: other ∈ position.diamond length):
    position.distance other ≤ length :=
  let rows := List.range (position.row - length) (position.row + length + 1)
  List.anyElim _ _ rows
    (List.memFlatMapElim (aroundRow position length) other rows (rewrite <- aroundRows position length in member))
    (row rowMember inRow =>
      Exists.elim (List.memMapElim _ other _ inRow) (column both =>
        let (Both columnMember same) := both
        let (Both rowLow rowHigh) := ((List.memRange _ _ _).forward rowMember)
        let (Both columnLow columnHigh) := ((List.memRange _ _ _).forward columnMember)
        rewrite <- same in omega [rowLow, rowHigh, columnLow, columnHigh]))

--| Every position at most `length` away is listed.
theorem aroundComplete ∀ (position: Position) (length: Nat) (other: Position)
    (near: position.distance other ≤ length):
    other ∈ position.diamond length :=
  match other with
    | { row, column } =>
      let spare := length - Nat.absDiff row position.row
      rewrite aroundRows position length in
        List.memFlatMapIntro
          (aroundRow position length)
          row
          ({ row, column }: Position)
          (List.range (position.row - length) (position.row + length + 1))
          (((List.memRange row (position.row - length) (position.row + length + 1)).backward
            (Both (omega [near]) (Nat.leLessSucc row (position.row + length) (omega [near])))))
          (List.memMap
            (List.range (position.column - spare) (position.column + spare + 1))
            column
            (((List.memRange column (position.column - spare) (position.column + spare + 1)).backward
              (Both (omega [near]) (Nat.leLessSucc column (position.column + spare) (omega [near])))))
            (other => ({ row, column = other }: Position)))

--| No position is listed twice.
theorem distinctAround ∀ (position: Position) (length: Nat): List.Distinct (position.diamond length) :=
  rewrite aroundRows position length in
    List.distinctFlatMap
      (aroundRow position length)
      (other => other.row)
      (List.range (position.row - length) (position.row + length + 1))
      (List.distinctRange (position.row - length) (position.row + length + 1))
      (row member =>
        let spare := length - Nat.absDiff row position.row
        List.distinctMap
          (List.range (position.column - spare) (position.column + spare + 1))
          (List.distinctRange _ _)
          (column => ({ row, column }: Position))
          (first second same => Eq.cong (other => other.column) same))
      (row member other inRow =>
        Exists.elim (List.memMapElim _ other _ inRow) (column both => rewrite <- And.right both in rfl))
