-- The positions `around` lists are exactly those at most `length` away
-- (`aroundSound`, `aroundComplete`), each once (`distinctAround`).

namespace Aoc.Year2024.Day20.Proofs
import Aoc.Year2024.Day20 (..)
import Aoc.Year2024.Day16.Proofs (memMapElim)
import Std (And, Eq, Exists, List, Nat)

-- The row of positions in the diamond, `spare` either side of the column.
def aroundRow (position: Position) (length: Nat) (row: Nat): List Position :=
  let spare := length - Nat.absDiff row position.row
  List.between (position.column - spare) (position.column + spare) |> .map (column => ({ row, column }: Position))

theorem aroundRows (position: Position) (length: Nat):
    position.around length = List.between (position.row - length) (position.row + length) |> .flatMap (aroundRow position length) :=
  rfl

-- Every position listed is at most `length` away.
theorem aroundSound (position: Position) (length: Nat) (other: Position) (member: other ∈ position.around length):
    position.distance other ≤ length :=
  let rows := List.between (position.row - length) (position.row + length)
  List.anyElim _ _ rows (List.memFlatMapElim (aroundRow position length) other rows (rewrite <- aroundRows position length in member))
    (row rowMember inRow =>
      Exists.elim (memMapElim _ other _ inRow) (column both =>
        let (Both columnMember same) := both
        let (Both rowLow rowHigh) := List.memBetween rowMember
        let (Both columnLow columnHigh) := List.memBetween columnMember
        rewrite <- same in omega [rowLow, rowHigh, columnLow, columnHigh]))

-- Every position at most `length` away is listed.
theorem aroundComplete (position: Position) (length: Nat): (other: Position) → position.distance other ≤ length → other ∈ position.around length
  | { row, column }, near =>
    let spare := length - Nat.absDiff row position.row
    rewrite aroundRows position length in
      List.memFlatMapIntro (aroundRow position length) row ({ row, column }: Position) (List.between (position.row - length) (position.row + length))
        (List.memBetweenIntro row (position.row - length) (position.row + length) (omega [near])
          (omega [near]))
        (List.memMap (List.between (position.column - spare) (position.column + spare)) column
          (List.memBetweenIntro column (position.column - spare) (position.column + spare)
            (omega [near]) (omega [near]))
          (other => ({ row, column = other }: Position)))

-- No position is listed twice.
theorem distinctAround (position: Position) (length: Nat): List.Distinct (position.around length) :=
  rewrite aroundRows position length in
    List.distinctFlatMap (aroundRow position length) (other => other.row) (List.between (position.row - length) (position.row + length))
      (List.distinctBetween (position.row - length) (position.row + length))
      (row member =>
        let spare := length - Nat.absDiff row position.row
        List.distinctMap (List.between (position.column - spare) (position.column + spare)) (List.distinctBetween _ _)
          (column => ({ row, column }: Position)) (first second same => Eq.cong (other => other.column) same))
      (row member other inRow => Exists.elim (memMapElim _ other _ inRow) (column both => rewrite <- And.right both in rfl))
