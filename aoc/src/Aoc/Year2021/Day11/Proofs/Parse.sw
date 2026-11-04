--| The parser keeps the puzzle's promises: every level of a successful
--| parse is a digit, 0 to 9, and every row is as long as the first, so the
--| grid is a rectangle (the shared grid parser's `parseGridRectangle`).
--| The answers' theorems need neither: they hold for every grid, ragged or
--| not, with any levels.
-- (D2108)

namespace Aoc.Year2021.Day11.Proofs
import Aoc.Year2021.Day11 (..)
import Aoc.Common (Grid, firstWidth, parseGrid)
import Aoc.Common.Proofs (parseGridRectangle)
import Std (Eq, Exists, Fail, Fin, List, Nat, Option, Result, Void)
import Std.Parse (digit)

--| Every level `parseLevels` reads is 9 or less...
theorem parseDigits (input: Text) (levels: List (List Nat)) (parsed: Fail.toResult (() => parseLevels input) = Ok levels)
    (row: List Nat) (rowIn: row ∈ levels) (level: Nat) (levelIn: level ∈ row): level ≤ 9 :=
  Exists.elim (parsedGrid input levels parsed) (grid both =>
    let (Both same _) := both
    Exists.elim (List.memMapElim (digits => digits.map Fin.toNat) row grid.rows (rewrite <- same in rowIn)) (digits found =>
      let (Both _ made) := found
      Exists.elim (List.memMapElim Fin.toNat level digits (rewrite made in levelIn)) (cell read =>
        rewrite <- And.right read in omega [Fin.toNatLt cell])))

--| ...and every row is as long as the first.
theorem parseRectangular (input: Text) (levels: List (List Nat)) (parsed: Fail.toResult (() => parseLevels input) = Ok levels)
    (row: List Nat) (rowIn: row ∈ levels): row.length = (levels.headOr []).length :=
  Exists.elim (parsedGrid input levels parsed) (grid both =>
    let (Both same rectangle) := both
    Exists.elim (List.memMapElim (digits => digits.map Fin.toNat) row grid.rows (rewrite <- same in rowIn)) (digits found =>
      let (Both digitsIn made) := found
      rewrite same, <- made, List.lengthMap digits Fin.toNat, firstLength grid.rows in rectangle digits digitsIn))

--| What `parseLevels` reads is a rectangle of digits read as numbers.
theorem parsedGrid (input: Text) (levels: List (List Nat)) (parsed: Fail.toResult (() => parseLevels input) = Ok levels):
    ∃ (grid: Grid (Fin 10)) => levels = numbers grid ∧ grid.Rectangle :=
  let split := rewrite Fail.toResultThen (() => parseGrid input digit) numbers at parsed
  Result.flatMapEqOk (Fail.toResult (() => parseGrid input digit)) (grid => Fail.toResult (() => numbers grid)) levels split
    (grid read made => Witness grid (Both (Eq.sym (Result.okInjective _ levels made)) (And.left (parseGridRectangle input digit grid read))))

--| The first row read as numbers is as long as the first row of digits.
theorem firstLength: (rows: List (List (Fin 10))) → ((rows.map (digits => digits.map Fin.toNat)).headOr []).length = firstWidth rows
  | [] => rfl
  | [first, ..rest] => List.lengthMap first Fin.toNat
