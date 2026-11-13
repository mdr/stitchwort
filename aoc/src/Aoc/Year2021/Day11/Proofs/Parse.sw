--| The parser keeps the puzzle's promises: every level of a successful
--| parse is a digit, 0 to 9, and every row is as long as the first, so the
--| grid is a rectangle (the shared grid parser's `parseGridRectangle`).
--| The answers' theorems need neither: they hold for every grid, ragged or
--| not, with any levels.
-- (D2108)

namespace Aoc.Year2021.Day11.Proofs
import Aoc.Year2021.Day11 (..)
import Aoc.Common (Grid, parseGrid)
import Aoc.Common.Proofs (parseGridRectangle)
import Std (Eq, Exists, Fail, Fin, List, Nat, Option, Result, Void)
import Std.Parse (digit)

--| Every level `parseCavern` reads is 9 or less...
theorem parseDigits ∀ (input: Text) (cavern: Cavern) (parsed: Fail.toResult (() => parseCavern input) = Ok cavern)
    (row: List Nat) (rowIn: row ∈ cavern.grid.rows) (level: Nat) (levelIn: level ∈ row): level ≤ 9 :=
  Exists.elim (parsedGrid input cavern parsed) (digits both =>
    let (Both same _) := both
    Exists.elim (List.memMapElim (digits => digits.map Fin.toNat) row digits.rows (rewrite same at rowIn in rowIn)) (read found =>
      let (Both _ made) := found
      Exists.elim (List.memMapElim Fin.toNat level read (rewrite made in levelIn)) (cell found =>
        rewrite <- And.right found in omega [Fin.toNatLt cell])))

--| ...and every row is as long as the first.
theorem parseRectangular ∀ (input: Text) (cavern: Cavern) (parsed: Fail.toResult (() => parseCavern input) = Ok cavern)
    (row: List Nat) (rowIn: row ∈ cavern.grid.rows): row.length = cavern.grid.width :=
  Exists.elim (parsedGrid input cavern parsed) (digits both =>
    let (Both same rectangle) := both
    Exists.elim (List.memMapElim (digits => digits.map Fin.toNat) row digits.rows (rewrite same at rowIn in rowIn)) (read found =>
      let (Both readIn made) := found
      rewrite same, <- made, List.lengthMap read Fin.toNat, digitsFirstWidth digits.rows in rectangle read readIn))

--| What `parseCavern` reads is a rectangle of digits read as numbers.
theorem parsedGrid ∀ (input: Text) (cavern: Cavern) (parsed: Fail.toResult (() => parseCavern input) = Ok cavern):
    ∃ (digits: Grid (Fin 10)) => cavern = Cavern.ofDigits digits ∧ digits.Rectangle :=
  let split := rewrite Fail.toResultThen (() => parseGrid input digit) Cavern.ofDigits at parsed
  Result.flatMapEqOk (Fail.toResult (() => parseGrid input digit)) (digits => Fail.toResult (() => Cavern.ofDigits digits)) cavern split
    (digits read made => Witness digits (Both (Eq.sym (Result.okInjective made)) (And.left (parseGridRectangle input digit digits read))))
