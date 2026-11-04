--| The grid parser keeps the puzzles' promise: a grid that `parseGrid`
--| reads is a rectangle with at least one cell. A day's own parser
--| built on it gets the same from `checkedGrid`.
-- (D2108)

namespace Aoc.Common.Proofs
import Aoc.Common (..)
import Std (Bool, DecEq, Decidable, Eq, Fail, List, Nat, Option, Parse, Result, Void)

--| A grid `parseGrid` reads is a rectangle, with a row and a column.
theorem parseGridRectangle (input: Text) (cell: () → {Parse} a) (grid: Grid a) (parsed: Fail.toResult (() => parseGrid input cell) = Ok grid):
    grid.Rectangle ∧ 0 < grid.width ∧ 0 < grid.height :=
  checkedGrid _ grid parsed

--| Whatever reads the rows, `checkGrid` passes on only a rectangle with a
--| cell.
theorem checkedGrid (read: () → {Fail} List (List a)) (grid: Grid a) (parsed: Fail.toResult (() => checkGrid (read ())) = Ok grid):
    grid.Rectangle ∧ 0 < grid.width ∧ 0 < grid.height :=
  let split := rewrite Fail.toResultThen read checkGrid at parsed
  Result.flatMapEqOk (Fail.toResult read) (x => Fail.toResult (() => checkGrid x)) grid split (rows _ checked => checkGridOk rows grid checked)

--| `checkGrid` keeps its rows, and only if the first has a cell and each is
--| as long as the first.
theorem checkGridOk (rows: List (List a)) (grid: Grid a) (h: Fail.toResult (() => checkGrid rows) = Ok grid):
    grid.Rectangle ∧ 0 < grid.width ∧ 0 < grid.height :=
  match empty: firstWidth rows == 0 with
    | True => Void.exfalso (Result.errNotOk _ grid h)
    | False =>
      match e: firstRagged rows with
        | Some (index, _) => Void.exfalso (Result.errNotOk _ grid h)
        | None =>
          let same: rows = grid.rows := Eq.cong Grid.rows (Result.okInjective _ grid h)
          let notRagged :=
            List.findNoneAll rows (row => row.length != firstWidth rows) (List.findWithIndexFromNone (row => row.length != firstWidth rows) 0 rows e)
          let wide: firstWidth rows ≠ 0 := Decidable.toBoolFalse _ empty
          rewrite <- same in
            Both (row member => DecEq.neFalse row.length (firstWidth rows) (Bool.notTrue _ (List.allMem _ row rows (List.allToAll _ rows notRagged) member)))
              (Both (omega [wide]) (tallOfWide rows (omega [wide])))

--| Rows whose first has a cell are at least one.
theorem tallOfWide: (rows: List (List a)) → 0 < firstWidth rows → 0 < rows.length
  | Nil, wide => wide
  | Cons first rest, wide => omega
