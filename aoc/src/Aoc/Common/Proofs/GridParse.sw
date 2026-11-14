--| The grid parser keeps the puzzles' promise: a grid that `parseGrid`
--| reads is a rectangle with at least one cell. A day's own parser
--| built on it gets the same from `checkedGrid`.
-- (D2108)

namespace Aoc.Common.Proofs
import Aoc.Common (..)
import Std (Bool, DecEq, Decidable, Eq, Fail, List, Nat, Option, Parse, Result, Void)

--| A grid `parseGrid` reads is a rectangle, with a row and a column.
theorem parseGridRectangle ∀ (input: Text) (cell: () → {Parse} a) (grid: Grid a)
    (parsed: Fail.toResult (() => parseGrid input cell) = Ok grid):
    grid.Rectangle ∧ 0 < grid.width ∧ 0 < grid.height :=
  checkedGrid _ grid parsed

--| Whatever reads the rows, `checkGrid` passes on only a rectangle with a
--| cell.
theorem checkedGrid ∀ (read: () → {Fail} List (List a)) (grid: Grid a)
    (parsed: Fail.toResult (() => checkGrid (read ())) = Ok grid):
    grid.Rectangle ∧ 0 < grid.width ∧ 0 < grid.height :=
  let split := rewrite Fail.toResultThen read checkGrid at parsed
  Result.flatMapEqOk (Fail.toResult read) (x => Fail.toResult (() => checkGrid x)) grid split (rows _ checked =>
    checkGridOk rows grid checked)

--| `checkGrid` keeps its rows, and only if the first has a cell and each is
--| as long as the first.
theorem checkGridOk ∀ (rows: List (List a)) (grid: Grid a)
    (h: Fail.toResult (() => checkGrid rows) = Ok grid):
    grid.Rectangle ∧ 0 < grid.width ∧ 0 < grid.height :=
  match Nat.decEq (firstWidth rows) 0 with
    | { holds = False, sound = _, complete = c } =>
      let wide: firstWidth rows ≠ 0 := e => Bool.falseNotTrue (c e)
      match e: firstRagged rows with
        | Some (index, _) => Void.exfalso (Result.errNotOk h)
        | None =>
          let same: rows = grid.rows := Eq.cong Grid.rows (Result.okInjective h)
          let notRagged :=
            List.findNoneAll rows
              (row => row.length != firstWidth rows)
              (List.findWithIndexFromNone (row => row.length != firstWidth rows) 0 rows e)
          rewrite <- same in
            Both
              (row member =>
                DecEq.neFalse row.length
                  (firstWidth rows)
                  (Bool.notTrue _ (List.allMem _ row rows (List.allToAll _ rows notRagged) member)))
              (Both (omega [wide]) (tallOfWide rows (omega [wide])))

--| `checkGrid` passes its rows on unchanged.
theorem checkGridRows ∀ (rows: List (List a)) (grid: Grid a)
    (h: Fail.toResult (() => checkGrid rows) = Ok grid):
    rows = grid.rows :=
  match Nat.decEq (firstWidth rows) 0 with
    | { holds = False, sound = _, complete = _ } =>
      match ragged: firstRagged rows with
        | Some (index, _) => Void.exfalso (Result.errNotOk h)
        | None => Eq.cong Grid.rows (Result.okInjective h)

--| Rows whose first has a cell are at least one.
theorem tallOfWide ∀ (rows: List (List a)) (wide: 0 < firstWidth rows): 0 < rows.length := match rows with
  | [first, ..rest] => omega

--| The converse of `checkGridOk`: a grid that is a rectangle, with a cell, is
--| what `checkGrid` makes of its own rows.
theorem checkGridComplete ∀ (grid: Grid a) (rectangle: grid.Rectangle):
    Fail.toResult (() => checkGrid grid.rows) = Ok grid :=
  match Nat.decEq (firstWidth grid.rows) 0 with
    | { holds = True, sound = s, complete = _ } => Void.exfalso (grid.widthNonZero (s rfl))
    | { holds = False, sound = _, complete = _ } =>
      match ragged: firstRagged grid.rows with
        | Some (index, row) =>
          Void.exfalso
            (Option.noneNotSome
              (index, row)
              (Eq.trans
                (Eq.sym
                  (List.findNoneWithIndexFrom
                    (row => row.length != firstWidth grid.rows)
                    0
                    grid.rows
                    (List.findNoneOfMem (row => row.length != firstWidth grid.rows) grid.rows (row member =>
                      rewrite rectangle row member in DecEq.neSelf (firstWidth grid.rows)))))
                ragged))
        | None =>
          match grid with
            | { rows, nonEmpty } => rfl

--| The converse of `parseGridRectangle`: a rectangular grid
--| whose rows `Parse.eachLine` reads off the lines is what `parseGrid` reads.
theorem parseGridComplete ∀ (input: Text) (cell: () → {Parse} a) (grid: Grid a) (rectangle: grid.Rectangle)
    (rowsRead: Fail.toResult (() => Parse.eachLine input (() => Parse.many1 cell |> .toList)) = Ok grid.rows):
    Fail.toResult (() => parseGrid input cell) = Ok grid :=
  rewrite Fail.toResultThen (() => Parse.eachLine input (() => Parse.many1 cell |> .toList)) checkGrid, rowsRead in
    checkGridComplete grid rectangle
