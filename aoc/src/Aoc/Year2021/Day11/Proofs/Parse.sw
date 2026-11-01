-- The parser keeps the puzzle's promises (D2108): every level of a
-- successful parse is a digit, 0 to 9, and every row is as long as the
-- first, so the grid is a rectangle. The answers' theorems need neither:
-- they hold for every grid, ragged or not, with any levels.

namespace Aoc.Year2021.Day11.Proofs
import Aoc.Year2021.Day11 (..)
import Std (Bool, DecEq, Eq, Exists, Fail, Fin, List, Nat, Option, Result, Void)

-- Every level `parseLevels` reads is 9 or less...
theorem parseDigits (input: Text) (levels: List (List Nat)) (parsed: Fail.toResult (() => parseLevels input) = Ok levels)
    (row: List Nat) (rowIn: row ∈ levels) (level: Nat) (levelIn: level ∈ row): level ≤ 9 :=
  Exists.elim (parsedRows _ levels parsed) (rows both =>
    let (Both same _) := both
    Exists.elim (List.memMapElim (digits => digits.map Fin.toNat) row rows (rewrite <- same in rowIn)) (digits found =>
      let (Both _ made) := found
      Exists.elim (List.memMapElim Fin.toNat level digits (rewrite made in levelIn)) (digit read =>
        rewrite <- And.right read in omega [Fin.toNatLt digit])))

-- ...and every row is as long as the first.
theorem parseRectangular (input: Text) (levels: List (List Nat)) (parsed: Fail.toResult (() => parseLevels input) = Ok levels)
    (row: List Nat) (rowIn: row ∈ levels): row.length = (levels.headOr []).length :=
  Exists.elim (parsedRows _ levels parsed) (rows both =>
    let (Both same notRagged) := both
    Exists.elim (List.memMapElim (digits => digits.map Fin.toNat) row rows (rewrite <- same in rowIn)) (digits found =>
      let (Both digitsIn made) := found
      let atRow := List.allMem _ digits rows (List.allToAll _ rows notRagged) digitsIn
      rewrite same, <- made, List.lengthMap digits Fin.toNat, firstLength rows in DecEq.neFalse digits.length (width rows) (Bool.notTrue _ atRow)))

-- Whatever reads the rows, `checkRows` gives the rows' digits as numbers,
-- and only if no row is ragged.
theorem parsedRows (read: () → {Fail} (List (List (Fin 10)))) (levels: List (List Nat))
    (parsed: Fail.toResult (() => checkRows (read ())) = Ok levels):
    ∃ (rows: List (List (Fin 10))) => levels = rows.map (digits => digits.map Fin.toNat) ∧ rows.all (digits => not (digits.length != width rows)) = True :=
  let split := rewrite Fail.toResultThen read checkRows at parsed
  Result.flatMapEqOk (Fail.toResult read) (x => Fail.toResult (() => checkRows x)) levels split
    (rows _ checked => Witness rows (checkRowsOk rows levels checked))

-- `checkRows` gives the digits as numbers, and only if no row is ragged.
theorem checkRowsOk (rows: List (List (Fin 10))) (levels: List (List Nat)) (h: Fail.toResult (() => checkRows rows) = Ok levels):
    levels = rows.map (digits => digits.map Fin.toNat) ∧ rows.all (digits => not (digits.length != width rows)) = True :=
  match e: firstRagged rows with
    | Some (index, _) => Void.exfalso (Result.errNotOk _ levels h)
    | None => Both (Eq.sym (Result.okInjective _ levels h)) (List.findNoneAll rows (row => row.length != width rows) (List.findWithIndexFromNone (row => row.length != width rows) 0 rows e))

-- The first row read as numbers is as long as the first row of digits.
theorem firstLength: (rows: List (List (Fin 10))) → ((rows.map (digits => digits.map Fin.toNat)).headOr []).length = width rows
  | Nil => rfl
  | Cons first rest => List.lengthMap first Fin.toNat
