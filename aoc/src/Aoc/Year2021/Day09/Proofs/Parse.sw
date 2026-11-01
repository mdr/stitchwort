-- The parser keeps the puzzle's promises (D2108): every height is a digit,
-- 0 to 9, by its type (`Fin 10`; `heightBelow10` in Facts.sw), and every
-- row of a successful parse is as long as the first, so the map is a
-- rectangle. Neither theorem of the answers needs either: they hold for
-- every map, rectangular or not.

namespace Aoc.Year2021.Day09.Proofs
import Aoc.Year2021.Day09 (..)
import Std (Bool, Decidable, Eq, Fail, Fin, List, Nat, Option, Result, Void)

-- Every row `parseHeightMap` reads is as long as the first.
theorem parseRectangular (input: Text) (map: HeightMap) (parsed: Fail.toResult (() => parseHeightMap input) = Ok map) (row: List (Fin 10))
    (member: row ∈ map.rows): row.length = width map.rows :=
  checkedRectangular _ map parsed row member

-- Whatever reads the rows, `checkRows` passes on only rows as long as the
-- first.
theorem checkedRectangular (read: () → {Fail} (List (List (Fin 10)))) (map: HeightMap) (parsed: Fail.toResult (() => checkRows (read ())) = Ok map)
    (row: List (Fin 10)) (member: row ∈ map.rows): row.length = width map.rows :=
  let split := rewrite Fail.toResultThen read checkRows at parsed
  Result.flatMapEqOk (Fail.toResult read) (x => Fail.toResult (() => checkRows x)) map split
    (rows _ checked => checkRowsOk rows map checked row member)

-- `checkRows` keeps its rows, and only if each is as long as the first.
theorem checkRowsOk (rows: List (List (Fin 10))) (map: HeightMap) (h: Fail.toResult (() => checkRows rows) = Ok map) (row: List (Fin 10))
    (member: row ∈ map.rows): row.length = width map.rows :=
  match e: firstRagged rows with
    | Some (index, _) => Void.exfalso (Result.errNotOk _ map h)
    | None =>
      let same: rows = map.rows := Eq.cong HeightMap.rows (Result.okInjective _ map h)
      let notRagged := findIndexedNone (row => row.length != width rows) 0 rows e
      let atRow := List.allMem _ row rows (List.allToAll _ rows notRagged) (rewrite same in member)
      rewrite <- same in sameOfNotDiffer row.length (width rows) atRow

-- `not (a != b)` is `a = b`.
theorem sameOfNotDiffer (a: Nat) (b: Nat) (h: not (a != b) = True): a = b :=
  Decidable.elimProof (Nat.decEq a b) (same => same)
    (differ => Void.exfalso (Bool.falseNotTrue (rewrite Decidable.toBoolOf (Decidable.not (Nat.decEq a b)) differ at h in h)))

-- No element of a list paired with its index is `bad`: none of the
-- elements is.
theorem findIndexedNone (bad: a → Bool): (i: Nat) → (xs: List a) →
    (List.withIndexFrom i xs).find (((_, x)) => bad x) = None → xs.all (x => not (bad x)) = True
  | i, Nil, h => rfl
  | i, Cons x rest, h =>
    match e: bad x with
      | False => findIndexedNone bad (Succ i) rest h
      | True => Void.exfalso (Option.noneNotSome _ (Eq.sym h))
