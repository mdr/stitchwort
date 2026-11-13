--| Counting over the eight positions around a cell, with the cell at each
--| looked up, counts the touching cells: what a program writes with
--| `at.around` and a lookup is what a spec says with `cells` and
--| `touching`.

namespace Aoc.Common.Proofs
import Aoc.Common (..)
import Std (Bool, Eq, List, Nat, Option, Void)

--| How many of the cells around `at` pass `keep`, looked up position by
--| position, is how many cells touching `at` pass it.
theorem countAround (rows: List (List a)) (keep: a → Bool) (at: Position):
    at.around.count (near => (cellAt rows near).any keep) = (cells rows).count (((other, x)) => touching at other && keep x) :=
  let held := (q: Position) => (cellAt rows q).any keep
  let positions := (cells rows).map Pair.fst
  let near := (q: Position) => touching at q && held q
  let onGrid := (q: Position) (passes: held q = True) =>
    match found: cellAt rows q with
      | Some x => List.memMap (cells rows) (q, x) (memCellsOfCellAt rows q x found) Pair.fst
  let same: List.Perm (at.around.filter held) (positions.filter near) :=
    List.permOfSameMembers (at.around.filter held) (positions.filter near) (List.distinctFilter at.around held (aroundDistinct at))
      (List.distinctFilter positions near (cellPositionsDistinct rows))
      (q member =>
        let (Both inAround passes) := List.memFilter at.around held member
        List.memFilterIntro positions near (onGrid q passes) (Both (aroundTouching at q inAround) passes))
      (q member =>
        let (Both inGrid both) := List.memFilter positions near member
        List.memFilterIntro at.around held (touchingAround at q both.left) both.right)
  calc at.around.count held
    _ = (at.around.filter held).length := Eq.sym (List.lengthFilter at.around held)
    _ = (positions.filter near).length := List.permLength _ _ same
    _ = positions.count near := List.lengthFilter positions near
    _ = (cells rows).count (cell => near cell.fst) := List.countMap (cells rows) near Pair.fst
    _ = (cells rows).count (((other, x)) => touching at other && keep x) :=
      List.countCongMem (cells rows) (cell => near cell.fst) (((other, x)) => touching at other && keep x)
        (cell member =>
          match cell with
            | (other, x) => rewrite cellAtOfMemCells rows other x member in rfl)

--| Counting the positions around `at` that pass `keep` without building
--| them as lists is counting them in the list `at.around`.
theorem countAroundIsAround (at: Position) (keep: Position → Bool): at.countAround keep = at.around.count keep :=
  let mk := (row: Nat) (column: Nat) => ({ row, column }: Position)
  let near := (near: Position) => not (near.row == at.row && near.column == at.column)
  let cell := (row: Nat) (column: Nat) => if row == at.row && column == at.column then 0 else Bool.toNat (keep { row, column })
  let rows := List.range (at.row - 1) (at.row + 1 + 1)
  let columns := List.range (at.column - 1) (at.column + 1 + 1)
  let weight := (position: Position) => if near position then Bool.toNat (keep position) else 0
  let rowSum := (row: Nat) =>
    Eq.trans (List.sumByMap columns weight (column => mk row column))
      (List.sumByCong columns (column => weight (mk row column)) (column => cell row column) (column =>
        match e: row == at.row && column == at.column with
          | True => rfl
          | False => rfl))
  calc at.countAround keep
    _ = List.sumBy rows (row => List.sumBy columns (column => cell row column)) :=
      rewrite Nat.sumFromRangeFrom (row => Nat.sumFrom (at.column - 1) (column => cell row column) (at.column + 1 + 1 - (at.column - 1))) (at.row + 1 + 1 - (at.row - 1)) (at.row - 1) in
        List.sumByCong rows _ _ (row => Nat.sumFromRangeFrom (column => cell row column) (at.column + 1 + 1 - (at.column - 1)) (at.column - 1))
    _ = List.sumBy (List.flatMap rows (row => List.map columns (column => mk row column))) weight :=
      Eq.sym (Eq.trans (List.sumByFlatMap rows weight (row => List.map columns (column => mk row column))) (List.sumByCong rows _ _ rowSum))
    _ = List.sumBy (at.around) (position => Bool.toNat (keep position)) :=
      Eq.sym (List.sumByFilter (List.flatMap rows (row => List.map columns (column => mk row column))) (position => Bool.toNat (keep position)) near)
    _ = at.around.count keep := Eq.sym (List.countSumBy at.around keep)
