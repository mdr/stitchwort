--| Counting over the eight positions around a cell, with the cell at each
--| looked up, counts the touching cells: what a program writes with
--| `at.around` and a lookup is what a spec says with `cells` and
--| `touching`.

namespace Aoc.Common.Proofs
import Aoc.Common (..)
import Std (Bool, Eq, List, Option, Void)

--| How many of the cells around `at` pass `keep`, looked up position by
--| position, is how many cells touching `at` pass it.
theorem countAround (rows: List (List a)) (keep: a → Bool) (at: Position):
    at.around.count (near => (cellAt rows near).any keep) = (cells rows).count (((other, x)) => touching at other && keep x) :=
  let held := (q: Position) => (cellAt rows q).any keep
  let positions := (cells rows).map Pair.fst
  let near := (q: Position) => touching at q && held q
  let onGrid := (q: Position) (passes: held q = True) =>
    match found: cellAt rows q with
      | None => Void.exfalso (Bool.falseNotTrue passes)
      | Some x => List.memMap (cells rows) (q, x) (memCellsOfCellAt rows q x found) Pair.fst
  let same: List.Perm (at.around.filter held) (positions.filter near) :=
    List.permOfSameMembers (at.around.filter held) (positions.filter near) (List.distinctFilter at.around held (aroundDistinct at))
      (List.distinctFilter positions near (cellPositionsDistinct rows))
      (q member =>
        let (Both inAround passes) := List.memFilter at.around held member
        List.memFilterIntro positions near (onGrid q passes) (Bool.andIntro (aroundTouching at q inAround) passes))
      (q member =>
        let (Both inGrid both) := List.memFilter positions near member
        List.memFilterIntro at.around held (touchingAround at q (Bool.andLeft both)) (Bool.andRight both))
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
