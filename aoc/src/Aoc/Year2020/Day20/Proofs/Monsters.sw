--| Part 2, as far as it goes: where the program finds a sea monster is
--| where the spec says one is.

namespace Aoc.Year2020.Day20.Proofs
import Aoc.Year2020.Day20 (..)
import Aoc.Year2020.Day20 (Spec)
import Std (Bool, DecEq, Eq, List, Nat, Option, Pair, Set, Void)

theorem roughAtIff (image: Image) (at: List Nat):
    at ∈ image.roughAt ↔ ∃ (row: Nat) => ∃ (column: Nat) => at = [row, column] ∧ Spec.pixelAt image row column = Some Rough := {
  forward = member =>
    match (List.memFlatMap _ at image.rows.withIndex).forward member with
      | Witness (row, pixels) (Both inRows inRow) =>
        match List.memMapElim (cell => [row, cell.fst]) at _ inRow with
          | Witness (column, pixel) (Both kept same) =>
            match List.memFilter pixels.withIndex (cell => cell.snd == Rough) kept with
              | Both inPixels rough =>
                let rowFound := (List.memWithIndex image.rows row pixels).forward inRows
                let pixelFound := (List.memWithIndex pixels column pixel).forward inPixels
                Witness row (Witness column (Both (Eq.sym same) (rewrite rowFound, pixelFound, DecEq.sound rough in rfl))),
  backward = found =>
    match found with
      | Witness row (Witness column (Both same rough)) =>
        match rowFound: image.rows.get row with
          | None => Void.exfalso (Option.noneNotSome Rough rough)
          | Some pixels =>
            let pixelFound: pixels.get column = Some Rough := rough
            (List.memFlatMap _ at image.rows.withIndex).backward
              (Witness (row, pixels) (Both ((List.memWithIndex image.rows row pixels).backward rowFound)
                (rewrite same in
                  List.memMap _ (column, Rough)
                    (List.memFilterIntro pixels.withIndex (cell => cell.snd == Rough) ((List.memWithIndex pixels column Rough).backward pixelFound) rfl)
                    (cell => [row, cell.fst]))))
}
