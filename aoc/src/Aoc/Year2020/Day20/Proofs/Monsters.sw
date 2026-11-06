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

theorem monsterIff (image: Image) (monster: Image) (row: Nat) (column: Nat):
    monster.roughAt.all (at => (Set.fromList image.roughAt).contains (shift [row, column] at)) = True ↔ Spec.MonsterAt image monster row column := {
  forward = all => r c drawn =>
    let onMonster := (roughAtIff monster [r, c]).backward (Witness r (Witness c (Both rfl drawn)))
    let contained := List.allMember _ monster.roughAt all [r, c] onMonster
    match (roughAtIff image [row + r, column + c]).forward ((Set.containsFromListIff image.roughAt [row + r, column + c]).forward contained) with
      | Witness r2 (Witness c2 (Both same rough)) =>
        let sameRow: row + r = r2 := Eq.cong (xs => xs.headOr 0) same
        let sameColumn: column + c = c2 := Eq.cong (xs => (xs.drop 1).headOr 0) same
        rewrite sameRow, sameColumn in rough,
  backward = monsterAt =>
    (List.allIff monster.roughAt _).backward
      (List.allOfMem _ monster.roughAt (at onMonster =>
        match (roughAtIff monster at).forward onMonster with
          | Witness r (Witness c (Both same drawn)) =>
            rewrite same in
              (Set.containsFromListIff image.roughAt [row + r, column + c]).backward
                ((roughAtIff image [row + r, column + c]).backward (Witness (row + r) (Witness (column + c) (Both rfl (monsterAt r c drawn)))))))
}

--| The program's monster starts are exactly the places where the spec has
--| a sea monster, as drawn, that fits within the image's height and its
--| first row's width.
theorem monsterStartsIff (image: Image) (monster: Image) (start: List Nat):
    start ∈ image.monsterStarts monster
      ↔ ∃ (row: Nat) => ∃ (column: Nat) =>
        start = [row, column]
          ∧ row + monster.rows.length ≤ image.rows.length
          ∧ column + (monster.rows.headOr []).length ≤ (image.rows.headOr []).length
          ∧ Spec.MonsterAt image monster row column :=
  let rough := Set.fromList image.roughAt
  let rows := image.rows.length + 1 - monster.rows.length
  let columns := (image.rows.headOr [] |> .length) + 1 - (monster.rows.headOr [] |> .length)
  let starts := List.range 0 rows |> .flatMap (row => List.range 0 columns |> .map (column => [row, column]))
  let isMonster := (start: List Nat) => monster.roughAt.all (at => rough.contains (shift start at))
  {
    forward = member =>
      match List.memFilter starts isMonster member with
        | Both inStarts kept =>
          match (List.memFlatMap _ start (List.range 0 rows)).forward inStarts with
            | Witness row (Both inRows inRow) =>
              match List.memMapElim (column => [row, column]) start _ inRow with
                | Witness column (Both inColumns same) =>
                  let rowBound := List.memRangeBounds row 0 rows inRows
                  let columnBound := List.memRangeBounds column 0 columns inColumns
                  Witness row (Witness column
                    (Both (Eq.sym same) (Both (omega) (Both (omega) ((monsterIff image monster row column).forward (rewrite <- same at kept in kept)))))),
    backward = found =>
      match found with
        | Witness row (Witness column (Both same (Both rowFits (Both columnFits monsterAt)))) =>
          let inStarts: [row, column] ∈ starts :=
            (List.memFlatMap _ [row, column] (List.range 0 rows)).backward
              (Witness row (Both (List.memRangeOf row 0 rows (omega)) (List.memMap _ column (List.memRangeOf column 0 columns (omega)) (column => [row, column]))))
          rewrite same in List.memFilterIntro starts isMonster inStarts ((monsterIff image monster row column).backward monsterAt)
  }
