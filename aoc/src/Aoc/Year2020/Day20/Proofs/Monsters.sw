--| Part 2, as far as it goes: where the program finds a sea monster is
--| where the spec says one is.

namespace Aoc.Year2020.Day20.Proofs
import Aoc.Year2020.Day20 (..)
import Aoc.Year2020.Day20 (Spec)
import Std (Bool, DecEq, Eq, List, Nat, Option, Pair, Set, Void)

theorem roughAtIff ∀ (image: Image) (at: List Nat):
    at ∈ image.roughAt ↔ ∃ (row: Nat) => ∃ (column: Nat) => at = [row, column] ∧ Spec.pixelAt image row column = Some Rough := {
  forward = member =>
    match (List.memFlatMap _ at image.rows.withIndex).forward member with
      | Witness (row, pixels) (Both inRows inRow) =>
        match (List.memFilterMap _ at pixels.withIndex).forward inRow with
          | Witness (column, pixel) (Both inPixels kept) =>
            match pixel with
              | Rough =>
                let rowFound := (List.memWithIndex image.rows row pixels).forward inRows
                let pixelFound := (List.memWithIndex pixels column Rough).forward inPixels
                Witness row (Witness column (Both (Eq.sym (Option.someInjective kept)) (rewrite rowFound, pixelFound in rfl))),
  backward = found =>
    match found with
      | Witness row (Witness column (Both same rough)) =>
        match rowFound: image.rows.get row with
          | Some pixels =>
            let pixelFound: pixels.get column = Some Rough := rough
            (List.memFlatMap _ at image.rows.withIndex).backward
              (Witness (row, pixels) (Both ((List.memWithIndex image.rows row pixels).backward rowFound)
                (List.memFilterMapIntro _ (column, Rough) at pixels.withIndex ((List.memWithIndex pixels column Rough).backward pixelFound) (rewrite same in rfl))))
}

theorem monsterIff ∀ (image: Image) (monster: Image) (row: Nat) (column: Nat):
    monster.roughAt.all (at => (Set.fromList image.roughAt).contains (shift [row, column] at)) = True ↔ Spec.MonsterAt image monster row column := {
  forward = all => r c drawn =>
    let onMonster := (roughAtIff monster [r, c]).backward (Witness r (Witness c (Both rfl drawn)))
    let contained := all.read [r, c] onMonster
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
theorem monsterStartsIff ∀ (image: Image) (monster: Image) (start: List Nat):
    start ∈ image.monsterStarts monster
      ↔ ∃ (row: Nat) => ∃ (column: Nat) =>
        start = [row, column]
          ∧ row + monster.rows.length ≤ image.rows.length
          ∧ column + (monster.rows.headOr []).length ≤ (image.rows.headOr []).length
          ∧ Spec.MonsterAt image monster row column :=
  let rough := image.roughAt.toSet
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

--| The pixels the program counts as part of a sea monster are exactly the
--| spec's.
theorem monsterPixelsIff ∀ (image: Image) (monster: Image) (at: List Nat):
    (image.monsterPixels monster).contains at = True ↔ Spec.Covered image monster at :=
  let place := (start: List Nat) => monster.roughAt.map (shift start)
  let inPixels := Set.containsFromListIff ((image.monsterStarts monster).flatMap place) at
  {
    forward = contained =>
      match (List.memFlatMap place at (image.monsterStarts monster)).forward (inPixels.forward contained) with
        | Witness start (Both isStart inPlace) =>
          match (monsterStartsIff image monster start).forward isStart with
            | Witness row (Witness column (Both same (Both rowFits (Both columnFits monsterAt)))) =>
              match List.memMapElim (shift start) at monster.roughAt inPlace with
                | Witness drawn (Both onMonster shifted) =>
                  match (roughAtIff monster drawn).forward onMonster with
                    | Witness r (Witness c (Both drawnAt rough)) =>
                      Witness row (Witness column (Witness r (Witness c
                        (Both rowFits (Both columnFits (Both monsterAt (Both rough (rewrite <- shifted, same, drawnAt in rfl)))))))),
    backward = covered =>
      match covered with
        | Witness row (Witness column (Witness r (Witness c (Both rowFits (Both columnFits (Both monsterAt (Both rough same))))))) =>
          let isStart := (monsterStartsIff image monster [row, column]).backward (Witness row (Witness column (Both rfl (Both rowFits (Both columnFits monsterAt)))))
          let onMonster := (roughAtIff monster [r, c]).backward (Witness r (Witness c (Both rfl rough)))
          inPixels.backward
            ((List.memFlatMap place at (image.monsterStarts monster)).backward
              (Witness [row, column] (Both isStart (rewrite same in List.memMap monster.roughAt [r, c] onMonster (shift [row, column])))))
  }

--| Counted over any listing of the image's `#`s, the spec's roughness with
--| sea monsters as `monster` draws them is the program's, and only it.
theorem roughnessExactly ∀ (image: Image) (monster: Image) (cells: List (List Nat)) (listed: Spec.RoughCells image cells) (answer: Nat):
    Spec.Roughness image monster cells answer ↔ answer = image.roughnessWith monster :=
  let rough := image.roughAt.toSet
  let covered := image.monsterPixels monster
  let free := (at: List Nat) => not (covered.contains at)
  let roughCell: ∀ (at: List Nat) => at ∈ cells → rough.contains at = True :=
    at member => (Set.containsFromListIff image.roughAt at).backward ((roughAtIff image at).backward ((listed.right at).forward member))
  let decides: ∀ (at: List Nat) => free at = True ↔ ¬Spec.Covered image monster at :=
    at => {
      forward = isFree => isCovered => Bool.falseNotTrue (Eq.trans (Eq.sym (Bool.notTrue _ isFree)) ((monsterPixelsIff image monster at).backward isCovered)),
      backward = notCovered =>
        match found: covered.contains at with
          | True => Void.exfalso (notCovered ((monsterPixelsIff image monster at).forward found))
          | False => rfl
    }
  let counted := List.countWithIff free decides cells answer
  let subset: ∀ (at: List Nat) => covered.contains at = True → rough.contains at = True :=
    at isCovered =>
      match (monsterPixelsIff image monster at).forward isCovered with
        | Witness row (Witness column (Witness r (Witness c (Both rowFits (Both columnFits (Both monsterAt (Both drawn same))))))) =>
          (Set.containsFromListIff image.roughAt at).backward
            ((roughAtIff image at).backward (Witness (row + r) (Witness (column + c) (Both same (monsterAt r c drawn)))))
  let parts := Set.sizeDifferenceSubset rough covered subset
  let freeSize := Set.sizeOfMembers (Set.difference rough covered) cells free listed.left
    (at inDifference =>
      let inRough := ((Set.containsDifferenceIff rough at covered).forward inDifference).left
      let found := (roughAtIff image at).forward ((Set.containsFromListIff image.roughAt at).forward inRough)
      let foundTrue: cells.contains at := (listed.right at).backward found
      foundTrue)
    (key listedHere =>
      rewrite Set.containsDifference rough key covered, roughCell key listedHere.read in rfl)
  let lengthCount := List.lengthFilter cells free
  {
    forward = numbered => rewrite (counted.forward numbered) in omega,
    backward = same => counted.backward (omega)
  }

theorem someMember ∀ [auto ord: Ord k] (set: Set k) (nonEmpty: (set.size > 0) = True): ∃ (key: k) => set.contains key = True :=
  match listed: set.toList with
    | [] => Void.exfalso (Bool.falseNotTrue (rewrite Set.sizeToList set, listed at nonEmpty in nonEmpty))
    | [key, ..rest] => Witness key ((Set.memToList set key).forward (rewrite listed in Inl rfl))

--| The orientation part 2 counts with is one of the sea monster's, and the
--| image has a sea monster that way round.
theorem roughnessTurned ∀ (image: Image) (monster: Image) (found: image.monsterTurned = Some monster):
    image.roughness = image.roughnessWith monster ∧ monster ∈ seaMonster.orientations ∧ ∃ (at: List Nat) => Spec.Covered image monster at :=
  match List.findSome seaMonster.orientations (turned => (image.monsterPixels turned).size > 0) monster found with
    | Both some member =>
      match someMember (image.monsterPixels monster) some with
        | Witness at covered => Both (Eq.cong image.roughnessFor found) (Both member (Witness at ((monsterPixelsIff image monster at).forward covered)))

-- `roughAt` lists each `#` once

theorem rowCellsDistinct ∀ (row: Nat) (pixels: List Pixel):
    List.Distinct (pixels.withIndex.filterMap (match some | (column, Rough) => [row, column])) :=
  let f: (Nat, Pixel) → Option (List Nat) := match some | (column, Rough) => [row, column]
  let hk: ∀ (cell: (Nat, Pixel)) (at: List Nat) => f cell = Some at → at = [row, cell.fst] := cell at kept =>
    match cell with
      | (column, Rough) => Eq.sym (Option.someInjective kept)
      | (column, Calm) => Void.exfalso (Option.noneNotSome at kept)
  let keyed: List.Distinct (pixels.withIndex.map (cell => [row, cell.fst])) :=
    rewrite List.withIndexFromRange pixels Calm 0, List.mapMap (List.range 0 pixels.length) (cell => [row, cell.fst]) (i => (0 + i, List.getOr pixels i Calm)) in
      List.distinctMap (List.range 0 pixels.length) (List.distinctRange 0 pixels.length) _ (i j same => omega [Eq.cong (xs => (xs.drop 1).headOr 0) same])
  rewrite <- List.mapId (pixels.withIndex.filterMap (match some | (column, Rough) => [row, column])) in
    List.distinctMapFilterMap f (cell => [row, cell.fst]) (at => at) hk pixels.withIndex keyed

--| A cell names its row, and the row's pixels are the image's row there,
--| so cells of different rows differ.
theorem roughAtDistinct ∀ (image: Image): List.Distinct image.roughAt :=
  let rowOf := (at: List Nat) => (at.headOr 0, (image.rows.get (at.headOr 0)).getOrElse [])
  List.distinctFlatMap _ rowOf image.rows.withIndex (List.distinctWithIndex image.rows)
    (entry member => rowCellsDistinct entry.fst entry.snd)
    (entry member at inRow =>
      match entry with
        | (row, pixels) =>
          match (List.memFilterMap _ at pixels.withIndex).forward inRow with
            | Witness (column, pixel) (Both inPixels kept) =>
              match pixel with
                | Rough => rewrite <- Option.someInjective kept, (List.memWithIndex image.rows row pixels).forward member in rfl)

theorem roughCells ∀ (image: Image): Spec.RoughCells image image.roughAt := Both (roughAtDistinct image) (at => roughAtIff image at)

--| Part 2 with the program's own listing of the `#`s: the spec's
--| roughness, with sea monsters as `monster` draws them, is the program's.
theorem roughnessListed ∀ (image: Image) (monster: Image) (answer: Nat):
    Spec.Roughness image monster image.roughAt answer ↔ answer = image.roughnessWith monster :=
  roughnessExactly image monster image.roughAt (roughCells image) answer
