-- What the graph for the flood fill needs: every step leads to a location
-- on the map.

namespace Aoc.Year2021.Day09
import Std (Bool, Eq, Exists, Fin, List, Option, Void)

-- A location with a height is one of the map's cells.
theorem HeightMap.memCellsOfHeight (map: HeightMap): (position: Position) → (height: Nat) → map.heightAt position = Some height →
    (position, height) ∈ map.cells
  | { row, column }, height, found =>
    match r: map.rows.get row with
      | None => Void.exfalso (Option.noneNotSome height (rewrite List.getOrGet map.rows row Nil, r at found))
      | Some cells =>
        let rowIs := List.getOrOfGet map.rows row Nil cells r
        match c: cells.get column with
          | None => Void.exfalso (Option.noneNotSome height (rewrite rowIs, c at found))
          | Some digit =>
            let same: digit.toNat = height := Option.someInjective _ _ (rewrite rowIs, c at found)
            let inGrid := (List.memGridCells map.rows row column digit).backward (Witness cells (Both r c))
            rewrite <- same in
              (List.memMap map.rows.gridCells ((row, column), digit) inGrid
                (arg => (({ row = arg.fst.fst, column = arg.fst.snd }: Position), arg.snd.toNat)))

-- Each step leads to a location on the map.
theorem HeightMap.edgesListed (map: HeightMap) (position: Position) (next: Position) (weight: Nat) (edge: (next, weight) ∈ map.edges position):
    next ∈ map.cells.map Pair.fst :=
  Exists.elim (List.memMapElim (other => (other, 1)) (next, weight) (position.neighbours.filter map.isOpen) edge) (other both =>
    let open := And.right (List.memFilter position.neighbours map.isOpen other (And.left both))
    let same: other = next := Eq.cong Pair.fst (And.right both)
    match h: map.heightAt other with
      | None => Void.exfalso (Bool.falseNotTrue open)
      | Some height => rewrite <- same in List.memMap map.cells (other, height) (map.memCellsOfHeight other height h) Pair.fst)
