--| Facts about the map that both parts use: a cell's height is the height
--| at its position, below 10, and a position with a height is a cell. (The
--| neighbours are the adjacent positions by the shared grid code's
--| `neighbourAdjacent` and `adjacentNeighbour`.)

namespace Aoc.Year2021.Day09.Proofs
import Aoc.Year2021.Day09 (..)
import Aoc.Common (Position, cellAt, cells, memCellsOfCellAt)
import Aoc.Common.Proofs (cellAtOfMemCells)
import Std (Eq, Exists, Fin, List, Nat, Option, Void)

--| A cell is a digit of the grid, at its position.
theorem memCellsElim ∀ (map: HeightMap) (position: Position) (height: Nat)
    (member: (position, height) ∈ map.cells):
    ∃ (digit: Fin 10) => cellAt map.grid.rows position = Some digit ∧ digit.toNat = height :=
  Exists.elim
    (List.memMapElim (cell => (cell.fst, cell.snd.toNat)) (position, height) (cells map.grid.rows) member)
    (entry both =>
      match entry with
        | (at, digit) =>
          let (Both inCells same) := both
          let samePosition: at = position := Eq.cong Pair.fst same
          Witness digit
            (Both (rewrite <- samePosition in cellAtOfMemCells map.grid.rows at digit inCells) (Eq.cong Pair.snd same)))

--| A cell's height is the height at its position...
theorem heightOfMemCells ∀ (map: HeightMap) (position: Position) (height: Nat)
    (member: (position, height) ∈ map.cells):
    map.heightAt position = Some height :=
  Exists.elim (memCellsElim map position height member) (digit both =>
    let (Both found same) := both
    rewrite found, <- same in rfl)

--| ...and a digit's, below 10.
theorem heightBelow10 ∀ (map: HeightMap) (position: Position) (height: Nat)
    (member: (position, height) ∈ map.cells):
    height < 10 :=
  Exists.elim (memCellsElim map position height member) (digit both => rewrite <- And.right both in Fin.toNatLt digit)

--| A location with a height is one of the map's cells.
theorem memCellsOfHeight ∀ (map: HeightMap) (position: Position) (height: Nat)
    (found: map.heightAt position = Some height):
    (position, height) ∈ map.cells :=
  match c: cellAt map.grid.rows position with
    | Some digit =>
      let same: digit.toNat = height := Option.someInjective found
      rewrite <- same in
        List.memMap (cells map.grid.rows) (position, digit) (memCellsOfCellAt map.grid.rows position digit c) (cell =>
          (cell.fst, cell.snd.toNat))
