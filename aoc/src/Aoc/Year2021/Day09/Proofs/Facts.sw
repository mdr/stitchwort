-- Facts about the map that both parts use: a cell's height is the height
-- at its position, below 10, and the program's neighbours are the spec's
-- adjacent positions.

namespace Aoc.Year2021.Day09.Proofs
import Aoc.Year2021.Day09 (..)
import Aoc.Year2021.Day09.Spec (..)
import Std (Bool, DecEq, Eq, Exists, Fin, List, Nat, Option, Void)

-- A cell is a digit of the grid, at its position.
theorem memCellsElim (map: HeightMap) (position: Position) (height: Nat) (member: (position, height) ∈ map.cells):
    ∃ (digit: Fin 10) => (map.rows.getOr position.row Nil |> .get position.column) = Some digit ∧ digit.toNat = height :=
  Exists.elim
    (List.memMapElim (arg => (({ row = arg.fst.fst, column = arg.fst.snd }: Position), arg.snd.toNat)) (position, height) map.rows.gridCells member)
    (entry both =>
      match entry with
        | ((row, column), digit) =>
          let (Both inGrid same) := both
          let samePosition: ({ row, column }: Position) = position := Eq.cong Pair.fst same
          let sameHeight: digit.toNat = height := Eq.cong Pair.snd same
          Exists.elim ((List.memGridCells map.rows row column digit).forward inGrid) (cells found =>
            let (Both r c) := found
            Witness digit (Both (rewrite <- samePosition, List.getOrOfGet map.rows row Nil cells r in c) sameHeight)))

-- A cell's height is the height at its position...
theorem heightOfMemCells (map: HeightMap) (position: Position) (height: Nat) (member: (position, height) ∈ map.cells):
    map.heightAt position = Some height :=
  Exists.elim (memCellsElim map position height member) (digit both =>
    let (Both found same) := both
    rewrite found, <- same in rfl)

-- ...and a digit's, below 10.
theorem heightBelow10 (map: HeightMap) (position: Position) (height: Nat) (member: (position, height) ∈ map.cells): height < 10 :=
  Exists.elim (memCellsElim map position height member) (digit both => rewrite <- And.right both in Fin.toNatLt digit)

theorem equalOf (a: Nat) (b: Nat) (same: a = b): (a == b) = True := rewrite same in DecEq.refl b

-- The four steps are adjacent.
theorem upAdjacent (row: Nat) (column: Nat): adjacent { row = Succ row, column } { row, column } = True :=
  Bool.orRight _ _ (Bool.andIntro _ _ (DecEq.refl column) (Bool.orRight _ _ (equalOf (row + 1) (Succ row) (omega))))

theorem leftAdjacent (row: Nat) (column: Nat): adjacent { row, column = Succ column } { row, column } = True :=
  Bool.orLeft _ _ (Bool.andIntro _ _ (DecEq.refl row) (Bool.orRight _ _ (equalOf (column + 1) (Succ column) (omega))))

theorem rightAdjacent (row: Nat) (column: Nat): adjacent { row, column } { row, column = column + 1 } = True :=
  Bool.orLeft _ _ (Bool.andIntro _ _ (DecEq.refl row) (Bool.orLeft _ _ (DecEq.refl (column + 1))))

theorem downAdjacent (row: Nat) (column: Nat): adjacent { row, column } { row = row + 1, column } = True :=
  Bool.orRight _ _ (Bool.andIntro _ _ (DecEq.refl column) (Bool.orLeft _ _ (DecEq.refl (row + 1))))

-- Every neighbour is adjacent.
theorem neighboursAdjacent: (position: Position) → position.neighbours.all (adjacent position) = True
  | { row = Zero, column = Zero } => rewrite rightAdjacent 0 0, downAdjacent 0 0 in rfl
  | { row = Zero, column = Succ column } => rewrite leftAdjacent 0 column, rightAdjacent 0 (Succ column), downAdjacent 0 (Succ column) in rfl
  | { row = Succ row, column = Zero } => rewrite upAdjacent row 0, rightAdjacent (Succ row) 0, downAdjacent (Succ row) 0 in rfl
  | { row = Succ row, column = Succ column } =>
    rewrite upAdjacent row (Succ column), leftAdjacent (Succ row) column, rightAdjacent (Succ row) (Succ column), downAdjacent (Succ row) (Succ column) in rfl

theorem neighbourAdjacent (position: Position) (next: Position) (member: next ∈ position.neighbours): adjacent position next = True :=
  List.allMem (q => adjacent position q = True) next position.neighbours (List.allToAll (adjacent position) position.neighbours (neighboursAdjacent position)) member

-- ...and each adjacent position is a neighbour.
theorem adjacentNeighbour: (position: Position) → (next: Position) → adjacent position next = True → next ∈ position.neighbours
  | { row, column }, { row = r, column = c }, near =>
    Bool.orElim _ _ _ near
      (sameRow =>
        let rows: row = r := DecEq.sound row r (Bool.andLeft _ _ sameRow)
        Bool.orElim _ _ _ (Bool.andRight _ _ sameRow)
          (right => rewrite <- rows, <- DecEq.sound (column + 1) c right in memRight row column)
          (left => rewrite <- rows, <- DecEq.sound (c + 1) column left in memLeft row c))
      (sameColumn =>
        let columns: column = c := DecEq.sound column c (Bool.andLeft _ _ sameColumn)
        Bool.orElim _ _ _ (Bool.andRight _ _ sameColumn)
          (down => rewrite <- columns, <- DecEq.sound (row + 1) r down in memDown row column)
          (up => rewrite <- columns, <- DecEq.sound (r + 1) row up in memUp r column))

-- Each step is a neighbour.
theorem memUp (row: Nat) (column: Nat): ({ row, column }: Position) ∈ ({ row = row + 1, column }: Position).neighbours := Inl rfl

theorem memLeft: (row: Nat) → (column: Nat) → ({ row, column }: Position) ∈ ({ row, column = column + 1 }: Position).neighbours
  | Zero, column => Inl rfl
  | Succ row, column => Inr (Inl rfl)

theorem memRight: (row: Nat) → (column: Nat) → ({ row, column = column + 1 }: Position) ∈ ({ row, column }: Position).neighbours
  | Zero, Zero => Inl rfl
  | Zero, Succ column => Inr (Inl rfl)
  | Succ row, Zero => Inr (Inl rfl)
  | Succ row, Succ column => Inr (Inr (Inl rfl))

theorem memDown: (row: Nat) → (column: Nat) → ({ row = row + 1, column }: Position) ∈ ({ row, column }: Position).neighbours
  | Zero, Zero => Inr (Inl rfl)
  | Zero, Succ column => Inr (Inr (Inl rfl))
  | Succ row, Zero => Inr (Inr (Inl rfl))
  | Succ row, Succ column => Inr (Inr (Inr (Inl rfl)))
