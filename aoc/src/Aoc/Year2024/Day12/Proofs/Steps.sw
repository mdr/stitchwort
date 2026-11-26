--| The program's steps are the spec's: `step` reaches exactly the positions one
--| orthogonal step away (`stepOrthogonal`, `orthogonalStep`), and
--| `neighboursGrowing` gives exactly the touching plots (`memNeighboursGrowing`).
--| Touching goes both ways (`touchesSymmetric`).

namespace Aoc.Year2024.Day12.Proofs
import Aoc.Year2024.Day12 (..)
import Aoc.Common (Direction, Position, directions)
import Aoc.Year2024.Day12.Spec (..)
import Std (And, Bool, DecEq, Eq, Exists, Iff, List, Nat, Option, Or, Void)

--| `isOrthogonalStep` as a proposition.
def Orthogonal (from to: Position): Prop :=
  ((from.row = to.row) ∧ ((from.column + 1 = to.column) ∨ (to.column + 1 = from.column)))
    ∨ ((from.column = to.column) ∧ ((from.row + 1 = to.row) ∨ (to.row + 1 = from.row)))

theorem orthogonalIntro ∀ (from to: Position) (orthogonal: Orthogonal from to): isOrthogonalStep from to = True :=
  arithmetic

theorem orthogonalElim ∀ (from to: Position) (step: isOrthogonalStep from to = True): Orthogonal from to :=
  match step with
    | Inl (Both sameRow (Inl right)) => Inl (Both sameRow.read (Inl right.read))
    | Inl (Both sameRow (Inr left)) => Inl (Both sameRow.read (Inr left.read))
    | Inr (Both sameColumn (Inl down)) => Inr (Both sameColumn.read (Inl down.read))
    | Inr (Both sameColumn (Inr up)) => Inr (Both sameColumn.read (Inr up.read))

--| A step in any direction is one orthogonal step.
theorem stepOrthogonal ∀ (from: Position) (side: Direction) (to: Position)
    (stepped: from.step side = Some to):
    Orthogonal from to :=
  match from, side with
    | { row = Succ above, column }, Up =>
      rewrite <- Option.someInjective stepped then Inr (Both byComputing (Inr (arithmetic)))
    | { row, column }, Down => rewrite <- Option.someInjective stepped then Inr (Both byComputing (Inl (arithmetic)))
    | { row, column = Succ before }, Left =>
      rewrite <- Option.someInjective stepped then Inl (Both byComputing (Inr (arithmetic)))
    | { row, column }, Right => rewrite <- Option.someInjective stepped then Inl (Both byComputing (Inl (arithmetic)))

--| One orthogonal step is a step in some direction.
theorem orthogonalStep ∀ (from to: Position)
    (h: Orthogonal from to):
    Exists Direction (side => from.step side = Some to) :=
  match from, to, h with
    | { row, column }, { row = toRow, column = toColumn }, Inl (Both rows (Inl right)) =>
      let same: Succ column = toColumn := arithmetic
      rewrite <- rows, <- same then Witness Right byComputing
    | { row, column = Zero }, { row = toRow, column = toColumn }, Inl (Both rows (Inr left)) =>
      Void.impossible arithmetic
    | { row, column = Succ before }, { row = toRow, column = toColumn }, Inl (Both rows (Inr left)) =>
      let same: before = toColumn := arithmetic
      rewrite <- rows, <- same then Witness Left byComputing
    | { row, column }, { row = toRow, column = toColumn }, Inr (Both columns (Inl down)) =>
      let same: Succ row = toRow := arithmetic
      rewrite <- columns, <- same then Witness Down byComputing
    | { row = Zero, column }, { row = toRow, column = toColumn }, Inr (Both columns (Inr up)) =>
      Void.impossible arithmetic
    | { row = Succ above, column }, { row = toRow, column = toColumn }, Inr (Both columns (Inr up)) =>
      let same: above = toRow := arithmetic
      rewrite <- columns, <- same then Witness Up byComputing

theorem orthogonalSymmetric ∀ (from to: Position) (orthogonal: Orthogonal from to): Orthogonal to from :=
  match orthogonal with
    | Inl (Both rows (Inl right)) => Inl (Both rows.flipped (Inr right))
    | Inl (Both rows (Inr left)) => Inl (Both rows.flipped (Inl left))
    | Inr (Both columns (Inl down)) => Inr (Both columns.flipped (Inr down))
    | Inr (Both columns (Inr up)) => Inr (Both columns.flipped (Inl up))

--| Every direction is one of `directions`.
theorem memDirections ∀ (side: Direction): side ∈ directions := match side with
  | Up => Inl byComputing
  | Right => Inr (Inl byComputing)
  | Down => Inr (Inr (Inl byComputing))
  | Left => Inr (Inr (Inr (Inl byComputing)))

--| `growSame` as an equation.
theorem growSameElim ∀ (garden: Garden) (plot other: Position)
    (same: growSame garden plot other = True):
    Exists Char (plant => (garden.plantAt plot = Some plant) ∧ (garden.plantAt other = Some plant)) :=
  match grows: garden.plantAt plot with | Some plant => Witness plant (Both byComputing same.read)

theorem growSameIntro ∀ (garden: Garden) (plot other: Position) (plant: Char)
    (here: garden.plantAt plot = Some plant)
    (there: garden.plantAt other = Some plant):
    growSame garden plot other = True :=
  rewrite here, there then DecEq.refl (Some plant)

theorem touchesSymmetric ∀ (garden: Garden) (plot other: Position)
    (touching: touches garden plot other = True):
    touches garden other plot = True :=
  let Both across same := touching
  Exists.elim (growSameElim garden plot other same) (plant both =>
    Both
      (orthogonalIntro other plot (orthogonalSymmetric plot other (orthogonalElim plot other across)))
      (growSameIntro garden other plot plant both.right both.left))

--| The neighbours a fill pushes are exactly the plots touching `plot` that
--| grow `plant`.
theorem memNeighboursGrowing ∀ (garden: Garden) (plant: Char) (plot other: Position):
    other ∈ garden.neighboursGrowing plant plot ↔ (Orthogonal plot other) ∧ (garden.plantAt other = Some plant) :=
  {
    forward = member =>
      let both := List.memFilter (directions.filterMap plot.step) (next => garden.plantAt next == Some plant) member
      Both
        (List.anyElim
          (side => plot.step side = Some other) _
          directions
          (List.memFilterMapElim plot.step other directions both.left)
          (side inDirections stepped => stepOrthogonal plot side other stepped))
        both.right.read,
    backward = has =>
      Exists.elim (orthogonalStep plot other has.left) (side stepped =>
        List.memFilterIntro
          (directions.filterMap plot.step)
          (next => garden.plantAt next == Some plant)
          (List.memFilterMapIntro plot.step side other directions (memDirections side) stepped)
          (rewrite And.right has then DecEq.refl (Some plant)))
  }

--| A plot touching one that grows `plant` is a neighbour the fill pushes.
theorem touchingGrowing ∀ (garden: Garden) (plant: Char) (plot other: Position)
    (grows: garden.plantAt plot = Some plant)
    (touching: touches garden plot other = True):
    other ∈ garden.neighboursGrowing plant plot :=
  let Both across sameGrowth := touching
  Exists.elim (growSameElim garden plot other sameGrowth) (same both =>
    let plantSame: same = plant := Option.someInjective (Eq.trans both.left.flipped grows)
    (memNeighboursGrowing garden plant plot other).backward
      (Both (orthogonalElim plot other across) (rewrite <- plantSame then And.right both)))

--| A neighbour the fill pushes from a plot growing `plant` touches it.
theorem growingTouches ∀ (garden: Garden) (plant: Char) (plot other: Position)
    (grows: garden.plantAt plot = Some plant)
    (member: other ∈ garden.neighboursGrowing plant plot):
    touches garden plot other = True :=
  let both := (memNeighboursGrowing garden plant plot other).forward member
  Both (orthogonalIntro plot other both.left) (growSameIntro garden plot other plant grows both.right)
