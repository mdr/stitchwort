-- The program's steps are the spec's: `step` reaches exactly the positions
-- one orthogonal step away (`stepOrthogonal`, `orthogonalStep`), and
-- `neighboursGrowing` gives exactly the touching plots (`memNeighboursGrowing`).
-- Touching goes both ways (`touchesSymmetric`).

namespace Aoc.Year2024.Day12.Proofs
import Aoc.Year2024.Day12 (..)
import Aoc.Year2024.Day12.Spec (..)
import Std (And, Bool, DecEq, Eq, Exists, Iff, List, Nat, Option, Or, Void)

-- `isOrthogonalStep` as a proposition.
def Orthogonal (from: Position) (to: Position): Prop :=
  Or (And (from.row = to.row) (Or (from.column + 1 = to.column) (to.column + 1 = from.column)))
    (And (from.column = to.column) (Or (from.row + 1 = to.row) (to.row + 1 = from.row)))

theorem eqTrue (x: Nat) (y: Nat) (same: x = y): (x == y) = True := rewrite same in DecEq.refl y

theorem orthogonalIntro (from: Position) (to: Position) (orthogonal: Orthogonal from to): isOrthogonalStep from to = True :=
  match orthogonal with
    | Inl (Both rows columns) =>
      Bool.orLeft _ _
        (Bool.andIntro _ _ (eqTrue _ _ rows)
          (match columns with
            | Inl right => Bool.orLeft _ _ (eqTrue _ _ right)
            | Inr left => Bool.orRight _ _ (eqTrue _ _ left)))
    | Inr (Both columns rows) =>
      Bool.orRight _ _
        (Bool.andIntro _ _ (eqTrue _ _ columns)
          (match rows with
            | Inl down => Bool.orLeft _ _ (eqTrue _ _ down)
            | Inr up => Bool.orRight _ _ (eqTrue _ _ up)))

theorem orthogonalElim (from: Position) (to: Position) (step: isOrthogonalStep from to = True): Orthogonal from to :=
  Bool.orElim _ _ _ step
    (across =>
      Inl
        (Both (DecEq.sound _ _ (Bool.andLeft _ _ across))
          (Bool.orElim _ _ _ (Bool.andRight _ _ across) (right => Inl (DecEq.sound _ _ right)) (left => Inr (DecEq.sound _ _ left)))))
    (upOrDown =>
      Inr
        (Both (DecEq.sound _ _ (Bool.andLeft _ _ upOrDown))
          (Bool.orElim _ _ _ (Bool.andRight _ _ upOrDown) (down => Inl (DecEq.sound _ _ down)) (up => Inr (DecEq.sound _ _ up)))))

-- A step in any direction is one orthogonal step.
theorem stepOrthogonal: (from: Position) → (side: Direction) → (to: Position) → from.step side = Some to → Orthogonal from to
  | { row = Succ above, column }, Up, to, stepped => rewrite <- Option.someInjective _ _ stepped in Inr (Both rfl (Inr (omega)))
  | { row = Zero, column }, Up, to, stepped => Void.exfalso (Option.noneNotSome to stepped)
  | { row, column }, Down, to, stepped => rewrite <- Option.someInjective _ _ stepped in Inr (Both rfl (Inl (omega)))
  | { row, column = Succ before }, Left, to, stepped => rewrite <- Option.someInjective _ _ stepped in Inl (Both rfl (Inr (omega)))
  | { row, column = Zero }, Left, to, stepped => Void.exfalso (Option.noneNotSome to stepped)
  | { row, column }, Right, to, stepped => rewrite <- Option.someInjective _ _ stepped in Inl (Both rfl (Inl (omega)))

-- One orthogonal step is a step in some direction.
theorem orthogonalStep: (from: Position) → (to: Position) → Orthogonal from to → Exists Direction (side => from.step side = Some to)
  | { row, column }, { row = toRow, column = toColumn }, Inl (Both rows (Inl right)) =>
    let same: Succ column = toColumn := omega
    rewrite <- rows, <- same in Witness Right rfl
  | { row, column = Zero }, { row = toRow, column = toColumn }, Inl (Both rows (Inr left)) => Void.exfalso (omega)
  | { row, column = Succ before }, { row = toRow, column = toColumn }, Inl (Both rows (Inr left)) =>
    let same: before = toColumn := omega
    rewrite <- rows, <- same in Witness Left rfl
  | { row, column }, { row = toRow, column = toColumn }, Inr (Both columns (Inl down)) =>
    let same: Succ row = toRow := omega
    rewrite <- columns, <- same in Witness Down rfl
  | { row = Zero, column }, { row = toRow, column = toColumn }, Inr (Both columns (Inr up)) => Void.exfalso (omega)
  | { row = Succ above, column }, { row = toRow, column = toColumn }, Inr (Both columns (Inr up)) =>
    let same: above = toRow := omega
    rewrite <- columns, <- same in Witness Up rfl

theorem orthogonalSymmetric (from: Position) (to: Position) (orthogonal: Orthogonal from to): Orthogonal to from :=
  match orthogonal with
    | Inl (Both rows (Inl right)) => Inl (Both (Eq.sym rows) (Inr right))
    | Inl (Both rows (Inr left)) => Inl (Both (Eq.sym rows) (Inl left))
    | Inr (Both columns (Inl down)) => Inr (Both (Eq.sym columns) (Inr down))
    | Inr (Both columns (Inr up)) => Inr (Both (Eq.sym columns) (Inl up))

-- Every direction is one of `directions`.
theorem memDirections: (side: Direction) → side ∈ directions
  | Up => Inl rfl
  | Down => Inr (Inl rfl)
  | Left => Inr (Inr (Inl rfl))
  | Right => Inr (Inr (Inr (Inl rfl)))

-- `growSame` as an equation.
theorem growSameElim (garden: Garden) (plot: Position) (other: Position) (same: growSame garden plot other = True):
    Exists Char (plant => And (garden.plantAt plot = Some plant) (garden.plantAt other = Some plant)) :=
  match grows: garden.plantAt plot with
    | Some plant => Witness plant (Both rfl (DecEq.sound _ _ same))
    | None => Void.exfalso (Bool.falseNotTrue same)

theorem growSameIntro (garden: Garden) (plot: Position) (other: Position) (plant: Char) (here: garden.plantAt plot = Some plant)
    (there: garden.plantAt other = Some plant): growSame garden plot other = True :=
  rewrite here, there in DecEq.refl (Some plant)

theorem touchesSymmetric (garden: Garden) (plot: Position) (other: Position) (touching: touches garden plot other = True): touches garden other plot = True :=
  Exists.elim (growSameElim garden plot other (Bool.andRight _ _ touching)) (plant both =>
    Bool.andIntro _ _ (orthogonalIntro other plot (orthogonalSymmetric plot other (orthogonalElim plot other (Bool.andLeft _ _ touching))))
      (growSameIntro garden other plot plant (And.right both) (And.left both)))

-- The neighbours a fill pushes are exactly the plots touching `plot` that
-- grow `plant`.
theorem memNeighboursGrowing (garden: Garden) (plant: Char) (plot: Position) (other: Position):
    other ∈ garden.neighboursGrowing plant plot ↔ And (Orthogonal plot other) (garden.plantAt other = Some plant) := {
  forward = member =>
    let both := List.memFilter (directions.filterMap plot.step) (next => garden.plantAt next == Some plant) other member
    Both
      (List.anyElim (side => plot.step side = Some other) _ directions (List.memFilterMapElim plot.step other directions (And.left both))
        (side inDirections stepped => stepOrthogonal plot side other stepped))
      (DecEq.sound _ _ (And.right both)),
  backward = has =>
    Exists.elim (orthogonalStep plot other (And.left has)) (side stepped =>
      List.memFilterIntro (directions.filterMap plot.step) (next => garden.plantAt next == Some plant) other
        (List.memFilterMapIntro plot.step side other directions (memDirections side) stepped) (rewrite And.right has in DecEq.refl (Some plant)))
}

-- A plot touching one that grows `plant` is a neighbour the fill pushes.
theorem touchingGrowing (garden: Garden) (plant: Char) (plot: Position) (other: Position) (grows: garden.plantAt plot = Some plant)
    (touching: touches garden plot other = True): other ∈ garden.neighboursGrowing plant plot :=
  Exists.elim (growSameElim garden plot other (Bool.andRight _ _ touching)) (same both =>
    let plantSame: same = plant := Option.someInjective _ _ (Eq.trans (Eq.sym (And.left both)) grows)
    (memNeighboursGrowing garden plant plot other).backward
      (Both (orthogonalElim plot other (Bool.andLeft _ _ touching)) (rewrite <- plantSame in And.right both)))

-- A neighbour the fill pushes from a plot growing `plant` touches it.
theorem growingTouches (garden: Garden) (plant: Char) (plot: Position) (other: Position) (grows: garden.plantAt plot = Some plant)
    (member: other ∈ garden.neighboursGrowing plant plot): touches garden plot other = True :=
  let both := (memNeighboursGrowing garden plant plot other).forward member
  Bool.andIntro _ _ (orthogonalIntro plot other (And.left both)) (growSameIntro garden plot other plant grows (And.right both))
