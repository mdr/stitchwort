--| The pocket the program starts from is the spec's start, and its cycles
--| are the spec's cycles.

namespace Aoc.Year2020.Day17.Proofs
import Aoc.Year2020.Day17 (..)
import Aoc.Year2020.Day17 (Spec)
import Aoc.Common (Position)
import Aoc.Common.Proofs (memGridPositionsWhere)
import Std (DecEq, Eq, Exists, List, Nat, Set)

theorem startsPocket ∀ (slice: Slice) (dimensions: Nat):
    Spec.Starts slice dimensions (slice.pocket dimensions).active :=
  let cubes := slice.grid.positionsWhere (== Active)
  cube =>
    {
      forward = there =>
        Exists.elim
          (List.memMapElim
            (Cube.inSlice dimensions)
            cube
            cubes
            ((Set.containsFromListIff (cubes.map (Cube.inSlice dimensions)) cube).forward there))
          (at (Both member made) =>
            Exists.elim ((memGridPositionsWhere slice.grid (== Active) at).forward member) (state (Both found active) =>
              match at with
                | { row, column } =>
                  Witness column (Witness row (Both (rewrite <- active.read in found) (rewrite <- made in rfl))))),
      backward = (Witness x (Witness y (Both found written))) =>
        let at: Position := { row = y, column = x }
        let member: at ∈ cubes :=
          (memGridPositionsWhere slice.grid (== Active) at).backward (Witness Active (Both found rfl))
        let made: Cube.inSlice dimensions at = cube := Cube.ext _ _ (Eq.sym written)
        (Set.containsFromListIff (cubes.map (Cube.inSlice dimensions)) cube).backward
          (rewrite <- made in List.memMap cubes at member (Cube.inSlice dimensions))
    }

theorem cycles ∀ (count: Nat) (pocket: Pocket):
    Spec.Cycles count pocket.active (Nat.iterate count Pocket.cycle pocket).active :=
  match count with
    | Zero => rfl
    | Succ more => Witness pocket.cycle.active (Both (cube => cycleActive pocket cube) (cycles more pocket.cycle))
