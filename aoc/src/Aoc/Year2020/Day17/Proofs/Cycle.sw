--| A cycle of the program is the spec's, cube by cube: `lifeStep`'s
--| theorem (Aoc.Common.Proofs) with the cubes' neighbour count
--| (Neighbours.sw) and the puzzle's rule.

namespace Aoc.Year2020.Day17.Proofs
import Aoc.Year2020.Day17 (..)
import Aoc.Year2020.Day17 (Spec)
import Aoc.Common.Proofs (stepActive)
import Std (Bool, Eq, Nat)

theorem activeNextRule ∀ (active: Bool) (count near: Nat)
    (same: count = near):
    (count == 3 || (count == 2 && active)) = (if active then near == 2 || near == 3 else near == 3) :=
  rewrite same in
    match active with
      | True => cases
      | False => cases

theorem noneRule ∀ (active: Bool) (near: Nat)
    (none: 0 = near):
    False = (if active then near == 2 || near == 3 else near == 3) :=
  rewrite <- none in
    match active with
      | True => rfl
      | False => rfl

theorem lifeRuleDies ∀ (active: Bool): lifeRule active 0 = False := match active with
  | True => rfl
  | False => rfl

theorem cycleActive ∀ (pocket: Pocket) (cube: Cube):
    pocket.cycle.active.contains cube = Spec.activeAfter pocket.active cube :=
  calc pocket.cycle.active.contains cube
    _ = lifeRule (pocket.active.contains cube) (Spec.activeNeighbours pocket.active cube) :=
      stepActive Cube.neighbours Spec.neighbours countNeighbours lifeRule lifeRuleDies pocket.active cube
    _ = Spec.activeAfter pocket.active cube := activeNextRule (pocket.active.contains cube) _ _ rfl
