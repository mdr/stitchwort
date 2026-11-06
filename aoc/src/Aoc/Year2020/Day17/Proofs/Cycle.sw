--| A cycle of the program is the spec's, cube by cube: the count it keeps
--| for each cube is the number of the cube's active neighbours, and a cube
--| missing from the counts has none.

namespace Aoc.Year2020.Day17.Proofs
import Aoc.Year2020.Day17 (..)
import Aoc.Year2020.Day17 (Spec)
import Std (Bool, Eq, List, Map, Nat, Option, Set)

theorem countsActive (active: Set Cube) (cube: Cube):
    (Map.counts (active.toList.flatMap (.neighbours))).getOr cube 0 = Spec.activeNeighbours active cube :=
  calc (Map.counts (active.toList.flatMap (.neighbours))).getOr cube 0
    _ = (active.toList.flatMap (.neighbours)).count (== cube) := Map.getOrCounts cube _
    _ = active.toList.sumBy (other => other.neighbours.count (== cube)) := List.countFlatMap (.neighbours) (== cube) active.toList
    _ = active.toList.sumBy (other => Bool.toNat (Spec.neighbours other cube)) := List.sumByCong active.toList _ _ (other => countNeighbours other cube)
    _ = active.toList.count (other => Spec.neighbours other cube) := Eq.sym (List.countSumBy active.toList _)
    _ = Spec.activeNeighbours active cube := Eq.sym (Set.countToList active _)

theorem activeNextRule (active: Bool) (count: Nat) (near: Nat) (same: count = near):
    (count == 3 || (count == 2 && active)) = (if active then near == 2 || near == 3 else near == 3) :=
  rewrite same in
    match active with
      | True => cases
      | False => cases

theorem noneRule (active: Bool) (near: Nat) (none: 0 = near): False = (if active then near == 2 || near == 3 else near == 3) :=
  rewrite <- none in
    match active with
      | True => rfl
      | False => rfl

theorem cycleActive (pocket: Pocket) (cube: Cube): pocket.cycle.active.contains cube = Spec.activeAfter pocket.active cube :=
  let counts := Map.counts (pocket.active.toList.flatMap (.neighbours))
  let near := countsActive pocket.active cube
  calc pocket.cycle.active.contains cube
    _ = (counts.filter pocket.activeNext).contains cube := Map.containsKeySet (counts.filter pocket.activeNext) cube
    _ = (counts.get cube).any (pocket.activeNext cube) := Map.containsFilter counts cube pocket.activeNext
    _ = Spec.activeAfter pocket.active cube :=
      match found: counts.get cube with
        | Some count => activeNextRule (pocket.active.contains cube) count (Spec.activeNeighbours pocket.active cube) near
        | None => noneRule (pocket.active.contains cube) (Spec.activeNeighbours pocket.active cube) near
