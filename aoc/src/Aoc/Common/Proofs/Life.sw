--| A generation of `lifeStep` is the rule applied cell by cell: the count
--| kept for a cell is the number of live cells that neighbour it
--| (`countsActive`), and a cell is alive after the step exactly when the
--| rule says so for that count (`stepActive`), given that the rule kills a
--| cell with no live neighbours, which the counts never mention.

namespace Aoc.Common.Proofs
import Aoc.Common (..)
import Std (Bool, Eq, List, Map, Nat, Option, Ord, Set)

--| The count kept for `cell` is the number of live cells that neighbour it,
--| given that `adjacent a b` is how many times `b` is among `a`'s
--| neighbours (once or not at all).
theorem countsActive ∀ [auto ord: Ord c] (neighbours: c → List c) (adjacent: c → c → Bool)
    (once: ∀ (a b: c) => (neighbours a).count (== b) = Bool.toNat (adjacent a b)) (alive: Set c) (cell: c):
    (lifeCounts neighbours alive).getOr cell 0 = alive.count (other => adjacent other cell) :=
  calc (lifeCounts neighbours alive).getOr cell 0
    _ = (alive.toList.flatMap neighbours).count (== cell) := Map.getOrCounts cell _
    _ = alive.toList.sumBy (other => (neighbours other).count (== cell)) := List.countFlatMap neighbours (== cell) alive.toList
    _ = alive.toList.sumBy (other => Bool.toNat (adjacent other cell)) := List.sumByCong alive.toList _ _ (other => once other cell)
    _ = alive.toList.count (other => adjacent other cell) := Eq.sym (List.countSumBy alive.toList _)
    _ = alive.count (other => adjacent other cell) := Eq.sym (Set.countToList alive _)

theorem ruleOfCount ∀ (rule: Bool → Nat → Bool) (alive: Bool) (count: Nat) (near: Nat) (same: count = near):
    rule alive count = rule alive near :=
  rewrite same in rfl

theorem ruleOfNone ∀ (rule: Bool → Nat → Bool) (alive: Bool) (near: Nat) (none: 0 = near) (dies: ∀ (alive: Bool) => rule alive 0 = False):
    False = rule alive near :=
  rewrite <- none in Eq.sym (dies alive)

--| A cell is alive after the step exactly when the rule says so for its
--| liveness and its number of live neighbours. `dies` is the rule on a cell
--| with no live neighbours, dead or alive: such a cell has no count, so the
--| step leaves it dead.
theorem stepActive ∀ [auto ord: Ord c] (neighbours: c → List c) (adjacent: c → c → Bool)
    (once: ∀ (a b: c) => (neighbours a).count (== b) = Bool.toNat (adjacent a b))
    (rule: Bool → Nat → Bool) (dies: ∀ (alive: Bool) => rule alive 0 = False) (alive: Set c) (cell: c):
    (lifeStep neighbours rule alive).contains cell = rule (alive.contains cell) (alive.count (other => adjacent other cell)) :=
  let counts := lifeCounts neighbours alive
  let near := countsActive neighbours adjacent once alive cell
  calc (lifeStep neighbours rule alive).contains cell
    _ = (counts.filter (cell count => rule (alive.contains cell) count)).contains cell := Map.containsKeySet (counts.filter (cell count => rule (alive.contains cell) count)) cell
    _ = (counts.get cell).any (rule (alive.contains cell)) := Map.containsFilter counts cell (cell count => rule (alive.contains cell) count)
    _ = rule (alive.contains cell) (alive.count (other => adjacent other cell)) :=
      match found: counts.get cell with
        | Some count => ruleOfCount rule (alive.contains cell) count (alive.count (other => adjacent other cell)) near
        | None => ruleOfNone rule (alive.contains cell) (alive.count (other => adjacent other cell)) near dies
