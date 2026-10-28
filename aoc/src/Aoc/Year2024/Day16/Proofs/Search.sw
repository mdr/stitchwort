-- Dijkstra's search, for any graph: what it settles is reached for that
-- cost (`searchSound`), and nothing reaches a state for less
-- (`searchClosed`, from which the maze's proofs follow any path).

namespace Aoc.Year2024.Day16.Proofs
import Aoc.Year2024.Day16 (..)
import Std (And, Bool, DecEq, Decidable, Eq, Exists, Iff, List, Map, Nat, Option, Or, Set, Void)

-- One step of the search: an empty queue ends it...
theorem searchEmpty [auto ord: Ord s] (graph: Graph s) (queue: Set (Nat, s)) (settled: Map s Nat) (found: queue.min = None):
    graph.searchFrom queue settled None found = settled :=
  rewrite Graph.searchFrom.unfold graph queue settled None found in rfl

-- ...a state already settled is dropped...
theorem searchSkip [auto ord: Ord s] (graph: Graph s) (queue: Set (Nat, s)) (settled: Map s Nat) (cost: Nat) (state: s)
    (found: queue.min = Some (cost, state)) (taken: settled.contains state = True):
    graph.searchFrom queue settled (Some (cost, state)) found
      = graph.searchFrom (queue.remove (cost, state)) settled (queue.remove (cost, state)).min rfl :=
  rewrite Graph.searchFrom.unfold graph queue settled (Some (cost, state)) found in
    Decidable.elimEq _ _ _ _ (fresh => Void.exfalso (Bool.falseNotTrue (Eq.trans (Eq.sym fresh) taken))) (other => rfl)

-- ...and one not settled yet is settled, with its neighbours queued.
theorem searchSettle [auto ord: Ord s] (graph: Graph s) (queue: Set (Nat, s)) (settled: Map s Nat) (cost: Nat) (state: s)
    (found: queue.min = Some (cost, state)) (fresh: settled.contains state = False) (within: graph.within state = True):
    graph.searchFrom queue settled (Some (cost, state)) found
      = graph.searchFrom (pushEdges cost (graph.edges state) (queue.remove (cost, state))) (settled.insert state cost)
        (pushEdges cost (graph.edges state) (queue.remove (cost, state))).min rfl :=
  rewrite Graph.searchFrom.unfold graph queue settled (Some (cost, state)) found in
    Decidable.elimEq _ _ _ _ (isFresh => Decidable.elimEq _ _ _ _ (isWithin => rfl) (notWithin => Void.exfalso (notWithin within)))
      (notFresh => Void.exfalso (notFresh fresh))
