--| The program's graph is the puzzle's steps: its safe positions are the
--| spec's (`safeAgrees`), a walk in it is a path of the spec's taking as many
--| steps as it costs (`walkSteps`), and back (`pathSteps`), by the shared
--| grid code's `walkPath` and `pathWalk`. A path with more bytes fallen is
--| one with fewer (`safeFewer`, and `isPathWeaken`).

namespace Aoc.Year2024.Day18.Proofs
import Aoc.Year2024.Day18 (..)
import Aoc.Year2024.Day18.Spec (..)
import Aoc.Common (Position, isPath, positions)
import Aoc.Common.Proofs (canEnter, enterCost, isPathCong, pathWalk, pathWalkCost, stepEdgeElim, unitPathCost, walkPath)
import Std (And, Bool, Eq, Graph, List, Map, Nat, Option, Set, Void)

--| The program's corrupted set holds the bytes fallen.
theorem safeAgrees (size: Nat) (bytes: List Position) (fallen: Nat) (position: Position):
    (MemorySpace.after size bytes fallen).isSafe position = isSafe size (bytes.take fallen) position :=
  rewrite Set.containsFromList position (bytes.take fallen) in
    rewrite List.anyCong (bytes.take fallen) (other => Map.Spec.sameKey position other) (other => other == position)
      (other => Map.Spec.sameKeyDecide position other) in rfl

--| A position can be entered exactly when the spec says it is safe.
theorem canEnterSafe (size: Nat) (bytes: List Position) (fallen: Nat) (position: Position):
    canEnter (MemorySpace.after size bytes fallen).enter position = isSafe size (bytes.take fallen) position :=
  rewrite <- safeAgrees size bytes fallen position in
    match safe: (MemorySpace.after size bytes fallen).isSafe position with
      | True => rfl
      | False => rfl

--| Entering a position costs one step...
theorem enterUnit (memory: MemorySpace) (position: Position) (cost: Nat) (found: memory.enter position = Some cost): cost = 1 :=
  match safe: memory.isSafe position with
    | True => Eq.sym (Option.someInjective found)

--| ...so each edge of the graph costs one.
theorem unitSteps (memory: MemorySpace) (state: Position) (next: Position) (weight: Nat) (edge: (next, weight) ∈ memory.graph.edges state): weight = 1 :=
  enterUnit memory next weight (And.right (stepEdgeElim memory.enter state next weight edge))

--| A walk in the graph is a path of the spec's, its cost its number of
--| steps...
theorem walkSteps (size: Nat) (bytes: List Position) (fallen: Nat) (from: Position) (path: List (Position, Nat)) (to: Position)
    (walked: (MemorySpace.after size bytes fallen).graph.Walk from path to):
    isPath (isSafe size (bytes.take fallen)) from (path.map Pair.fst) to = True ∧ Graph.cost path = (path.map Pair.fst).length :=
  let memory := MemorySpace.after size bytes fallen
  let (Both entering costs) :=
    walkPath memory.enter (positions size size) (position cost found => memory.enterListed position cost found) from path to walked
  Both (rewrite <- isPathCong (canEnter memory.enter) (isSafe size (bytes.take fallen)) (canEnterSafe size bytes fallen) from (path.map Pair.fst) to in entering)
    (Eq.trans costs (unitPathCost memory.enter (enterUnit memory) from (path.map Pair.fst) to entering))

--| ...and a path of the spec's is a walk, costing its number of steps.
theorem pathSteps (size: Nat) (bytes: List Position) (fallen: Nat) (from: Position) (steps: List Position) (to: Position)
    (path: isPath (isSafe size (bytes.take fallen)) from steps to = True):
    (MemorySpace.after size bytes fallen).graph.Walk from (steps.map (next => (next, enterCost (MemorySpace.after size bytes fallen).enter next))) to
      ∧ Graph.cost (steps.map (next => (next, enterCost (MemorySpace.after size bytes fallen).enter next))) = steps.length :=
  let memory := MemorySpace.after size bytes fallen
  let entering: isPath (canEnter memory.enter) from steps to = True :=
    rewrite isPathCong (canEnter memory.enter) (isSafe size (bytes.take fallen)) (canEnterSafe size bytes fallen) from steps to in path
  Both (pathWalk memory.enter (positions size size) (position cost found => memory.enterListed position cost found) from steps to entering)
    (Eq.trans (pathWalkCost memory.enter steps) (unitPathCost memory.enter (enterUnit memory) from steps to entering))

--| A position safe with more bytes fallen is safe with fewer.
theorem safeFewer (size: Nat) (bytes: List Position) (fewer: Nat) (more: Nat) (le: fewer ≤ more) (position: Position)
    (safe: isSafe size (bytes.take more) position = True): isSafe size (bytes.take fewer) position = True :=
  let inside := safe.left
  let clear := safe.right
  match there: (bytes.take fewer).contains position with
    | True =>
      let worse := containsTakeMono position bytes fewer more le there
      rewrite worse at clear in cases
    | False => Both inside rfl
