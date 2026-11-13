--| Any map of risk levels with a position: the program's search finds the
--| spec's lowest total risk from the top left to the bottom right. A walk
--| in the program's graph is a path of the spec's, costing its total risk,
--| and back (`walkPath`, `pathWalk`: the shared grid code's lemmas about
--| its graphs). Std's Dijkstra search (`Graph.distancesShortest`) finds a
--| walk's cost for each position it settles, and no walk costs less. A
--| path to the bottom right exists (along the top row, then down the last
--| column: `Aoc.Common.Proofs.routePath`), so the search settles it.

namespace Aoc.Year2021.Day15.Proofs
import Aoc.Year2021.Day15 (..)
import Aoc.Year2021.Day15.Spec (..)
import Aoc.Common (Position, boxEnter, boxEnterListed, positions)
import Aoc.Common.Proofs (enterCost, pathWalkCost, route, routePath)
import Std (Bool, DecEq, Eq, Exists, Graph, List, Map, Nat, Option, Void)

--| A walk in the graph is a path through its positions, and costs their
--| total risk...
theorem walkPath ∀ (risks: RiskMap) (start: Position) (path: List (Position, Nat)) (finish: Position) (walked: risks.graph.Walk start path finish):
    isPath risks.levelAt start (path.map Pair.fst) finish = True ∧ Graph.cost path = totalRisk risks.levelAt (path.map Pair.fst) :=
  Aoc.Common.Proofs.walkPath (boxEnter risks.height risks.width risks.level) (positions risks.height risks.width)
    (position c found => boxEnterListed risks.height risks.width risks.level position c found) start path finish walked

--| ...and a path is a walk, each step costing the level it enters.
theorem pathWalk ∀ (risks: RiskMap) (start: Position) (steps: List Position) (finish: Position) (path: isPath risks.levelAt start steps finish = True):
    risks.graph.Walk start (steps.map (next => (next, enterCost risks.levelAt next))) finish :=
  Aoc.Common.Proofs.pathWalk (boxEnter risks.height risks.width risks.level) (positions risks.height risks.width)
    (position c found => boxEnterListed risks.height risks.width risks.level position c found) start steps finish path

--| A position on the map has its level.
theorem levelAtOn ∀ (risks: RiskMap) (position: Position) (onMap: (position.row < risks.height && position.column < risks.width) = True):
    risks.levelAt position = Some (risks.level position) :=
  rewrite onMap in rfl

--| A path leads from the top left to the bottom right of a map with a
--| position.
theorem routeOnMap ∀ (risks: RiskMap) (tall: 0 < risks.height) (wide: 0 < risks.width):
    isPath risks.levelAt topLeft (route risks.height risks.width) (bottomRight risks.height risks.width) = True :=
  routePath (position => (risks.levelAt position).isSome) risks.height risks.width tall wide (position inside => rewrite levelAtOn risks position inside in rfl)

--| The program's search finds the lowest total risk from the top left to
--| the bottom right, on any map with a position.
theorem lowestRiskCorrect ∀ (risks: RiskMap) (tall: 0 < risks.height) (wide: 0 < risks.width):
    LowestRisk risks.levelAt (bottomRight risks.height risks.width) risks.lowestRisk :=
  let target := bottomRight risks.height risks.width
  let sources := [(risks.start, 0)]
  let shortest := Graph.distancesShortest risks.graph (index := risks.index) sources
  let routeWalk := pathWalk risks topLeft (route risks.height risks.width) target (routeOnMap risks tall wide)
  Exists.elim (And.right shortest risks.start 0 (Inl rfl) _ target routeWalk) (found both =>
    let got := And.left both
    let answer: risks.lowestRisk = found := rewrite got in rfl
    rewrite answer in Both (cheapestPath risks target found got) (steps path => noCheaperPath risks target found got steps path))

--| The cost the search finds is some path's total risk...
theorem cheapestPath ∀ (risks: RiskMap) (target: Position) (found: Nat) (got: (risks.graph.distances (index := risks.index) [(risks.start, 0)]).get target = Some found):
    ∃ (steps: List Position) => isPath risks.levelAt topLeft steps target = True ∧ totalRisk risks.levelAt steps = found :=
  Exists.elim (And.left (Graph.distancesShortest risks.graph (index := risks.index) [(risks.start, 0)]) target found got) (source rest =>
    Exists.elim rest (start rest2 =>
      Exists.elim rest2 (path parts =>
        let (Both isSource (Both walked costs)) := parts
        match isSource with
          | Inr none => Void.exfalso none
          | Inl same =>
            let fromStart: topLeft = source := Eq.cong Pair.fst same
            let startZero: 0 = start := Eq.cong Pair.snd same
            let (Both stepsPath stepsCost) := walkPath risks source path target walked
            Witness (path.map Pair.fst) (Both (rewrite fromStart in stepsPath) (omega [costs, startZero, stepsCost])))))

--| ...and no path costs less.
theorem noCheaperPath ∀ (risks: RiskMap) (target: Position) (found: Nat) (got: (risks.graph.distances (index := risks.index) [(risks.start, 0)]).get target = Some found)
    (steps: List Position) (path: isPath risks.levelAt topLeft steps target = True): found ≤ totalRisk risks.levelAt steps :=
  let walked := pathWalk risks topLeft steps target path
  Exists.elim (And.right (Graph.distancesShortest risks.graph (index := risks.index) [(risks.start, 0)]) risks.start 0 (Inl rfl) _ target walked) (other both =>
    let (Both gotOther below) := both
    let same: other = found := Option.someInjective (Eq.trans (Eq.sym gotOther) got)
    omega [same, below, pathWalkCost risks.levelAt steps])
