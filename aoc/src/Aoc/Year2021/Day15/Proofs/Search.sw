-- Any map of risk levels with a position: the program's search finds the
-- spec's lowest total risk from the top left to the bottom right. A walk
-- in the program's graph is a path of the spec's, costing its total risk,
-- and back (`walkPath`, `pathWalk`). Std's Dijkstra search
-- (`Graph.distancesShortest`) finds a walk's cost for each position it
-- settles, and no walk costs less. A path to the bottom right exists (along
-- the top row, then down the last column), so the search settles it.

namespace Aoc.Year2021.Day15.Proofs
import Aoc.Year2021.Day15 (..)
import Aoc.Year2021.Day15.Spec (..)
import Aoc.Year2021.Day09 (Position)
import Aoc.Year2021.Day09.Spec (adjacent)
import Aoc.Year2021.Day09.Proofs (adjacentNeighbour, neighbourAdjacent, rightAdjacent, downAdjacent)
import Std (Bool, DecEq, Eq, Exists, Graph, List, Map, Nat, Option, Void)

-- A level, or 0 off the map.
def levelOr (levels: Position → Option Nat) (position: Position): Nat := (levels position).getOrElse 0

theorem totalRiskCons (levels: Position → Option Nat) (next: Position) (rest: List Position):
    totalRisk levels (Cons next rest) = levelOr levels next + totalRisk levels rest :=
  List.sumByCons rest next (position => (levels position).getOrElse 0)

-- A step of the graph goes to an adjacent position on the map, costing its
-- level.
theorem edgeStep (risks: RiskMap) (from: Position) (next: Position) (weight: Nat) (edge: (next, weight) ∈ risks.edges from):
    adjacent from next = True ∧ risks.levelAt next = Some weight :=
  Exists.elim
    (List.anyMember _ from.neighbours
      (List.memFilterMapElim (other => risks.levelAt other |> .map (level => (other, level))) (next, weight) from.neighbours edge))
    (other both =>
      let (Both isNeighbour made) := both
      match found: risks.levelAt other with
        | None => Void.exfalso (Option.noneNotSome (next, weight) made)
        | Some level =>
          let same: (other, level) = (next, weight) := Option.someInjective _ _ made
          let sameNext: other = next := Eq.cong Pair.fst same
          let sameLevel: level = weight := Eq.cong Pair.snd same
          rewrite <- sameNext, <- sameLevel in Both (neighbourAdjacent from other isNeighbour) found)

-- A step to an adjacent position on the map is a step of the graph.
theorem stepEdge (risks: RiskMap) (from: Position) (next: Position) (level: Nat) (near: adjacent from next = True) (found: risks.levelAt next = Some level):
    (next, level) ∈ risks.edges from :=
  List.memFilterMapIntro (other => risks.levelAt other |> .map (level => (other, level))) next (next, level) from.neighbours
    (adjacentNeighbour from next near) (rewrite found in rfl)

-- A walk in the graph is a path through its positions, and costs their
-- total risk...
theorem walkPath (risks: RiskMap): (start: Position) → (path: List (Position, Nat)) → (finish: Position) → risks.graph.Walk start path finish →
    isPath risks.levelAt start (path.map Pair.fst) finish = True ∧ Graph.cost path = totalRisk risks.levelAt (path.map Pair.fst)
  | start, Nil, finish, walked => Both (rewrite walked in DecEq.refl finish) rfl
  | start, Cons (next, weight) rest, finish, (Both edge later) =>
    let (Both near found) := edgeStep risks start next weight edge
    let (Both restPath restCost) := walkPath risks next rest finish later
    let entered: levelOr risks.levelAt next = weight := rewrite found in rfl
    Both (Bool.andIntro _ _ near (Bool.andIntro _ _ (rewrite found in rfl) restPath))
      (omega [Graph.costCons next weight rest, restCost, totalRiskCons risks.levelAt next (rest.map Pair.fst), entered])

-- ...and a path is a walk, each step costing the level it enters...
theorem pathWalk (risks: RiskMap): (start: Position) → (steps: List Position) → (finish: Position) → isPath risks.levelAt start steps finish = True →
    risks.graph.Walk start (steps.map (next => (next, levelOr risks.levelAt next))) finish
  | start, Nil, finish, path => DecEq.sound start finish path
  | start, Cons next rest, finish, path =>
    let near := Bool.andLeft _ _ path
    let rest2 := Bool.andRight _ _ path
    match found: risks.levelAt next with
      | None => Void.exfalso (Bool.falseNotTrue rest2)
      | Some level =>
        Both (stepEdge risks start next level near found)
          (pathWalk risks next rest finish rest2)

-- ...costing the path's total risk.
theorem pathWalkCost (levels: Position → Option Nat):
    (steps: List Position) → Graph.cost (steps.map (next => (next, levelOr levels next))) = totalRisk levels steps
  | Nil => rfl
  | Cons next rest =>
    omega [
      Graph.costCons next (levelOr levels next) (rest.map (next => (next, levelOr levels next))),
      pathWalkCost levels rest,
      totalRiskCons levels next rest
    ]

-- A position on the map has its level.
theorem levelAtOn (risks: RiskMap) (position: Position) (onMap: (position.row < risks.height && position.column < risks.width) = True):
    risks.levelAt position = Some (risks.level position) :=
  rewrite onMap in rfl

-- A path, then another from where it ends.
theorem isPathAppend (levels: Position → Option Nat) (more: List Position) (to: Position):
    (from: Position) → (steps: List Position) → (middle: Position) → isPath levels from steps middle = True → isPath levels middle more to = True →
      isPath levels from (steps ++ more) to = True
  | from, Nil, middle, path, after => rewrite DecEq.sound from middle path in after
  | from, Cons next rest, middle, path, after =>
    Bool.andIntro _ _ (Bool.andLeft _ _ path)
      (Bool.andIntro _ _ (Bool.andLeft _ _ (Bool.andRight _ _ path))
        (isPathAppend levels more to next rest middle (Bool.andRight _ _ (Bool.andRight _ _ path)) after))

-- `count` steps right along row `row`, from column `column`...
def rightSteps (row: Nat) (column: Nat): Nat → List Position
  | Zero => Nil
  | Succ count => Cons ({ row, column = column + 1 }) (rightSteps row (column + 1) count)

-- ...and `count` steps down column `column`, from row `row`.
def downSteps (row: Nat) (column: Nat): Nat → List Position
  | Zero => Nil
  | Succ count => Cons ({ row = row + 1, column }) (downSteps (row + 1) column count)

-- Steps right on the map are a path...
theorem rightPath (risks: RiskMap) (row: Nat) (below: row < risks.height): (column: Nat) → (count: Nat) → column + count < risks.width →
    isPath risks.levelAt { row, column } (rightSteps row column count) { row, column = column + count } = True
  | column, Zero, inside => rewrite Nat.addZero column in DecEq.refl ({ row, column }: Position)
  | column, Succ count, inside =>
    let onMap: (row < risks.height && column + 1 < risks.width) = True := Bool.andIntro _ _ below (omega [inside])
    let later := rightPath risks row below (column + 1) count (omega [inside])
    let same: column + 1 + count = column + Succ count := omega
    Bool.andIntro _ _ (rightAdjacent row column)
      (Bool.andIntro _ _ (rewrite levelAtOn risks { row, column = column + 1 } onMap in rfl) (rewrite <- same in later))

-- ...and so are steps down.
theorem downPath (risks: RiskMap) (column: Nat) (before: column < risks.width): (row: Nat) → (count: Nat) → row + count < risks.height →
    isPath risks.levelAt { row, column } (downSteps row column count) { row = row + count, column } = True
  | row, Zero, inside => rewrite Nat.addZero row in DecEq.refl ({ row, column }: Position)
  | row, Succ count, inside =>
    let onMap: (row + 1 < risks.height && column < risks.width) = True := Bool.andIntro _ _ (omega [inside]) before
    let later := downPath risks column before (row + 1) count (omega [inside])
    let same: row + 1 + count = row + Succ count := omega
    Bool.andIntro _ _ (downAdjacent row column)
      (Bool.andIntro _ _ (rewrite levelAtOn risks { row = row + 1, column } onMap in rfl) (rewrite <- same in later))

-- Along the top row, then down the last column.
def route (height: Nat) (width: Nat): List Position := rightSteps 0 0 (width - 1) ++ downSteps 0 (width - 1) (height - 1)

-- A path leads from the top left to the bottom right of a map with a
-- position.
theorem routePath (risks: RiskMap) (tall: 0 < risks.height) (wide: 0 < risks.width):
    isPath risks.levelAt topLeft (route risks.height risks.width) (bottomRight risks.height risks.width) = True :=
  isPathAppend risks.levelAt (downSteps 0 (risks.width - 1) (risks.height - 1)) (bottomRight risks.height risks.width) topLeft
    (rightSteps 0 0 (risks.width - 1)) { row = 0, column = risks.width - 1 } (rightPath risks 0 tall 0 (risks.width - 1) (omega))
    (downPath risks (risks.width - 1) (omega) 0 (risks.height - 1) (omega))

-- The program's search finds the lowest total risk from the top left to
-- the bottom right, on any map with a position.
theorem lowestRiskCorrect (risks: RiskMap) (tall: 0 < risks.height) (wide: 0 < risks.width):
    LowestRisk risks.levelAt (bottomRight risks.height risks.width) risks.lowestRisk :=
  let target := bottomRight risks.height risks.width
  let sources := [(risks.start, 0)]
  let shortest := Graph.distancesShortest risks.graph sources
  let routeWalk := pathWalk risks topLeft (route risks.height risks.width) target (routePath risks tall wide)
  Exists.elim (And.right shortest risks.start 0 (Inl rfl) _ target routeWalk) (found both =>
    let got := And.left both
    let answer: risks.lowestRisk = found := rewrite got in rfl
    rewrite answer in Both (cheapestPath risks target found got) (steps path => noCheaperPath risks target found got steps path))

-- The cost the search finds is some path's total risk...
theorem cheapestPath (risks: RiskMap) (target: Position) (found: Nat) (got: (risks.graph.distances [(risks.start, 0)]).get target = Some found):
    ∃ (steps: List Position) => isPath risks.levelAt topLeft steps target = True ∧ totalRisk risks.levelAt steps = found :=
  Exists.elim (And.left (Graph.distancesShortest risks.graph [(risks.start, 0)]) target found got) (source rest =>
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

-- ...and no path costs less.
theorem noCheaperPath (risks: RiskMap) (target: Position) (found: Nat) (got: (risks.graph.distances [(risks.start, 0)]).get target = Some found)
    (steps: List Position) (path: isPath risks.levelAt topLeft steps target = True): found ≤ totalRisk risks.levelAt steps :=
  let walked := pathWalk risks topLeft steps target path
  Exists.elim (And.right (Graph.distancesShortest risks.graph [(risks.start, 0)]) risks.start 0 (Inl rfl) _ target walked) (other both =>
    let (Both gotOther below) := both
    let same: other = found := Option.someInjective _ _ (Eq.trans (Eq.sym gotOther) got)
    omega [same, below, pathWalkCost risks.levelAt steps])
