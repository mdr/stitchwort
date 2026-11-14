--| The walks of a grid's graph (`stepGraph`, GridGraph.sw) are the paths of
--| `isPath` through the positions that can be entered, and a walk costs the
--| sum of what entering each of its positions costs. With std's
--| `Graph.distancesShortest` or `Graph.breadthFirstShortest`, that makes
--| what the searches find the cheapest paths.

namespace Aoc.Common.Proofs
import Aoc.Common (..)
import Std (Bool, DecEq, Eq, Exists, Graph, List, Nat, Option, Void)

--| Whether a position can be entered...
def canEnter (enter: Position → Option Nat) (position: Position): Bool := (enter position).isSome

--| ...and what entering it costs (0 where it can't be).
def enterCost (enter: Position → Option Nat) (position: Position): Nat := (enter position).getOrElse 0

--| A step of the graph goes to an adjacent position that can be entered,
--| costing what entering it costs...
theorem stepEdgeElim ∀ (enter: Position → Option Nat) (from next: Position) (weight: Nat)
    (edge: (next, weight) ∈ stepEdges enter from):
    adjacent from next = True ∧ enter next = Some weight :=
  Exists.elim
    (List.anyMember _ from.neighbours
      (List.memFilterMapElim
        (other => enter other |> .map (cost => (other, cost)))
        (next, weight)
        from.neighbours
        edge))
    (other both =>
      let (Both isNeighbour made) := both
      match found: enter other with
        | Some cost =>
          let same: (other, cost) = (next, weight) := Option.someInjective made
          rewrite <- Eq.cong Pair.fst same, <- Eq.cong Pair.snd same in
            Both (neighbourAdjacent from other isNeighbour) found)

--| ...and each such step is one of the graph's.
theorem stepEdgeIntro ∀ (enter: Position → Option Nat) (from next: Position) (cost: Nat)
    (near: adjacent from next = True)
    (found: enter next = Some cost):
    (next, cost) ∈ stepEdges enter from :=
  List.memFilterMapIntro
    (other => enter other |> .map (cost => (other, cost)))
    next
    (next, cost)
    from.neighbours
    (adjacentNeighbour from next near)
    (rewrite found in rfl)

--| A walk is a path through the positions it enters, and costs what
--| entering them costs...
theorem walkPath ∀ (enter: Position → Option Nat) (states: List Position)
    (complete: ∀ (position: Position) (cost: Nat) => enter position = Some cost → position ∈ states)
    (start: Position) (path: List (Position, Nat))
    (finish: Position) (walked: (stepGraph enter states complete).Walk start path finish):
    isPath (canEnter enter) start (path.map Pair.fst) finish = True
      ∧ Graph.cost path = (path.map Pair.fst).sumBy (enterCost enter) :=
  match path, walked with
    | [], walked => Both (rewrite walked in DecEq.refl finish) rfl
    | [(next, weight), ..rest], (Both edge later) =>
      let (Both near found) := stepEdgeElim enter start next weight edge
      let (Both restPath restCost) := walkPath enter states complete next rest finish later
      let entered: enterCost enter next = weight := rewrite found in rfl
      Both
        (Both near (Both (rewrite found in rfl) restPath))
        (omega [
          Graph.costCons next weight rest,
          restCost,
          List.sumByCons (rest.map Pair.fst) next (enterCost enter),
          entered
        ])

--| ...and a path is a walk, each step costing what entering its position
--| costs...
theorem pathWalk ∀ (enter: Position → Option Nat) (states: List Position)
    (complete: ∀ (position: Position) (cost: Nat) => enter position = Some cost → position ∈ states)
    (start: Position) (steps: List Position) (finish: Position)
    (path: isPath (canEnter enter) start steps finish = True):
    (stepGraph enter states complete).Walk start (steps.map (next => (next, enterCost enter next))) finish :=
  match steps with
    | [] => path.read
    | [next, ..rest] =>
      let near := path.left
      let rest2 := path.right
      match found: enter next with
        | Some cost =>
          Both (stepEdgeIntro enter start next cost near found) (pathWalk enter states complete next rest finish rest2)

--| ...costing the sum of what entering its positions costs.
theorem pathWalkCost ∀ (enter: Position → Option Nat) (steps: List Position):
    Graph.cost (steps.map (next => (next, enterCost enter next))) = steps.sumBy (enterCost enter) :=
  match steps with
    | [] => rfl
    | [next, ..rest] =>
      omega [
        Graph.costCons next (enterCost enter next) (rest.map (next => (next, enterCost enter next))),
        pathWalkCost enter rest,
        List.sumByCons rest next (enterCost enter)
      ]

--| Where entering any position costs 1, a path through the positions that
--| can be entered costs its number of steps (for `Graph.breadthFirst`).
theorem unitPathCost ∀ (enter: Position → Option Nat)
    (unit: ∀ (position: Position) (cost: Nat) => enter position = Some cost → cost = 1)
    (from: Position) (steps: List Position) (to: Position)
    (path: isPath (canEnter enter) from steps to = True):
    steps.sumBy (enterCost enter) = steps.length :=
  match steps with
    | [] => rfl
    | [next, ..rest] =>
      let one := unitEnterCost enter unit next path.right.left
      let restCost := unitPathCost enter unit next rest to path.right.right
      omega [List.sumByCons rest next (enterCost enter), restCost, one]

--| Entering a position that can be entered costs 1, there.
theorem unitEnterCost ∀ (enter: Position → Option Nat)
    (unit: ∀ (position: Position) (cost: Nat) => enter position = Some cost → cost = 1) (position: Position)
    (entered: canEnter enter position = True):
    enterCost enter position = 1 :=
  match found: enter position with | Some cost => unit position cost found

-- Paths

--| A path through positions allowed by one test is a path by any test that
--| allows them too.
theorem isPathWeaken ∀ (f g: Position → Bool)
    (weaker: ∀ (position: Position) => f position = True → g position = True)
    (from: Position) (steps: List Position) (to: Position)
    (path: isPath f from steps to = True):
    isPath g from steps to = True :=
  match steps with
    | [] => path
    | [next, ..rest] =>
      Both path.left (Both (weaker next path.right.left) (isPathWeaken f g weaker next rest to path.right.right))

--| A path through positions allowed by one test is a path by another that
--| agrees with it.
theorem isPathCong ∀ (f g: Position → Bool)
    (same: ∀ (position: Position) => f position = g position)
    (from: Position) (steps: List Position) (to: Position):
    isPath f from steps to = isPath g from steps to :=
  match steps with
    | [] => rfl
    | [next, ..rest] => rewrite same next, isPathCong f g same next rest to in rfl

--| A path, then another from where it ends.
theorem isPathAppend ∀ (allowed: Position → Bool) (more: List Position) (to from: Position)
    (steps: List Position) (middle: Position)
    (path: isPath allowed from steps middle = True)
    (after: isPath allowed middle more to = True):
    isPath allowed from (steps ++ more) to = True :=
  match steps with
    | [] => rewrite path.read in after
    | [next, ..rest] =>
      Both path.left (Both path.right.left (isPathAppend allowed more to next rest middle path.right.right after))

--| A path from an allowed position ends at one.
theorem isPathEnd ∀ (allowed: Position → Bool) (from: Position) (steps: List Position) (to: Position)
    (start: allowed from = True)
    (path: isPath allowed from steps to = True):
    allowed to = True :=
  match steps with
    | [] => rewrite <- path.read in start
    | [next, ..rest] => isPathEnd allowed next rest to path.right.left path.right.right

--| `count` steps right along row `row`, from column `column`...
def rightSteps (row column: Nat): Nat → List Position
  | Zero => []
  | Succ count => [{ row, column = column + 1 }, ..rightSteps row (column + 1) count]

--| ...and `count` steps down column `column`, from row `row`.
def downSteps (row column: Nat): Nat → List Position
  | Zero => []
  | Succ count => [{ row = row + 1, column }, ..downSteps (row + 1) column count]

--| Steps right through allowed positions are a path...
theorem rightPath ∀ (allowed: Position → Bool) (row column count: Nat)
    (open: ∀ (k: Nat) => column < k → k ≤ column + count → allowed { row, column = k } = True):
    isPath allowed { row, column } (rightSteps row column count) { row, column = column + count } = True :=
  match count with
    | Zero => rewrite Nat.addZero column in DecEq.refl ({ row, column }: Position)
    | Succ count =>
      let later := rightPath allowed row (column + 1) count (k above below => open k (omega) (omega))
      let same: column + 1 + count = column + Succ count := omega
      Both (rightAdjacent row column) (Both (open (column + 1) (omega) (omega)) (rewrite <- same in later))

--| ...and so are steps down.
theorem downPath ∀ (allowed: Position → Bool) (column row count: Nat)
    (open: ∀ (k: Nat) => row < k → k ≤ row + count → allowed { row = k, column } = True):
    isPath allowed { row, column } (downSteps row column count) { row = row + count, column } = True :=
  match count with
    | Zero => rewrite Nat.addZero row in DecEq.refl ({ row, column }: Position)
    | Succ count =>
      let later := downPath allowed column (row + 1) count (k above below => open k (omega) (omega))
      let same: row + 1 + count = row + Succ count := omega
      Both (downAdjacent row column) (Both (open (row + 1) (omega) (omega)) (rewrite <- same in later))

--| Along the top row, then down the last column, of `height` rows and
--| `width` columns.
def route (height width: Nat): List Position := rightSteps 0 0 (width - 1) ++ downSteps 0 (width - 1) (height - 1)

--| If every position within `height` rows and `width` columns is allowed,
--| the route is a path from the top left to the bottom right.
theorem routePath ∀ (allowed: Position → Bool) (height width: Nat)
    (tall: 0 < height)
    (wide: 0 < width)
    (open: ∀ (position: Position) => position.within height width = True → allowed position = True):
    isPath allowed { row = 0, column = 0 } (route height width) { row = height - 1, column = width - 1 } = True :=
  isPathAppend allowed
    (downSteps 0 (width - 1) (height - 1))
    { row = height - 1, column = width - 1 }
    { row = 0, column = 0 }
    (rightSteps 0 0 (width - 1))
    { row = 0, column = width - 1 }
    (rightPath allowed 0 0 (width - 1) (k above below =>
      open { row = 0, column = k } (Both (omega [tall]) (omega [below, wide]))))
    (downPath allowed (width - 1) 0 (height - 1) (k above below =>
      open { row = k, column = width - 1 } (Both (omega [below, tall]) (omega [wide]))))
