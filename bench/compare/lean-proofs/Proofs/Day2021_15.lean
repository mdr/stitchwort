import Lib

/-! 2021 day 15, ported from aoc/src/Aoc/Year2021/Day15 and the parts of
aoc/src/Aoc/Common (Grid.sw, GridGraph.sw and their Proofs/) it uses.

Std's Dijkstra search and its theorem `Graph.distancesShortest` are not
ported: `Dijkstra` below is that theorem (its result map is a function `Position → Option Nat`
here: the proofs only ever `get` from it), taken as a hypothesis, as Stitchwort's
check takes it from the prebuilt standard library. The parser and its
`parseRectangle` (and so `part1FromInput`, `part2FromInput`) are left out. -/

namespace Day2021_15

-- Aoc.Common: positions and paths

structure Position where
  row : Nat
  column : Nat
  deriving DecidableEq, Ord

inductive Direction | up | right | down | left

def directions : List Direction := [.up, .right, .down, .left]

def Position.step (position : Position) : Direction → Option Position
  | .up =>
    match position.row with
    | 0 => none
    | above + 1 => some { position with row := above }
  | .right => some { position with column := position.column + 1 }
  | .down => some { position with row := position.row + 1 }
  | .left =>
    match position.column with
    | 0 => none
    | before + 1 => some { position with column := before }

def Position.neighbours (position : Position) : List Position := directions.filterMap position.step

def adjacent (from' to : Position) : Bool :=
  (from'.row == to.row && (from'.column + 1 == to.column || to.column + 1 == from'.column))
    || (from'.column == to.column && (from'.row + 1 == to.row || to.row + 1 == from'.row))

def isPath (allowed : Position → Bool) (from' : Position) : List Position → Position → Bool
  | [], to => from' == to
  | next :: rest, to => adjacent from' next && allowed next && isPath allowed next rest to

def Position.within (position : Position) (height width : Nat) : Bool :=
  position.row < height && position.column < width

def positions (height width : Nat) : List Position :=
  (List.range height).flatMap fun row => (List.range width).map fun column => ({ row, column } : Position)

-- Std: graphs and the search's theorem

structure Graph (σ : Type) where
  edges : σ → List (σ × Nat)
  states : List σ
  listed : ∀ (state next : σ) (weight : Nat), (next, weight) ∈ edges state → next ∈ states

def Graph.Walk (graph : Graph σ) (start : σ) : List (σ × Nat) → σ → Prop
  | [], finish => start = finish
  | (next, weight) :: rest, finish => (next, weight) ∈ graph.edges start ∧ graph.Walk next rest finish

def Graph.cost (path : List (σ × Nat)) : Nat := (path.map Prod.snd).sum

theorem Graph.costCons (next : σ) (weight : Nat) (rest : List (σ × Nat)) :
    Graph.cost ((next, weight) :: rest) = weight + Graph.cost rest := by
  simp [Graph.cost]

def Graph.Reached (graph : Graph σ) (sources : List (σ × Nat)) (state : σ) (cost : Nat) : Prop :=
  ∃ source start path, (source, start) ∈ sources ∧ graph.Walk source path state ∧ start + Graph.cost path = cost

def Graph.Bound (settled : σ → Option Nat) (cost : Nat) (state : σ) : Prop :=
  ∃ found, settled state = some found ∧ found ≤ cost

def Graph.Shortest (graph : Graph σ) (sources : List (σ × Nat)) (result : σ → Option Nat) : Prop :=
  (∀ state cost, result state = some cost → graph.Reached sources state cost) ∧
    ∀ source start, (source, start) ∈ sources → ∀ path state, graph.Walk source path state →
      Graph.Bound result (start + Graph.cost path) state

/-- Std's `Graph.distances` and `Graph.distancesShortest`. -/
structure Dijkstra where
  distances : Graph Position → List (Position × Nat) → Position → Option Nat
  shortest : ∀ graph sources, Graph.Shortest graph sources (distances graph sources)

-- Aoc.Common: the grid's graph

def stepEdges (enter : Position → Option Nat) (position : Position) : List (Position × Nat) :=
  position.neighbours.filterMap fun next => (enter next).map fun cost => (next, cost)

theorem stepEdgesListed (enter : Position → Option Nat) (states : List Position)
    (complete : ∀ position cost, enter position = some cost → position ∈ states) (position next : Position)
    (weight : Nat) (edge : (next, weight) ∈ stepEdges enter position) : next ∈ states := by
  obtain ⟨other, _, made⟩ := List.mem_filterMap.mp edge
  cases found : enter other with
  | none => simp [found] at made
  | some cost =>
    simp only [found, Option.map_some, Option.some.injEq, Prod.mk.injEq] at made
    rw [← made.1]; exact complete other cost found

def stepGraph (enter : Position → Option Nat) (states : List Position)
    (complete : ∀ position cost, enter position = some cost → position ∈ states) : Graph Position where
  edges position := stepEdges enter position
  states := states
  listed position next weight edge := stepEdgesListed enter states complete position next weight edge

def boxEnter (height width : Nat) (cost : Position → Nat) (position : Position) : Option Nat :=
  if position.within height width then some (cost position) else none

theorem memPositionsOfWithin (height width : Nat) (position : Position)
    (inside : position.within height width = true) : position ∈ positions height width := by
  obtain ⟨row, column⟩ := position
  simp only [Position.within, Bool.and_eq_true, decide_eq_true_eq] at inside
  simp only [positions, List.mem_flatMap, List.mem_range, List.mem_map]
  exact ⟨row, inside.1, column, inside.2, rfl⟩

theorem boxEnterListed (height width : Nat) (cost : Position → Nat) :
    ∀ (position : Position) (c : Nat), boxEnter height width cost position = some c → position ∈ positions height width := by
  intro position c found
  cases inside : position.within height width
  · simp [boxEnter, inside] at found
  · exact memPositionsOfWithin height width position inside

def boxGraph (height width : Nat) (cost : Position → Nat) : Graph Position :=
  stepGraph (boxEnter height width cost) (positions height width) (boxEnterListed height width cost)

-- Aoc.Common.Proofs: adjacency, walks and paths

theorem rightAdjacent (row column : Nat) : adjacent ⟨row, column⟩ ⟨row, column + 1⟩ = true := by
  simp [adjacent]

theorem downAdjacent (row column : Nat) : adjacent ⟨row, column⟩ ⟨row + 1, column⟩ = true := by
  simp [adjacent]

theorem stepAdjacent : ∀ (position : Position) (direction : Direction) (next : Position),
    position.step direction = some next → adjacent position next = true
  | ⟨0, column⟩, .up, next, stepped => by simp [Position.step] at stepped
  | ⟨row + 1, column⟩, .up, next, stepped => by
    simp only [Position.step, Option.some.injEq] at stepped; rw [← stepped]; simp [adjacent]
  | ⟨row, column⟩, .right, next, stepped => by
    simp only [Position.step, Option.some.injEq] at stepped; rw [← stepped]; exact rightAdjacent row column
  | ⟨row, column⟩, .down, next, stepped => by
    simp only [Position.step, Option.some.injEq] at stepped; rw [← stepped]; exact downAdjacent row column
  | ⟨row, 0⟩, .left, next, stepped => by simp [Position.step] at stepped
  | ⟨row, column + 1⟩, .left, next, stepped => by
    simp only [Position.step, Option.some.injEq] at stepped; rw [← stepped]; simp [adjacent]

theorem adjacentStep (position next : Position) (near : adjacent position next = true) :
    ∃ direction, position.step direction = some next := by
  obtain ⟨r, c⟩ := position
  obtain ⟨r', c'⟩ := next
  simp only [adjacent, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at near
  rcases near with ⟨rfl, h | h⟩ | ⟨rfl, h | h⟩
  · exact ⟨.right, by simp [Position.step, ← h]⟩
  · subst h; exact ⟨.left, by simp [Position.step]⟩
  · exact ⟨.down, by simp [Position.step, ← h]⟩
  · subst h; exact ⟨.up, by simp [Position.step]⟩

theorem memDirections (direction : Direction) : direction ∈ directions := by
  cases direction <;> simp [directions]

theorem memNeighbours (position next : Position) :
    next ∈ position.neighbours ↔ ∃ direction, position.step direction = some next := by
  simp only [Position.neighbours, List.mem_filterMap]
  exact ⟨fun ⟨d, _, h⟩ => ⟨d, h⟩, fun ⟨d, h⟩ => ⟨d, memDirections d, h⟩⟩

theorem neighbourAdjacent (position next : Position) (member : next ∈ position.neighbours) :
    adjacent position next = true :=
  let ⟨direction, found⟩ := (memNeighbours position next).mp member
  stepAdjacent position direction next found

theorem adjacentNeighbour (position next : Position) (near : adjacent position next = true) :
    next ∈ position.neighbours :=
  (memNeighbours position next).mpr (adjacentStep position next near)

def canEnter (enter : Position → Option Nat) (position : Position) : Bool := (enter position).isSome

def enterCost (enter : Position → Option Nat) (position : Position) : Nat := (enter position).getD 0

theorem stepEdgeElim (enter : Position → Option Nat) (from' next : Position) (weight : Nat)
    (edge : (next, weight) ∈ stepEdges enter from') :
    adjacent from' next = true ∧ enter next = some weight := by
  obtain ⟨other, isNeighbour, made⟩ := List.mem_filterMap.mp edge
  cases found : enter other with
  | none => simp [found] at made
  | some cost =>
    simp only [found, Option.map_some, Option.some.injEq, Prod.mk.injEq] at made
    obtain ⟨rfl, rfl⟩ := made
    exact ⟨neighbourAdjacent from' other isNeighbour, found⟩

theorem stepEdgeIntro (enter : Position → Option Nat) (from' next : Position) (cost : Nat)
    (near : adjacent from' next = true) (found : enter next = some cost) :
    (next, cost) ∈ stepEdges enter from' :=
  List.mem_filterMap.mpr ⟨next, adjacentNeighbour from' next near, by simp [found]⟩

theorem walkPath (enter : Position → Option Nat) (states : List Position)
    (complete : ∀ position cost, enter position = some cost → position ∈ states) :
    ∀ (start : Position) (path : List (Position × Nat)) (finish : Position),
      (stepGraph enter states complete).Walk start path finish →
      isPath (canEnter enter) start (path.map Prod.fst) finish = true
        ∧ Graph.cost path = ((path.map Prod.fst).map (enterCost enter)).sum
  | start, [], finish, walked => by
    simp only [Graph.Walk] at walked
    simp [isPath, walked, Graph.cost]
  | start, (next, weight) :: rest, finish, ⟨edge, later⟩ => by
    obtain ⟨near, found⟩ := stepEdgeElim enter start next weight edge
    obtain ⟨restPath, restCost⟩ := walkPath enter states complete next rest finish later
    have entered : enterCost enter next = weight := by simp [enterCost, found]
    refine ⟨?_, ?_⟩
    · simp only [List.map_cons, isPath, near, canEnter, found, Option.isSome_some, Bool.and_true,
        Bool.true_and]
      exact restPath
    · rw [Graph.costCons, restCost]; simp [entered]

theorem pathWalk (enter : Position → Option Nat) (states : List Position)
    (complete : ∀ position cost, enter position = some cost → position ∈ states) :
    ∀ (start : Position) (steps : List Position) (finish : Position),
      isPath (canEnter enter) start steps finish = true →
      (stepGraph enter states complete).Walk start (steps.map fun next => (next, enterCost enter next)) finish
  | start, [], finish, path => by simpa [isPath, Graph.Walk] using path
  | start, next :: rest, finish, path => by
    simp only [isPath, Bool.and_eq_true] at path
    obtain ⟨⟨near, canNext⟩, restPath⟩ := path
    cases found : enter next with
    | none => simp [canEnter, found] at canNext
    | some cost =>
      refine ⟨?_, pathWalk enter states complete next rest finish restPath⟩
      have := stepEdgeIntro enter start next cost near found
      simpa [enterCost, found, stepGraph] using this

theorem pathWalkCost (enter : Position → Option Nat) :
    ∀ steps : List Position, Graph.cost (steps.map fun next => (next, enterCost enter next)) = (steps.map (enterCost enter)).sum
  | [] => rfl
  | next :: rest => by
    rw [List.map_cons, Graph.costCons, pathWalkCost enter rest]; simp

theorem isPathAppend (allowed : Position → Bool) (more : List Position) (to : Position) :
    ∀ (from' : Position) (steps : List Position) (middle : Position),
      isPath allowed from' steps middle = true → isPath allowed middle more to = true →
      isPath allowed from' (steps ++ more) to = true
  | from', [], middle, path, after => by
    simp only [isPath, beq_iff_eq] at path; rw [← path] at after; simpa using after
  | from', next :: rest, middle, path, after => by
    simp only [isPath, Bool.and_eq_true] at path
    simp only [List.cons_append, isPath, Bool.and_eq_true]
    exact ⟨path.1, isPathAppend allowed more to next rest middle path.2 after⟩

def rightSteps (row column : Nat) : Nat → List Position
  | 0 => []
  | count + 1 => ⟨row, column + 1⟩ :: rightSteps row (column + 1) count

def downSteps (row column : Nat) : Nat → List Position
  | 0 => []
  | count + 1 => ⟨row + 1, column⟩ :: downSteps (row + 1) column count

theorem rightPath (allowed : Position → Bool) (row : Nat) : ∀ (column count : Nat),
    (∀ k, column < k → k ≤ column + count → allowed ⟨row, k⟩ = true) →
    isPath allowed ⟨row, column⟩ (rightSteps row column count) ⟨row, column + count⟩ = true
  | column, 0, _ => by simp [isPath, rightSteps]
  | column, count + 1, open' => by
    have later := rightPath allowed row (column + 1) count (fun k above below => open' k (by omega) (by omega))
    have same : column + 1 + count = column + (count + 1) := by omega
    rw [same] at later
    simp only [rightSteps, isPath, Bool.and_eq_true]
    exact ⟨⟨rightAdjacent row column, open' (column + 1) (by omega) (by omega)⟩, later⟩

theorem downPath (allowed : Position → Bool) (column : Nat) : ∀ (row count : Nat),
    (∀ k, row < k → k ≤ row + count → allowed ⟨k, column⟩ = true) →
    isPath allowed ⟨row, column⟩ (downSteps row column count) ⟨row + count, column⟩ = true
  | row, 0, _ => by simp [isPath, downSteps]
  | row, count + 1, open' => by
    have later := downPath allowed column (row + 1) count (fun k above below => open' k (by omega) (by omega))
    have same : row + 1 + count = row + (count + 1) := by omega
    rw [same] at later
    simp only [downSteps, isPath, Bool.and_eq_true]
    exact ⟨⟨downAdjacent row column, open' (row + 1) (by omega) (by omega)⟩, later⟩

def route (height width : Nat) : List Position :=
  rightSteps 0 0 (width - 1) ++ downSteps 0 (width - 1) (height - 1)

theorem routePath (allowed : Position → Bool) (height width : Nat) (tall : 0 < height) (wide : 0 < width)
    (open' : ∀ position : Position, position.within height width = true → allowed position = true) :
    isPath allowed ⟨0, 0⟩ (route height width) ⟨height - 1, width - 1⟩ = true :=
  isPathAppend allowed (downSteps 0 (width - 1) (height - 1)) ⟨height - 1, width - 1⟩ ⟨0, 0⟩
    (rightSteps 0 0 (width - 1)) ⟨0, width - 1⟩
    (by simpa using rightPath allowed 0 0 (width - 1) (fun k above below =>
      open' ⟨0, k⟩ (by simp only [Position.within, Bool.and_eq_true, decide_eq_true_eq]; omega)))
    (by simpa using downPath allowed (width - 1) 0 (height - 1) (fun k above below =>
      open' ⟨k, width - 1⟩ (by simp only [Position.within, Bool.and_eq_true, decide_eq_true_eq]; omega)))

-- Aoc.Common: rows of cells and grids

def cellAt (rows : List (List α)) (position : Position) : Option α :=
  match rows[position.row]? with
  | some row => row[position.column]?
  | none => none

def firstWidth (rows : List (List α)) : Nat := (rows.headD []).length

def mapCells (rows : List (List α)) (f : Position → α → β) : List (List β) :=
  rows.mapIdx fun r row => row.mapIdx fun c cell => f ⟨r, c⟩ cell

structure Grid (α : Type) where
  rows : List (List α)
  nonEmpty : (firstWidth rows == 0) = false

def Grid.height (grid : Grid α) : Nat := grid.rows.length

def Grid.width (grid : Grid α) : Nat := firstWidth grid.rows

def Grid.Rectangle (grid : Grid α) : Prop := ∀ row, row ∈ grid.rows → row.length = grid.width

def Grid.at (grid : Grid α) (position : Position) : Option α := cellAt grid.rows position

def Grid.contains (grid : Grid α) (position : Position) : Bool := position.within grid.height grid.width

theorem mapFirstWidth : ∀ (rows : List (List α)) (f : Position → α → β), firstWidth (mapCells rows f) = firstWidth rows
  | [], _ => rfl
  | first :: rest, f => by
    simp [firstWidth, mapCells, List.mapIdx_cons]

def Grid.map (grid : Grid α) (f : Position → α → β) : Grid β where
  rows := mapCells grid.rows f
  nonEmpty := by rw [mapFirstWidth]; exact grid.nonEmpty

def Grid.lookupOr (grid : Grid α) (fallback : α) : Position → α :=
  let table := (grid.rows.map List.toArray).toArray
  fun position => (table.getD position.row #[]).getD position.column fallback

theorem cellAtMapCells (rows : List (List α)) (f : Position → α → β) (position : Position) :
    cellAt (mapCells rows f) position = (cellAt rows position).map (f position) := by
  obtain ⟨r, c⟩ := position
  simp only [cellAt, mapCells, List.getElem?_mapIdx]
  cases rows[r]? <;> simp [List.getElem?_mapIdx]

theorem lookupOrAt (grid : Grid α) (fallback : α) (position : Position) :
    grid.lookupOr fallback position = ((grid.at position).getD fallback) := by
  simp only [Grid.lookupOr, Grid.at, cellAt]
  cases h : grid.rows[position.row]? <;> simp [h, Array.getD_eq_getD_getElem?]

theorem withinOfAt (grid : Grid α) (rectangle : grid.Rectangle) (position : Position) (x : α)
    (found : grid.at position = some x) : grid.contains position = true := by
  simp only [Grid.at, cellAt] at found
  cases atRow : grid.rows[position.row]? with
  | none => simp [atRow] at found
  | some line =>
    simp only [atRow] at found
    have wide : line.length = grid.width := rectangle line (List.mem_of_getElem? atRow)
    have tall : position.row < grid.rows.length := (List.getElem?_eq_some_iff.mp atRow).1
    have across : position.column < line.length := (List.getElem?_eq_some_iff.mp found).1
    have wide' : position.column < grid.width := wide ▸ across
    simp [Grid.contains, Position.within, Grid.height, tall, wide']

theorem atOfWithin (grid : Grid α) (rectangle : grid.Rectangle) (position : Position)
    (inside : grid.contains position = true) : ∃ x, grid.at position = some x := by
  simp only [Grid.contains, Position.within, Grid.height, Grid.width, Bool.and_eq_true] at inside
  have tall : position.row < grid.rows.length := of_decide_eq_true inside.1
  have inside2 : position.column < grid.width := of_decide_eq_true inside.2
  have ⟨line, atRow⟩ : ∃ line, grid.rows[position.row]? = some line :=
    ⟨_, List.getElem?_eq_getElem tall⟩
  have wide : line.length = grid.width := rectangle line (List.mem_of_getElem? atRow)
  have across : position.column < line.length := by omega
  exact ⟨line[position.column], by simp [Grid.at, cellAt, atRow, List.getElem?_eq_getElem across]⟩

-- The program

structure Cave where
  grid : Grid (Fin 10)

def Cave.height (cave : Cave) : Nat := cave.grid.height

def Cave.width (cave : Cave) : Nat := cave.grid.width

structure RiskMap where
  height : Nat
  width : Nat
  level : Position → Nat

def RiskMap.levelAt (risks : RiskMap) (position : Position) : Option Nat :=
  boxEnter risks.height risks.width risks.level position

def RiskMap.graph (risks : RiskMap) : Graph Position := boxGraph risks.height risks.width risks.level

def RiskMap.start (_risks : RiskMap) : Position := ⟨0, 0⟩

def RiskMap.target (risks : RiskMap) : Position := ⟨risks.height - 1, risks.width - 1⟩

def RiskMap.lowestRisk (D : Dijkstra) (risks : RiskMap) : Nat :=
  (D.distances risks.graph [(risks.start, 0)] risks.target).getD 0

def Cave.levels (cave : Cave) : Position → Nat := (cave.grid.map fun _ digit => digit.val).lookupOr 0

def Cave.risks (cave : Cave) : RiskMap := { height := cave.height, width := cave.width, level := cave.levels }

def wrap (level : Nat) : Nat := if level > 9 then level - 9 else level

def Cave.tiles (cave : Cave) : RiskMap :=
  let find := cave.levels
  let height := cave.height
  let width := cave.width
  { height := 5 * height
    width := 5 * width
    level := fun position =>
      let base := find ⟨position.row % height, position.column % width⟩
      wrap (base + (position.row / height + position.column / width)) }

def Cave.tiled (cave : Cave) : RiskMap :=
  if cave.height != 0 then if cave.width != 0 then cave.tiles else cave.risks else cave.risks

def solvePart1 (D : Dijkstra) (cave : Cave) : Nat := cave.risks.lowestRisk D

def solvePart2 (D : Dijkstra) (cave : Cave) : Nat := cave.tiled.lowestRisk D

-- Spec

def Rectangle (cave : Cave) : Prop :=
  0 < cave.width ∧ ∀ row : List (Fin 10), row ∈ cave.grid.rows → row.length = cave.width

def levelAt (cave : Cave) (position : Position) : Option Nat :=
  match cave.grid.rows[position.row]? with
  | none => none
  | some row => (row[position.column]?).map Fin.val

def topLeft : Position := ⟨0, 0⟩

def bottomRight (height width : Nat) : Position := ⟨height - 1, width - 1⟩

def specIsPath (levels : Position → Option Nat) (from' : Position) (steps : List Position) (to : Position) : Bool :=
  isPath (fun position => (levels position).isSome) from' steps to

def totalRisk (levels : Position → Option Nat) (steps : List Position) : Nat :=
  (steps.map fun position => (levels position).getD 0).sum

def LowestRisk (levels : Position → Option Nat) (target : Position) (answer : Nat) : Prop :=
  (∃ steps, specIsPath levels topLeft steps target = true ∧ totalRisk levels steps = answer)
    ∧ ∀ steps, specIsPath levels topLeft steps target = true → answer ≤ totalRisk levels steps

def Part1Answer (cave : Cave) (answer : Nat) : Prop :=
  LowestRisk (levelAt cave) (bottomRight cave.height cave.width) answer

def raise (level : Nat) : Nat := if level == 9 then 1 else level + 1

def iterate (f : Nat → Nat) : Nat → Nat → Nat
  | 0, x => x
  | n + 1, x => iterate f n (f x)

def tiledLevelAt (cave : Cave) (position : Position) : Option Nat :=
  if cave.height != 0 then
    if cave.width != 0 then
      if position.row < 5 * cave.height && position.column < 5 * cave.width then
        (levelAt cave ⟨position.row % cave.height, position.column % cave.width⟩).map fun level =>
          iterate raise (position.row / cave.height + position.column / cave.width) level
      else none
    else none
  else none

def Part2Answer (cave : Cave) (answer : Nat) : Prop :=
  LowestRisk (tiledLevelAt cave) (bottomRight (5 * cave.height) (5 * cave.width)) answer

-- Proofs/Search.sw

theorem walkPathBox (risks : RiskMap) (start : Position) (path : List (Position × Nat)) (finish : Position)
    (walked : risks.graph.Walk start path finish) :
    specIsPath risks.levelAt start (path.map Prod.fst) finish = true
      ∧ Graph.cost path = totalRisk risks.levelAt (path.map Prod.fst) :=
  walkPath (boxEnter risks.height risks.width risks.level) (positions risks.height risks.width)
    (fun position c found => boxEnterListed risks.height risks.width risks.level position c found)
    start path finish walked

theorem pathWalkBox (risks : RiskMap) (start : Position) (steps : List Position) (finish : Position)
    (path : specIsPath risks.levelAt start steps finish = true) :
    risks.graph.Walk start (steps.map fun next => (next, enterCost risks.levelAt next)) finish :=
  pathWalk (boxEnter risks.height risks.width risks.level) (positions risks.height risks.width)
    (fun position c found => boxEnterListed risks.height risks.width risks.level position c found)
    start steps finish path

theorem levelAtOn (risks : RiskMap) (position : Position)
    (onMap : (position.row < risks.height && position.column < risks.width) = true) :
    risks.levelAt position = some (risks.level position) := by
  have inside : position.within risks.height risks.width = true := onMap
  simp [RiskMap.levelAt, boxEnter, inside]

theorem routeOnMap (risks : RiskMap) (tall : 0 < risks.height) (wide : 0 < risks.width) :
    specIsPath risks.levelAt topLeft (route risks.height risks.width) (bottomRight risks.height risks.width) = true :=
  routePath (fun position => (risks.levelAt position).isSome) risks.height risks.width tall wide
    (fun position inside => by rw [levelAtOn risks position inside]; rfl)

theorem cheapestPath (D : Dijkstra) (risks : RiskMap) (target : Position) (found : Nat)
    (got : D.distances risks.graph [(risks.start, 0)] target = some found) :
    ∃ steps, specIsPath risks.levelAt topLeft steps target = true ∧ totalRisk risks.levelAt steps = found := by
  obtain ⟨source, start, path, isSource, walked, costs⟩ := (D.shortest risks.graph [(risks.start, 0)]).1 target found got
  simp only [List.mem_singleton, Prod.mk.injEq] at isSource
  obtain ⟨fromStart, startZero⟩ := isSource
  obtain ⟨stepsPath, stepsCost⟩ := walkPathBox risks source path target walked
  refine ⟨path.map Prod.fst, ?_, ?_⟩
  · rw [fromStart] at stepsPath; exact stepsPath
  · omega

theorem noCheaperPath (D : Dijkstra) (risks : RiskMap) (target : Position) (found : Nat)
    (got : D.distances risks.graph [(risks.start, 0)] target = some found)
    (steps : List Position) (path : specIsPath risks.levelAt topLeft steps target = true) :
    found ≤ totalRisk risks.levelAt steps := by
  have walked := pathWalkBox risks topLeft steps target path
  obtain ⟨other, gotOther, below⟩ := (D.shortest risks.graph [(risks.start, 0)]).2 risks.start 0
    (List.mem_singleton.mpr rfl) _ target walked
  have same : other = found := Option.some.inj (gotOther.symm.trans got)
  have cost := pathWalkCost risks.levelAt steps
  have : totalRisk risks.levelAt steps = (steps.map (enterCost risks.levelAt)).sum := rfl
  omega

theorem lowestRiskCorrect (D : Dijkstra) (risks : RiskMap) (tall : 0 < risks.height) (wide : 0 < risks.width) :
    LowestRisk risks.levelAt (bottomRight risks.height risks.width) (risks.lowestRisk D) := by
  have shortest := D.shortest risks.graph [(risks.start, 0)]
  have routeWalk := pathWalkBox risks topLeft (route risks.height risks.width)
    (bottomRight risks.height risks.width) (routeOnMap risks tall wide)
  obtain ⟨found, got, _⟩ := shortest.2 risks.start 0 (List.mem_singleton.mpr rfl) _ _ routeWalk
  have answer : risks.lowestRisk D = found := by
    have target : risks.target = bottomRight risks.height risks.width := rfl
    simp only [RiskMap.lowestRisk, target, got]; rfl
  rw [answer]
  exact ⟨cheapestPath D risks _ found got, fun steps path => noCheaperPath D risks _ found got steps path⟩

-- Proofs/Levels.sw

theorem levelAtCell (cave : Cave) (position : Position) :
    levelAt cave position = (cellAt cave.grid.rows position).map Fin.val := by
  simp only [levelAt, cellAt]
  cases cave.grid.rows[position.row]? <;> rfl

theorem levelsAt (cave : Cave) (position : Position) :
    cave.levels position = ((cellAt cave.grid.rows position).map Fin.val).getD 0 := by
  rw [Cave.levels, lookupOrAt]
  show (cellAt (mapCells cave.grid.rows (fun _ digit => digit.val)) position).getD 0 = _
  rw [cellAtMapCells]

theorem levelsAgree (cave : Cave) (rectangle : Rectangle cave) (position : Position) :
    levelAt cave position = cave.risks.levelAt position := by
  rw [levelAtCell]
  cases inside : position.within cave.height cave.width
  · cases found : cellAt cave.grid.rows position with
    | none => simp [RiskMap.levelAt, Cave.risks, boxEnter, inside]
    | some digit =>
      have := withinOfAt cave.grid rectangle.2 position digit found
      simp only [Grid.contains, Cave.height, Cave.width] at this inside
      rw [this] at inside; exact Bool.noConfusion inside
  · obtain ⟨digit, found⟩ := atOfWithin cave.grid rectangle.2 position inside
    have level : cave.levels position = digit.val := by rw [levelsAt]; simp [Grid.at] at found; simp [found]
    simp [Grid.at] at found
    simp [RiskMap.levelAt, Cave.risks, boxEnter, inside, found, level]

theorem wrapSmall (level : Nat) (small : level ≤ 9) : wrap level = level := by
  simp only [wrap]; split <;> omega

theorem wrapLarge (level : Nat) (large : 9 < level) : wrap level = level - 9 := by
  simp only [wrap]; split <;> omega

theorem iterateRaise : ∀ (count level : Nat), level ≤ 9 → level + count ≤ 17 → iterate raise count level = wrap (level + count)
  | 0, level, low, _ => by simp [iterate, wrapSmall level low]
  | count + 1, level, low, sum => by
    simp only [iterate]
    by_cases nine : level = 9
    · subst nine
      have later := iterateRaise count 1 (by omega) (by omega)
      have : raise 9 = 1 := rfl
      rw [this, later, wrapSmall (1 + count) (by omega), wrapLarge (9 + (count + 1)) (by omega)]
      omega
    · have later := iterateRaise count (level + 1) (by omega) (by omega)
      have : raise level = level + 1 := by simp [raise, nine]
      rw [this, later]
      congr 1; omega

theorem noRowsNoWidth : ∀ rows : List (List α), rows.length = 0 → firstWidth rows = 0
  | [], _ => rfl
  | _ :: _, zero => by simp at zero

theorem heightNotZero (cave : Cave) (rectangle : Rectangle cave) : cave.height ≠ 0 := fun zero => by
  have := rectangle.1
  have := noRowsNoWidth cave.grid.rows zero
  simp only [Cave.width, Grid.width] at *
  omega

theorem levelBelow10 (cave : Cave) (position : Position) (level : Nat) (found : levelAt cave position = some level) :
    level < 10 := by
  simp only [levelAt] at found
  cases r : cave.grid.rows[position.row]? with
  | none => simp [r] at found
  | some cells =>
    simp only [r] at found
    cases c : cells[position.column]? with
    | none => simp [c] at found
    | some digit =>
      simp only [c, Option.map_some, Option.some.injEq] at found
      rw [← found]; exact digit.isLt

theorem tiledLevelsAgree (cave : Cave) (rectangle : Rectangle cave) (position : Position) :
    tiledLevelAt cave position = cave.tiled.levelAt position := by
  have wide : cave.width ≠ 0 := by have := rectangle.1; omega
  have tall : cave.height ≠ 0 := heightNotZero cave rectangle
  have tiled : cave.tiled = cave.tiles := by simp [Cave.tiled, tall, wide]
  rw [tiled]
  simp only [tiledLevelAt, bne_iff_ne, ne_eq, tall, wide, not_false_eq_true, ite_true]
  by_cases rowIn : position.row < 5 * cave.height
  · by_cases columnIn : position.column < 5 * cave.width
    · let place : Position := ⟨position.row % cave.height, position.column % cave.width⟩
      have found : levelAt cave place = some (cave.levels place) := by
        rw [levelsAgree cave rectangle place]
        exact levelAtOn cave.risks place (by
          have h1 := Nat.mod_lt position.row (Nat.pos_of_ne_zero tall)
          have h2 := Nat.mod_lt position.column (Nat.pos_of_ne_zero wide)
          show (decide (_ < cave.height) && decide (_ < cave.width)) = true
          simp only [Bool.and_eq_true, decide_eq_true_eq]; exact ⟨h1, h2⟩)
      have tileRow : position.row / cave.height ≤ 4 := by
        have : position.row < cave.height * 5 := by rw [Nat.mul_comm]; exact rowIn
        have := Nat.div_lt_of_lt_mul this; omega
      have tileColumn : position.column / cave.width ≤ 4 := by
        have : position.column < cave.width * 5 := by rw [Nat.mul_comm]; exact columnIn
        have := Nat.div_lt_of_lt_mul this; omega
      have below := levelBelow10 cave place _ found
      have raised := iterateRaise (position.row / cave.height + position.column / cave.width) (cave.levels place)
        (by omega) (by omega)
      have rowIn' : position.row < cave.tiles.height := rowIn
      have columnIn' : position.column < cave.tiles.width := columnIn
      simp only [RiskMap.levelAt, boxEnter, Position.within, rowIn, columnIn, rowIn', columnIn',
        decide_true, Bool.and_self, ite_true]
      rw [found]
      simp only [Option.map_some]
      exact congrArg some raised
    · have : ¬ position.column < cave.tiles.width := columnIn
      simp [RiskMap.levelAt, boxEnter, Position.within, columnIn, this]
  · have : ¬ position.row < cave.tiles.height := rowIn
    simp [RiskMap.levelAt, boxEnter, Position.within, rowIn, this]

-- Proofs/Answers.sw

theorem part1Correct (D : Dijkstra) (cave : Cave) (rectangle : Rectangle cave) : Part1Answer cave (solvePart1 D cave) := by
  have same : levelAt cave = cave.risks.levelAt := funext (levelsAgree cave rectangle)
  have found := lowestRiskCorrect D cave.risks (Nat.pos_of_ne_zero (heightNotZero cave rectangle)) rectangle.1
  rw [Part1Answer, same]
  exact found

theorem tiledSize (cave : Cave) (rectangle : Rectangle cave) :
    cave.tiled.height = 5 * cave.height ∧ cave.tiled.width = 5 * cave.width := by
  have wide : cave.width ≠ 0 := by have := rectangle.1; omega
  have tall : cave.height ≠ 0 := heightNotZero cave rectangle
  simp [Cave.tiled, tall, wide, Cave.tiles]

theorem part2Correct (D : Dijkstra) (cave : Cave) (rectangle : Rectangle cave) : Part2Answer cave (solvePart2 D cave) := by
  have same : tiledLevelAt cave = cave.tiled.levelAt := funext (tiledLevelsAgree cave rectangle)
  obtain ⟨height, width⟩ := tiledSize cave rectangle
  have tall := heightNotZero cave rectangle
  have found := lowestRiskCorrect D cave.tiled (by omega) (by have := rectangle.1; omega)
  rw [Part2Answer, same]
  unfold bottomRight
  rw [← height, ← width]
  exact found

end Day2021_15
