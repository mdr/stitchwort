--| A grid as a graph for std's searches (`Graph.breadthFirst`,
--| `Graph.distances`): from each position, a step to each neighbour that
--| can be entered, costing what entering it costs. The proofs that its
--| walks are the paths of `isPath`, costing the sum of what each position
--| entered costs, are in `Aoc.Common.Proofs` (Proofs/GridGraph.sw).

namespace Aoc.Common
import Std (Bool, Eq, Exists, Graph, List, Nat, Option, Void)

--| The graph whose edges step from a position to each neighbour that can
--| be entered, costing `enter next` (`None`: it can't be entered). The
--| search's `states` must list every position that can be entered
--| (`complete`); they are what makes the search end. `Grid.graph` and
--| `boxGraph` give them.
def stepGraph (enter: Position → Option Nat) (states: List Position)
    (complete: ∀ (position: Position) (cost: Nat) => enter position = Some cost → position ∈ states): Graph Position := {
  edges = position => stepEdges enter position,
  states,
  listed = position next weight edge => stepEdgesListed enter states complete position next weight edge
}

--| A step to each neighbour that can be entered, with its cost.
def stepEdges (enter: Position → Option Nat) (position: Position): List (Position, Nat) :=
  position.neighbours.filterMap (next => enter next |> .map (cost => (next, cost)))

--| Each step leads to a position that can be entered, so to one of the
--| states.
theorem stepEdgesListed (enter: Position → Option Nat) (states: List Position)
    (complete: ∀ (position: Position) (cost: Nat) => enter position = Some cost → position ∈ states) (position: Position) (next: Position)
    (weight: Nat) (edge: (next, weight) ∈ stepEdges enter position): next ∈ states :=
  Exists.elim (List.anyMember _ position.neighbours (List.memFilterMapElim (other => enter other |> .map (cost => (other, cost))) (next, weight) position.neighbours edge))
    (other both =>
      match found: enter other with
        | None => Void.exfalso (Option.noneNotSome (next, weight) (And.right both))
        | Some cost =>
          let same: (other, cost) = (next, weight) := Option.someInjective (And.right both)
          rewrite <- Eq.cong Pair.fst same in complete other cost found)

--| Entering a position of the first `height` rows and `width` columns
--| costs `cost` of it; nothing else can be entered.
def boxEnter (height: Nat) (width: Nat) (cost: Position → Nat) (position: Position): Option Nat :=
  if position.within height width then Some (cost position) else None

--| The graph of the first `height` rows and `width` columns, entering each
--| position costing `cost` of it.
def boxGraph (height: Nat) (width: Nat) (cost: Position → Nat): Graph Position :=
  stepGraph (boxEnter height width cost) (positions height width) (position c found => boxEnterListed height width cost position c found)

--| A position that can be entered is one of the box's.
theorem boxEnterListed (height: Nat) (width: Nat) (cost: Position → Nat) (position: Position) (c: Nat)
    (found: boxEnter height width cost position = Some c): position ∈ positions height width :=
  match inside: position.within height width with
    | True => memPositionsOfWithin height width position inside

--| A position within the box is one of its positions.
theorem memPositionsOfWithin (height: Nat) (width: Nat) (position: Position) (inside: position.within height width = True): position ∈ positions height width :=
  match position with
    | { row, column } =>
      let below: row < height := inside.left
      let before: column < width := inside.right
      List.memFlatMapIntro (row => List.range 0 width |> .map (column => ({ row, column }: Position))) row { row, column } (List.range 0 height)
        (List.memRangeFromIntro row height 0 (omega) (omega [below]))
        (List.memMap (List.range 0 width) column (List.memRangeFromIntro column width 0 (omega) (omega [before])) (column => ({ row, column }: Position)))

--| The graph of rows of cells: entering a position costs `enter` of it and
--| its cell (`None`: it can't be entered); off the rows, nothing can be
--| entered. Its `states` are every cell's position, computed when the graph
--| is built: build it once.
def cellsGraph (rows: List (List a)) (enter: Position → a → Option Nat): Graph Position :=
  stepGraph (cellsEnter rows enter) ((cells rows).map Pair.fst) (position c found => cellsEnterListed rows enter position c found)

def Grid.graph (grid: Grid a) (enter: Position → a → Option Nat): Graph Position := cellsGraph grid.rows enter

--| What entering a position of the rows costs.
def cellsEnter (rows: List (List a)) (enter: Position → a → Option Nat) (position: Position): Option Nat :=
  cellAt rows position |> .flatMap (enter position)

--| A position that can be entered has a cell.
theorem cellsEnterListed (rows: List (List a)) (enter: Position → a → Option Nat) (position: Position) (c: Nat)
    (found: cellsEnter rows enter position = Some c): position ∈ (cells rows).map Pair.fst :=
  match at: cellAt rows position with
    | Some x => List.memMap (cells rows) (position, x) (memCellsOfCellAt rows position x at) Pair.fst

--| The cell at a position is one of the cells.
theorem memCellsOfCellAt (rows: List (List a)) (position: Position) (x: a) (found: cellAt rows position = Some x): (position, x) ∈ cells rows :=
  match position with
    | { row, column } =>
      match r: rows.get row with
        | Some cells =>
          let inGrid := (List.memGridCells rows row column x).backward (Witness cells (Both r found))
          List.memMap rows.gridCells ((row, column), x) inGrid (arg => (({ row = arg.fst.fst, column = arg.fst.snd }: Position), arg.snd))

--| Numbers the positions of the first `height` rows and `width` columns row
--| by row, `row * width + column`, so that std's search keeps their costs
--| in an array: `(boxGraph height width cost).distances (index := boxIndex
--| height width) sources`. Positions outside the box have no number.
def boxIndex (height: Nat) (width: Nat): Graph.Index Position := {
  size = height * width,
  number = position => if position.within height width then Some (position.row * width + position.column) else None,
  decode = number => Some { row = number / width, column = number % width },
  below = position number numbered => boxIndexBelow height width position number numbered,
  roundTrip = position number numbered => boxIndexRoundTrip height width position number numbered
}

--| A position within the box is numbered below `height * width`.
theorem boxIndexBelow (height: Nat) (width: Nat) (position: Position) (number: Nat)
    (numbered: (if position.within height width then Some (position.row * width + position.column) else None) = Some number): number < height * width :=
  match position with
    | { row, column } =>
      match inside: ({ row, column }: Position).within height width with
        | True =>
          let below: row < height := inside.left
          let before: column < width := inside.right
          let rows := Nat.leMulRight (row + 1) height width (omega [below])
          let spread: (row + 1) * width = row * width + width := ring
          omega [Option.someInjective numbered, rows, spread, before]

--| Decoding a position's number gives the position back.
theorem boxIndexRoundTrip (height: Nat) (width: Nat) (position: Position) (number: Nat)
    (numbered: (if position.within height width then Some (position.row * width + position.column) else None) = Some number):
    Some ({ row = number / width, column = number % width }: Position) = Some position :=
  match position with
    | { row, column } =>
      match inside: ({ row, column }: Position).within height width with
        | True =>
          let before: column < width := inside.right
          rewrite <- Option.someInjective numbered in
            rewrite Nat.modUnique (row * width + column) width row column before rfl, Nat.mulAddDivSmall row width column before in rfl
