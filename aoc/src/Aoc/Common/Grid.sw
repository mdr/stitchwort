--| Grids, shared between days: positions and the four directions, a step,
--| the four and the eight neighbours of a position, grids as lists of rows
--| (`cells`, `cellAt`, `mapCells` for rows of any lengths; `Grid` with its
--| `width`, `positions` and a fast `lookup`), and a parser whose grids are
--| rectangles. The graph of a grid for std's searches is in GridGraph.sw.
--| Its tests are in `Aoc.Common.Tests` (Tests/Grid.sw); the proofs about it
--| in `Aoc.Common.Proofs` (Proofs/Grid*.sw).
--|
--| Positions are `Nat`s, row then column, counting from the top left: the
--| cells of a grid are rows of a list, so a position is two indices, and a
--| step above row 0 or left of column 0 is `None` rather than a negative
--| index. How far to move, which can be negative, is an `Offset`
--| (Offset.sw).

namespace Aoc.Common
import Std (Array, Bool, Decidable, DecEq, Fail, Fin, List, Nat, Option, Parse, Text)
import Std.Parse (many1)

--| A position on a grid: row 0 is the top row, column 0 the left column.
type Position = { row: Nat, column: Nat }

type Direction = | Up | Right | Down | Left

--| The four directions, clockwise from up.
def directions: List Direction := [Up, Right, Down, Left]

--| A quarter turn clockwise.
def Direction.turnRight: Direction → Direction
  | Up => Right
  | Right => Down
  | Down => Left
  | Left => Up

--| A quarter turn anticlockwise.
def Direction.turnLeft: Direction → Direction
  | Up => Left
  | Left => Down
  | Down => Right
  | Right => Up

--| A half turn.
def Direction.opposite: Direction → Direction
  | Up => Down
  | Right => Left
  | Down => Up
  | Left => Right

--| The position one step in `direction`: none above row 0 or left of
--| column 0. Past the far edges there is no limit here; `Position.within`
--| and `Grid.step` bound it.
def Position.step (position: Position): Direction → Option Position
  | Up =>
    match position.row with
      | Zero => None
      | Succ above => Some { position | row = above }
  | Right => Some { position | column = position.column + 1 }
  | Down => Some { position | row = position.row + 1 }
  | Left =>
    match position.column with
      | Zero => None
      | Succ before => Some { position | column = before }

--| The positions one step up, right, down and left: two to four of them.
def Position.neighbours (position: Position): List Position := directions.filterMap position.step

--| The eight positions around `at`, diagonals included: none above row 0 or
--| left of column 0. Row by row.
def Position.around (at: Position): List Position :=
  List.range (at.row - 1) (at.row + 1 + 1)
    |> .flatMap (row => List.range (at.column - 1) (at.column + 1 + 1) |> .map (column => ({ row, column }: Position)))
    |> .filter (near => not (near.row == at.row && near.column == at.column))

--| How many of the eight positions around `at` pass `keep`: what
--| `at.around.count keep` is (`Aoc.Common.Proofs.countAroundIsAround`), but
--| without building the positions as lists, which cost most of the time of
--| a search that asks it at every cell.
def Position.countAround (at: Position) (keep: Position → Bool): Nat :=
  Nat.sumFrom
    (at.row - 1)
    (row =>
      Nat.sumFrom
        (at.column - 1)
        (column => if row == at.row && column == at.column then 0 else Bool.toNat (keep { row, column }))
        (at.column + 1 + 1 - (at.column - 1)))
    (at.row + 1 + 1 - (at.row - 1))

--| Up, down, left or right of each other: one column apart in the same row,
--| or one row apart in the same column. (What `neighbours` lists: see
--| `Aoc.Common.Proofs.neighbourAdjacent` and `adjacentNeighbour`.)
def adjacent (from to: Position): Bool :=
  (from.row == to.row && (from.column + 1 == to.column || to.column + 1 == from.column))
    || (from.column == to.column && (from.row + 1 == to.row || to.row + 1 == from.row))

--| Next to each other, diagonals included: different positions at most one
--| row and at most one column apart. (What `around` lists.)
def touching (at other: Position): Bool :=
  not (at.row == other.row && at.column == other.column)
    && at.row ≤ other.row + 1
    && other.row ≤ at.row + 1
    && at.column ≤ other.column + 1
    && other.column ≤ at.column + 1

--| Steps from `from` to `to`, the positions entered in turn: each adjacent
--| to the one before, and `allowed`.
def isPath (allowed: Position → Bool) (from: Position): (steps: List Position) → (to: Position) → Bool
  | [], to => from == to
  | [next, ..rest], to => adjacent from next && allowed next && isPath allowed next rest to

--| In the first `height` rows and `width` columns.
def Position.within (position: Position) (height width: Nat): Bool := position.row < height && position.column < width

--| Every position in the first `height` rows and `width` columns, row by
--| row.
def positions (height width: Nat): List Position :=
  List.range 0 height |> .flatMap (row => List.range 0 width |> .map (column => ({ row, column }: Position)))

-- Rows of cells, of any lengths

--| Every cell of `rows` with its position, row by row.
def cells (rows: List (List a)): List (Position, a) :=
  rows.gridCells |> .map (((at, cell)) => (({ row = at.fst, column = at.snd }: Position), cell))

--| The cell at `position`; `None` off the rows.
def cellAt (rows: List (List a)) (position: Position): Option a := match rows.get position.row with
  | Some row => row.get position.column
  | None => None

--| The positions of the cells of `cells` whose tile passes `keep`, in the
--| order of `cells` (`Grid.positionsWhere`, for rows of any lengths).
def positionsWhere (cells: List (Position, a)) (keep: a → Bool): List Position :=
  cells.filterMap (match some | (position, here) if keep here => position)

--| The position of the one cell of `cells` equal to `wanted` (`Grid.findOnly`,
--| for rows of any lengths).
def onlyCell [auto eq: DecEq a] (cells: List (Position, a)) (wanted: a) (what: Text): {Fail} Position :=
  match positionsWhere cells (== wanted) with
    | [position] => position
    | [] => Fail.fail "no ${what}"
    | _ => Fail.fail "more than one ${what}"

--| `f` of every cell and its position, in the same shape.
def mapCells (rows: List (List a)) (f: Position → a → b): List (List b) :=
  rows.mapWithIndex (r row => row.mapWithIndex (c cell => f { row = r, column = c } cell))

-- Rectangular grids

--| The first row's length.
def firstWidth (rows: List (List a)): Nat := rows.headOr [] |> .length

--| A grid, row by row, with a first row that has a cell: the puzzles' grids
--| are never empty, so a width is never 0 (`Grid.widthNonZero`). A
--| rectangle when every row is as long as the first (`Grid.Rectangle`), as
--| `parseGrid`'s grids are. The proof is an equation, so that grids have
--| `==` and the counterexample search can make them. A grid written out as
--| a literal needs it, `{ rows, nonEmpty = … }`; `Grid.of` finds it.
type Grid (a: Type) = { rows: List (List a), nonEmpty: (firstWidth rows == 0) = False }

--| A grid of `rows`, whose first row has a cell.
def Grid.of (rows: List (List a)) [auto nonEmpty: (firstWidth rows == 0) = False]: Grid a := { rows, nonEmpty }

def Grid.height (grid: Grid a): Nat := grid.rows.length

--| The first row's length.
def Grid.width (grid: Grid a): Nat := firstWidth grid.rows

--| A grid has a column, so `column % grid.width` can be written with this
--| in scope: `let nonZero := grid.widthNonZero`.
theorem Grid.widthNonZero ∀ (grid: Grid a): grid.width ≠ 0 := same => grid.nonEmpty.read same

--| Every row is as long as the first.
def Grid.Rectangle (grid: Grid a): Prop := ∀ (row: List a) => row ∈ grid.rows → row.length = grid.width

--| `Rectangle`, as a `Bool` that can be computed and searched
--| (`Aoc.Common.Proofs.isRectangleIff`).
def Grid.isRectangle (grid: Grid a): Bool := grid.rows.all (.length == grid.width)

--| The cell at `position`; `None` off the grid. O(row + column): for many
--| lookups, `lookup`.
def Grid.at (grid: Grid a) (position: Position): Option a := cellAt grid.rows position

--| Every cell with its position, row by row.
def Grid.cells (grid: Grid a): List (Position, a) := cells grid.rows

--| The positions whose tile passes `keep`, row by row.
def Grid.positionsWhere (grid: Grid a) (keep: a → Bool): List Position := positionsWhere grid.cells keep

--| The position of the one cell equal to `wanted`. Fails if there is none
--| or more than one, saying `what` was wanted: `grid.findOnly S "S tile"`
--| fails with "no S tile" or "more than one S tile".
def Grid.findOnly [auto eq: DecEq a] (grid: Grid a) (wanted: a) (what: Text): {Fail} Position :=
  onlyCell grid.cells wanted what

--| Every position of the grid's rectangle, row by row.
def Grid.positions (grid: Grid a): List Position := positions grid.height grid.width

--| On the grid's rectangle.
def Grid.contains (grid: Grid a) (position: Position): Bool := position.within grid.height grid.width

--| The position one step in `direction`, if it is on the grid's rectangle.
def Grid.step (grid: Grid a) (position: Position) (direction: Direction): Option Position :=
  match position.step direction with
    | Some next => if grid.contains next then Some next else None
    | None => None

--| Mapping the cells keeps the first row's length.
theorem mapFirstWidth ∀ (rows: List (List a)) (f: Position → a → b): firstWidth (mapCells rows f) = firstWidth rows :=
  match rows with
    | [] => rfl
    | [first, ..rest] => List.lengthMapWithIndex first (c cell => f { row = 0, column = c } cell)

--| `f` of every cell and its position.
def Grid.map (grid: Grid a) (f: Position → a → b): Grid b :=
  { rows = mapCells grid.rows f, nonEmpty = rewrite mapFirstWidth grid.rows f in grid.nonEmpty }

--| `at`, through a table built once: `let find := grid.lookup` and then
--| `find position` takes O(1) when run, the table an array of rows, each an
--| array of cells. (`lookupAt` says it is `at`.)
def Grid.lookup (grid: Grid a): Position → Option a :=
  let table := grid.rows.map (.toArray) |> .toArray
  position => table.getOr position.row Array.empty |> .get position.column

--| The same with `fallback` off the grid, for the inner loops of searches:
--| no `Option` to take apart. (`lookupOrAt` says it is `at` or
--| `fallback`.)
def Grid.lookupOr (grid: Grid a) (fallback: a): Position → a :=
  let table := grid.rows.map (.toArray) |> .toArray
  position => table.getOr position.row Array.empty |> .getOr position.column fallback

-- Parsing

--| One row per line, each line one or more cells read by `cell`, and every
--| row as long as the first, which has a cell (the puzzle's grids are
--| rectangles). A successful parse is a rectangle (`parseGridRectangle`).
def parseGrid (input: Text) (cell: () → {Parse} a): {Fail} Grid a :=
  checkGrid (Parse.eachLine input (() => many1 cell |> .toList))

--| The grid, if its first row has a cell and every row is as long as the
--| first; otherwise fail, saying why.
def checkGrid (rows: List (List a)): {Fail} Grid a :=
  if empty: firstWidth rows = 0 then Fail.fail "expected a grid, got no cells"
  else
    match firstRagged rows with
      | Some (index, row) =>
        Fail.fail "line ${index + 1}: expected ${firstWidth rows} cells, as on the first line, got ${row.length}"
      | None => { rows, nonEmpty = Decidable.toBoolOfNot (DecEq.decide (firstWidth rows) 0) empty }

--| The first row not as long as the first, with its index.
def firstRagged (rows: List (List a)): Option (Nat, List a) :=
  rows.withIndex.find (((_, row)) => row.length != firstWidth rows)
