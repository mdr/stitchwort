--| Facts about rows of cells and grids: a cell of `cells` is the cell at
--| its position, `mapCells` maps each cell where it is, no position is a
--| cell twice; a rectangle's cells are exactly at the positions within it,
--| `lookup` is `at`, and a grid's step stays on it.

namespace Aoc.Common.Proofs
import Aoc.Common (..)
import Std (Array, Bool, DecEq, Eq, Exists, Fin, Iff, List, Nat, Option, Void)

-- Rows of cells

--| The cell at a position, taken apart: its row, and the cell in it.
theorem cellAtElim (rows: List (List a)) (position: Position) (x: a) (found: cellAt rows position = Some x):
    ∃ (cells: List a) => rows.get position.row = Some cells ∧ cells.get position.column = Some x :=
  match e: List.get rows position.row with
    | Some row => Witness row (Both rfl found)

--| A cell of `cells` is the cell at its position...
theorem cellAtOfMemCells (rows: List (List a)) (position: Position) (x: a) (member: (position, x) ∈ cells rows): cellAt rows position = Some x :=
  Exists.elim (List.memMapElim (arg => (({ row = arg.fst.fst, column = arg.fst.snd }: Position), arg.snd)) (position, x) rows.gridCells member)
    (entry both =>
      match entry with
        | ((row, column), cell) =>
          let (Both inGrid same) := both
          let samePosition: ({ row, column }: Position) = position := Eq.cong Pair.fst same
          let sameCell: cell = x := Eq.cong Pair.snd same
          Exists.elim ((List.memGridCells rows row column cell).forward inGrid) (line found =>
            let (Both atRow atColumn) := found
            rewrite <- samePosition, <- sameCell in rewrite atRow in atColumn))

--| ...and the other way round.
theorem memCells (rows: List (List a)) (position: Position) (x: a): ((position, x) ∈ cells rows) ↔ (cellAt rows position = Some x) := {
  forward = member => cellAtOfMemCells rows position x member,
  backward = found => memCellsOfCellAt rows position x found
}

--| The cell at a position after `mapCells` is `f` of the cell there before.
theorem cellAtMapCells (rows: List (List a)) (f: Position → a → b) (position: Position):
    cellAt (mapCells rows f) position = Option.map (cellAt rows position) (f position) := match position with
      | { row = r, column = c } =>
        rewrite List.getMapWithIndex rows (r row => row.mapWithIndex (c cell => f { row = r, column = c } cell)) r in
          match List.get rows r with
            | None => rfl
            | Some row => List.getMapWithIndex row (c cell => f { row = r, column = c } cell) c

--| `mapCells` of functions equal at every cell.
theorem mapCellsCong (rows: List (List a)) (g1: Position → a → b) (g2: Position → a → b)
    (same: ∀ (position: Position) (x: a) => g1 position x = g2 position x): mapCells rows g1 = mapCells rows g2 :=
  List.mapCong (List.withIndex rows) (p => List.mapWithIndex p.snd (c cell => g1 { row = p.fst, column = c } cell))
    (p => List.mapWithIndex p.snd (c cell => g2 { row = p.fst, column = c } cell))
    (p =>
      List.mapCong (List.withIndex p.snd) (q => g1 { row = p.fst, column = q.fst } q.snd) (q => g2 { row = p.fst, column = q.fst } q.snd)
        (q => same { row = p.fst, column = q.fst } q.snd))

--| The cells after `mapCells` are the cells before, each mapped.
theorem cellsMapCells (rows: List (List a)) (f: Position → a → b): cells (mapCells rows f) = (cells rows).map (((at, x)) => (at, f at x)) :=
  let toCell := (arg: ((Nat, Nat), b)) => (({ row = arg.fst.fst, column = arg.fst.snd }: Position), arg.snd)
  let toCellBefore := (arg: ((Nat, Nat), a)) => (({ row = arg.fst.fst, column = arg.fst.snd }: Position), arg.snd)
  rewrite gridCellsMapCells rows f,
    List.mapMap rows.gridCells toCell (((at, x)) => (at, f { row = at.fst, column = at.snd } x)),
    List.mapMap rows.gridCells (((at, x)) => (at, f at x)) toCellBefore in rfl

--| The grid cells after `mapCells`.
theorem gridCellsMapCells (rows: List (List a)) (f: Position → a → b):
    (mapCells rows f).gridCells = rows.gridCells.map (((at, x)) => (at, f { row = at.fst, column = at.snd } x)) :=
  calc (mapCells rows f).gridCells
    _ = List.concat (List.map (List.withIndex (mapCells rows f)) (p => rowCells p.fst p.snd))
      := List.flatMapEqConcatMap (p => rowCells p.fst p.snd) (List.withIndex (mapCells rows f))
    _ = List.concat (List.map (List.withIndex rows) (p => rowCells p.fst (List.mapWithIndex p.snd (c cell => f { row = p.fst, column = c } cell))))
      := rewrite List.withIndexFromMap 0 rows (p => List.mapWithIndex p.snd (c cell => f { row = p.fst, column = c } cell)),
        List.mapMap (List.withIndex rows) (q => rowCells q.fst q.snd) (p => (p.fst, List.mapWithIndex p.snd (c cell => f { row = p.fst, column = c } cell)))
    _ = List.concat (List.map (List.withIndex rows) (p => List.map (rowCells p.fst p.snd) (((at, x)) => (at, f { row = at.fst, column = at.snd } x))))
      := Eq.cong List.concat (List.mapCong (List.withIndex rows) _ _ (p => rowCellsMapWithIndex p.fst p.snd f))
    _ = rows.gridCells.map (((at, x)) => (at, f { row = at.fst, column = at.snd } x))
      := Eq.sym (rewrite List.flatMapEqConcatMap (p => rowCells p.fst p.snd) (List.withIndex rows),
        List.mapConcat (List.map (List.withIndex rows) (p => rowCells p.fst p.snd)) (((at, x)) => (at, f { row = at.fst, column = at.snd } x)),
        List.mapMap (List.withIndex rows) (xs => List.map xs (((at, x)) => (at, f { row = at.fst, column = at.snd } x))) (p => rowCells p.fst p.snd) in rfl)

--| Row r's cells, as `gridCells` makes them.
def rowCells (r: Nat) (row: List a): List ((Nat, Nat), a) := row.withIndex |> .map (((c, cell)) => ((r, c), cell))

--| Row r's cells after `mapCells`.
theorem rowCellsMapWithIndex (r: Nat) (row: List a) (f: Position → a → b):
    rowCells r (row.mapWithIndex (c cell => f { row = r, column = c } cell))
      = List.map (rowCells r row) (((at, x)) => (at, f { row = at.fst, column = at.snd } x)) :=
  rewrite List.withIndexFromMap 0 row (q => f { row = r, column = q.fst } q.snd),
    List.mapMap (List.withIndex row) (((c, cell)) => ((r, c), cell)) (q => (q.fst, f { row = r, column = q.fst } q.snd)),
    List.mapMap (List.withIndex row) (((at, x)) => (at, f { row = at.fst, column = at.snd } x)) (((c, cell)) => ((r, c), cell)) in rfl

--| No position is a cell twice.
theorem cellPositionsDistinct (rows: List (List a)): List.Distinct ((cells rows).map Pair.fst) :=
  rewrite List.mapMap rows.gridCells Pair.fst (arg => (({ row = arg.fst.fst, column = arg.fst.snd }: Position), arg.snd)),
    <- List.mapMap rows.gridCells (at => ({ row = at.fst, column = at.snd }: Position)) Pair.fst in
    List.distinctMap (rows.gridCells.map Pair.fst) (gridPositionsDistinct rows) (at => ({ row = at.fst, column = at.snd }: Position))
      (x y same => pairExt x y (Eq.cong Position.row same) (Eq.cong Position.column same))

--| Pairs with equal parts are equal.
theorem pairExt (x y: (Nat, Nat)) (first: x.fst = y.fst) (second: x.snd = y.snd): x = y := match x, y with
  | (a, b), (c, d) => rewrite first, second in rfl

--| No position is in `gridCells` twice.
theorem gridPositionsDistinct (rows: List (List a)): List.Distinct (rows.gridCells.map Pair.fst) :=
  rewrite List.flatMapEqConcatMap (p => rowCells p.fst p.snd) (List.withIndex rows) in rowsDistinct 0 rows

--| The positions of the cells of rows s, s + 1, …: no repeats.
theorem rowsDistinct (s: Nat) (rows: List (List a)):
    List.Distinct (List.map (List.concat (List.map (List.withIndexFrom s rows) (p => rowCells p.fst p.snd))) Pair.fst) :=
  match rows with
    | [] => Trivial
    | [row, ..rest] =>
      let later := List.concat (List.map (List.withIndexFrom (Succ s) rest) (p => rowCells p.fst p.snd))
      rewrite List.mapAppend (rowCells s row) later Pair.fst in
        List.distinctAppend (List.map (rowCells s row) Pair.fst) (List.map later Pair.fst)
          (rewrite List.mapMap (List.withIndex row) Pair.fst (((c, cell)) => ((s, c), cell)) in List.distinctWithIndexFromPaired s 0 row)
          (rowsDistinct (Succ s) rest)
          (List.allOfMem (q => q ∉ List.map later Pair.fst) (List.map (rowCells s row) Pair.fst) (q inRow inLater =>
            Exists.elim (List.memMapElim Pair.fst q (rowCells s row) inRow) (cell both =>
              let atRow: s = q.fst := rewrite <- And.right both in Eq.sym (rowCellsRow s row cell (And.left both))
              let below := rowsAbove (Succ s) rest q inLater
              omega)))

--| Row r's cells are in row r.
theorem rowCellsRow (r: Nat) (row: List a) (cell: ((Nat, Nat), a)) (member: cell ∈ rowCells r row): cell.fst.fst = r :=
  Exists.elim (List.memMapElim (((c, x)) => ((r, c), x)) cell (List.withIndex row) member) (p both =>
    rewrite <- And.right both in rfl)

--| The cells of rows s, s + 1, … are in row s or below.
theorem rowsAbove (s: Nat) (rows: List (List a)) (q: (Nat, Nat))
    (member: q ∈ List.map (List.concat (List.map (List.withIndexFrom s rows) (p => rowCells p.fst p.snd))) Pair.fst): s ≤ q.fst :=
  Exists.elim (List.memMapElim Pair.fst q _ member) (cell both =>
    List.anyElim (p => cell ∈ rowCells p.fst p.snd) (s ≤ q.fst) (List.withIndexFrom s rows)
      (List.memFlatMapElim (p => rowCells p.fst p.snd) cell (List.withIndexFrom s rows)
        (rewrite List.flatMapEqConcatMap (p => rowCells p.fst p.snd) (List.withIndexFrom s rows) in And.left both))
      (p inRows inRow =>
        let above := List.memWithIndexFromLe s rows p inRows
        let atRow := rowCellsRow p.fst p.snd cell inRow
        let same: cell.fst = q := And.right both
        rewrite <- same in omega))

-- Positions within a rectangle

--| The positions within `height` rows and `width` columns are exactly
--| `positions height width`.
theorem memPositions (height: Nat) (width: Nat) (position: Position): (position ∈ positions height width) ↔ (position.within height width = True) := {
  forward = member => withinOfMemPositions height width position member,
  backward = inside => memPositionsOfWithin height width position inside
}

theorem withinOfMemPositions (height: Nat) (width: Nat) (position: Position) (member: position ∈ positions height width): position.within height width = True :=
  List.anyElim (row => position ∈ List.map (List.range 0 width) (column => ({ row, column }: Position))) (position.within height width = True)
    (List.range 0 height) (List.memFlatMapElim (row => List.map (List.range 0 width) (column => ({ row, column }: Position))) position (List.range 0 height) member)
    (row inRows inRow =>
      Exists.elim (List.memMapElim (column => ({ row, column }: Position)) position (List.range 0 width) inRow) (column both =>
        let (Both inColumns same) := both
        let (Both _ below) := List.memRangeFrom row height 0 inRows
        let (Both _ before) := List.memRangeFrom column width 0 inColumns
        rewrite <- same in Both (omega [below]) (omega [before])))

-- Grids

--| On a rectangle, a position has a cell exactly when it is within it...
theorem withinOfAt (grid: Grid a) (rectangle: grid.Rectangle) (position: Position) (x: a) (found: grid.at position = Some x):
    grid.contains position = True :=
  Exists.elim (cellAtElim grid.rows position x found) (line both =>
    let (Both atRow atColumn) := both
    let wide: line.length = grid.width := rectangle line (List.memOfGet grid.rows position.row line atRow)
    let tall := (List.getInRange grid.rows position.row).backward (rewrite atRow in rfl)
    let across := (List.getInRange line position.column).backward (rewrite atColumn in rfl)
    Both tall (rewrite <- wide in across))

--| ...and the other way round.
theorem atOfWithin (grid: Grid a) (rectangle: grid.Rectangle) (position: Position) (inside: grid.contains position = True):
    ∃ (x: a) => grid.at position = Some x :=
  let tall := (List.getInRange grid.rows position.row).forward (inside.left)
  match atRow: List.get grid.rows position.row with
    | Some line =>
      let wide: line.length = grid.width := rectangle line (List.memOfGet grid.rows position.row line atRow)
      let across := (List.getInRange line position.column).forward (rewrite wide in inside.right)
      match atColumn: List.get line position.column with
        | Some x => Witness x rfl

--| The fast lookup is `at`.
theorem lookupAt (grid: Grid a) (position: Position): grid.lookup position = grid.at position :=
  rewrite List.getOrGet (grid.rows.map List.toArray) position.row Array.empty, List.getMap grid.rows List.toArray position.row in
    match List.get grid.rows position.row with
      | None => rfl
      | Some line => rfl

--| The fast lookup with a fallback is `at`, or the fallback off the grid.
theorem lookupOrAt (grid: Grid a) (fallback: a) (position: Position): grid.lookupOr fallback position = (grid.at position).getOrElse fallback :=
  rewrite List.getOrGet (grid.rows.map List.toArray) position.row Array.empty, List.getMap grid.rows List.toArray position.row in
    match List.get grid.rows position.row with
      | None => rfl
      | Some line => List.getOrGet line position.column fallback

--| `isRectangle` is `Rectangle`.
theorem isRectangleIff (grid: Grid a): grid.isRectangle = True ↔ grid.Rectangle := {
  forward = all row member => (all.read row member).read,
  backward = rectangle =>
    List.allOfAll (row => row.length == grid.width) grid.rows
      (List.allOfMem (row => (row.length == grid.width) = True) grid.rows (row member => rewrite rectangle row member in DecEq.refl grid.width))
}

--| A grid mapped is as wide and as tall...
theorem mapWidth (grid: Grid a) (f: Position → a → b): (grid.map f).width = grid.width ∧ (grid.map f).height = grid.height :=
  Both (mapFirstWidth grid.rows f) (List.lengthMapWithIndex grid.rows (r row => row.mapWithIndex (c cell => f { row = r, column = c } cell)))

--| ...and a rectangle mapped is a rectangle.
theorem mapRectangle (grid: Grid a) (rectangle: grid.Rectangle) (f: Position → a → b): (grid.map f).Rectangle
  | row, member =>
    Exists.elim (List.memMapElim (pair => pair.snd.mapWithIndex (c cell => f { row = pair.fst, column = c } cell)) row grid.rows.withIndex member)
      (pair both =>
        match pair with
          | (r, line) =>
            let (Both inRows made) := both
            let original := List.memOfGet grid.rows r line ((List.memWithIndex grid.rows r line).forward inRows)
            rewrite <- made, List.lengthMapWithIndex line (c cell => f { row = r, column = c } cell), And.left (mapWidth grid f) in
              rectangle line original)

--| A grid's step is a step, onto the grid's rectangle.
theorem gridStepElim (grid: Grid a) (position: Position) (direction: Direction) (next: Position) (stepped: grid.step position direction = Some next):
    position.step direction = Some next ∧ grid.contains next = True := match s: position.step direction with
      | Some other =>
        match inside: grid.contains other with
          | True =>
            let same: other = next := Option.someInjective stepped
            rewrite <- same in Both rfl inside

theorem gridStepIntro (grid: Grid a) (position: Position) (direction: Direction) (next: Position) (stepped: position.step direction = Some next)
    (inside: grid.contains next = True): grid.step position direction = Some next :=
  rewrite stepped in rewrite inside in rfl

--| A cell `positionsWhere` keeps is at that position, and its tile passes.
theorem keptCell (keep: a → Bool) (at: Position) (tile: a) (position: Position)
    (kept: (match some | (here, tile) if keep tile => here) (at, tile) = Some position): at = position ∧ keep tile = True :=
  match c: keep tile with
    | True => Both (Option.someInjective kept) rfl

--| A cell whose tile passes is kept, at its position.
theorem keepsCell (keep: a → Bool) (at: Position) (tile: a) (passes: keep tile = True):
    (match some | (here, tile) if keep tile => here) (at, tile) = Some at := match c: keep tile with
      | True => rfl

--| A position is among those of the cells whose tile passes `keep` exactly
--| when one of those cells has a tile that does.
theorem memPositionsWhere (cells: List (Position, a)) (keep: a → Bool) (position: Position):
    (position ∈ positionsWhere cells keep) ↔ (∃ (tile: a) => (position, tile) ∈ cells ∧ keep tile = True) := {
  forward = member =>
    Exists.elim ((List.memFilterMap (match some | (here, tile) if keep tile => here) position cells).forward member) (entry both =>
      match entry with
        | (at, tile) =>
          let (Both inCells kept) := both
          let (Both same passes) := keptCell keep at tile position kept
          Witness tile (Both (rewrite <- same in inCells) passes)),
  backward = found =>
    Exists.elim found (tile both =>
      let (Both inCells passes) := both
      (List.memFilterMap (match some | (here, tile) if keep tile => here) position cells).backward
        (Witness (position, tile) (Both inCells (keepsCell keep position tile passes))))
}

--| A position is among a grid's `positionsWhere` exactly when the grid has a
--| tile there that passes `keep`.
theorem memGridPositionsWhere (grid: Grid a) (keep: a → Bool) (position: Position):
    (position ∈ grid.positionsWhere keep) ↔ (∃ (tile: a) => grid.at position = Some tile ∧ keep tile = True) := {
  forward = member =>
    Exists.elim ((memPositionsWhere grid.cells keep position).forward member) (tile both =>
      Witness tile (Both ((memCells grid.rows position tile).forward (And.left both)) (And.right both))),
  backward = found =>
    Exists.elim found (tile both =>
      (memPositionsWhere grid.cells keep position).backward
        (Witness tile (Both ((memCells grid.rows position tile).backward (And.left both)) (And.right both))))
}

--| `mapCells` of functions equal at every cell of the rows.
theorem mapCellsCongAt (rows: List (List a)) (g1: Position → a → b) (g2: Position → a → b)
    (same: ∀ (position: Position) (x: a) => cellAt rows position = Some x → g1 position x = g2 position x): mapCells rows g1 = mapCells rows g2 :=
  List.mapCongMem (List.withIndex rows) (p => List.mapWithIndex p.snd (c cell => g1 { row = p.fst, column = c } cell))
    (p => List.mapWithIndex p.snd (c cell => g2 { row = p.fst, column = c } cell))
    (p inRows =>
      match p with
        | (r, row) =>
          let rowAt := (List.memWithIndex rows r row).forward inRows
          List.mapCongMem (List.withIndex row) (q => g1 { row = r, column = q.fst } q.snd) (q => g2 { row = r, column = q.fst } q.snd)
            (q inRow =>
              match q with
                | (c, cell) =>
                  let cellAt := (List.memWithIndex row c cell).forward inRow
                  same { row = r, column = c } cell (rewrite rowAt in cellAt)))
