-- Day 4, part 1 proved for every rectangular grid: the printed answer is the
-- number of accessible rolls as Proofs/Spec.sw states it (`part1Correct`, at
-- the bottom). The argument: a round, row by row (`roundFromAt`) and cell by
-- cell (`peelCellsAt`, `colsAt`), leaves each cell as `keep cell window`
-- (`cellRound`), where the window is the 3 by 3 block with an empty border;
-- the window is the neighbours plus the cell (`windowIsNeighbours`); and a
-- round only removes rolls (`keepLe`), so the rolls it removes add up cell by
-- cell to the accessible ones (`taken`). Part 2 is not proved yet: see the
-- plan in docs/aoc-2025.md (day 4).

namespace Aoc.Day04.Proofs
import Aoc.Day04 (..)
import Std (Eq)

theorem cellAtGrid (lines: List Text) (row: Nat) (col: Nat):
    cellAt lines row col = List.getOr Floor col (Cons Floor (List.getOr Nil row (Cons Nil (parseGrid lines)))) := rfl

-- What a round leaves in a cell holding `roll`, whose 3 by 3 window holds
-- `window` rolls.
def keep (roll: Cell) (window: Nat): Cell := if roll == Roll && 5 <= window then Roll else Floor

-- `peelCells` cell by cell: the window of cell i is the column sums at i - 1
-- (`left` for the first), i and i + 1.
theorem peelCellsAt (left: Nat): (cols: List Nat) -> (rolls: List Cell) -> List.length cols = List.length rolls -> (i: Nat) ->
    List.getOr Floor i (peelCells left cols rolls) = keep (List.getOr Floor i rolls) (List.getOr 0 i (Cons left cols) + List.getOr 0 i cols + List.getOr 0 (Succ i) cols)
  | Nil,               Nil,              h, i      => rfl
  | Nil,               Cons roll rolls,  h, i      => Void.exfalso (Nat.zeroNotSucc (List.length rolls) h)
  | Cons here columns, Nil,              h, i      => Void.exfalso (Nat.succNotZero (List.length columns) h)
  | Cons here columns, Cons roll rolls,  h, Zero   => rewrite List.headOrGetOr 0 columns
  | Cons here columns, Cons roll rolls,  h, Succ i => peelCellsAt here columns rolls (Nat.succInjective (List.length columns) (List.length rolls) h) i

theorem lengthPeelCells (left: Nat): (cols: List Nat) -> (rolls: List Cell) -> List.length cols = List.length rolls ->
    List.length (peelCells left cols rolls) = List.length rolls
  | Nil,               Nil,              h => rfl
  | Nil,               Cons roll rolls,  h => Void.exfalso (Nat.zeroNotSucc (List.length rolls) h)
  | Cons here columns, Nil,              h => Void.exfalso (Nat.succNotZero (List.length columns) h)
  | Cons here columns, Cons roll rolls,  h => rewrite lengthPeelCells here columns rolls (Nat.succInjective (List.length columns) (List.length rolls) h)

-- `roundFrom` row by row: row r is peeled with the rows next to it.
theorem roundFromAt (gap: List Cell): (above: List Cell) -> (rows: Grid) -> (r: Nat) -> r < List.length rows ->
    List.getOr Nil r (roundFrom gap above rows) = peelRow (List.getOr gap r (Cons above rows)) (List.getOr gap r rows) (List.getOr gap (Succ r) rows)
  | above, Nil,           r,      h => Void.exfalso (Bool.falseNotTrue h)
  | above, Cons row rest, Zero,   h => rewrite List.headOrGetOr gap rest
  | above, Cons row rest, Succ r, h => roundFromAt gap row rest r h

theorem lengthRoundFrom (gap: List Cell): (above: List Cell) -> (rows: Grid) -> List.length (roundFrom gap above rows) = List.length rows
  | above, Nil           => rfl
  | above, Cons row rest => rewrite lengthRoundFrom gap row rest

-- The missing rows (a row of floor, or none at all) hold no rolls.
theorem gapCells (k: Nat): (rows: Grid) -> (r: Nat) -> (i: Nat) ->
    List.getOr Floor i (List.getOr (List.replicate k Floor) r rows) = List.getOr Floor i (List.getOr Nil r rows)
  | Nil,           r,      i => List.getOrReplicate Floor i k
  | Cons row rest, Zero,   i => rfl
  | Cons row rest, Succ r, i => gapCells k rest r i

theorem gapCellsTop (k: Nat) (rows: Grid): (r: Nat) -> (i: Nat) ->
    List.getOr Floor i (List.getOr (List.replicate k Floor) r (Cons (List.replicate k Floor) rows)) = List.getOr Floor i (List.getOr Nil r (Cons Nil rows))
  | Zero,   i => List.getOrReplicate Floor i k
  | Succ r, i => gapCells k rows r i

-- Every row is w long (a precondition: the grid is rectangular).
def Rows (w: Nat) (rows: Grid): Prop := (r: Nat) -> r < List.length rows -> List.length (List.getOr Nil r rows) = w

theorem rowsLength (w: Nat) (gap: List Cell) (hg: List.length gap = w): (rows: Grid) -> Rows w rows -> (r: Nat) -> List.length (List.getOr gap r rows) = w
  | Nil,           h, r      => hg
  | Cons row rest, h, Zero   => h 0 rfl
  | Cons row rest, h, Succ r => rowsLength w gap hg rest (s hs => h (Succ s) hs) r

theorem rowsTop (k: Nat) (grid: Grid) (rect: Rows k grid): Rows k (Cons (List.replicate k Floor) grid) :=
  s hs => match s with
    | Zero   => List.lengthReplicate Floor k
    | Succ t => rect t hs

-- The grid with an empty border, counted from 1 (as `cellAt`), and the
-- rolls in a cell of it.
def cellOf (grid: Grid) (row: Nat) (col: Nat): Cell := List.getOr Floor col (Cons Floor (List.getOr Nil row (Cons Nil grid)))

def bordered (grid: Grid) (row: Nat) (col: Nat): Nat := (cellOf grid row col).count

-- The column of three cells from row R down, in column C (bordered).
def colSum (grid: Grid) (row: Nat) (col: Nat): Nat := bordered grid row col + bordered grid (Succ row) col + bordered grid (Succ (Succ row)) col

-- The column sums `peelRow` adds up are the bordered grid's.
theorem colsAt (k: Nat) (grid: Grid) (rect: Rows k grid) (r: Nat): (col: Nat) ->
    List.getOr 0 col (Cons 0 (List.zipWith3 (a b c => Cell.count a + Cell.count b + Cell.count c)
        (List.getOr (List.replicate k Floor) r (Cons (List.replicate k Floor) grid)) (List.getOr (List.replicate k Floor) r grid) (List.getOr (List.replicate k Floor) (Succ r) grid)))
      = colSum grid r col
  | Zero   => rfl
  | Succ i =>
    rewrite List.getOrZipWith3 (a b c => Cell.count a + Cell.count b + Cell.count c) Floor Floor Floor 0 rfl
        (List.getOr (List.replicate k Floor) r (Cons (List.replicate k Floor) grid)) (List.getOr (List.replicate k Floor) r grid) (List.getOr (List.replicate k Floor) (Succ r) grid)
        (rewrite rowsLength k (List.replicate k Floor) (List.lengthReplicate Floor k) grid rect r,
           rowsLength k (List.replicate k Floor) (List.lengthReplicate Floor k) (Cons (List.replicate k Floor) grid) (rowsTop k grid rect) r)
        (rewrite rowsLength k (List.replicate k Floor) (List.lengthReplicate Floor k) grid rect (Succ r),
           rowsLength k (List.replicate k Floor) (List.lengthReplicate Floor k) (Cons (List.replicate k Floor) grid) (rowsTop k grid rect) r)
        i,
      gapCellsTop k grid r i, gapCells k grid r i, gapCells k grid (Succ r) i

-- One cell after a round.
theorem cellRound (k: Nat) (grid: Grid) (rect: Rows k grid) (r: Nat) (hr: r < List.length grid) (c: Nat):
    List.getOr Floor c (List.getOr Nil r (roundFrom (List.replicate k Floor) (List.replicate k Floor) grid))
      = keep (cellOf grid (Succ r) (Succ c)) (colSum grid r c + colSum grid r (Succ c) + colSum grid r (Succ (Succ c))) :=
  let gap := List.replicate k Floor
  let cols := List.zipWith3 (a b c => Cell.count a + Cell.count b + Cell.count c) (List.getOr gap r (Cons gap grid)) (List.getOr gap r grid) (List.getOr gap (Succ r) grid)
  let lenA: List.length (List.getOr gap r (Cons gap grid)) = k := rowsLength k gap (List.lengthReplicate Floor k) (Cons gap grid) (rowsTop k grid rect) r
  let lenR: List.length (List.getOr gap r grid) = k := rowsLength k gap (List.lengthReplicate Floor k) grid rect r
  let lenB: List.length (List.getOr gap (Succ r) grid) = k := rowsLength k gap (List.lengthReplicate Floor k) grid rect (Succ r)
  let lenCols: List.length cols = List.length (List.getOr gap r grid) :=
    rewrite List.lengthZipWith3 (a b c => Cell.count a + Cell.count b + Cell.count c) (List.getOr gap r (Cons gap grid)) (List.getOr gap r grid) (List.getOr gap (Succ r) grid)
        (rewrite lenR, lenA) (rewrite lenB, lenA),
      lenA, lenR
  calc List.getOr Floor c (List.getOr Nil r (roundFrom gap gap grid))
    _ = List.getOr Floor c (peelCells 0 cols (List.getOr gap r grid)) := rewrite roundFromAt gap gap grid r hr
    _ = keep (List.getOr Floor c (List.getOr gap r grid)) (List.getOr 0 c (Cons 0 cols) + List.getOr 0 (Succ c) (Cons 0 cols) + List.getOr 0 (Succ (Succ c)) (Cons 0 cols))
        := peelCellsAt 0 cols (List.getOr gap r grid) lenCols c
    _ = keep (cellOf grid (Succ r) (Succ c)) (colSum grid r c + colSum grid r (Succ c) + colSum grid r (Succ (Succ c)))
        := rewrite gapCells k grid r c, colsAt k grid rect r c, colsAt k grid rect r (Succ c), colsAt k grid rect r (Succ (Succ c))

-- A round never adds a roll.
theorem keepLe: (a: Cell) -> (w: Nat) -> Cell.count (keep a w) <= Cell.count a
  | Floor, w => rfl
  | Roll,  w =>
    match Nat.leq 5 w with
      | True  => rfl
      | False => rfl


-- The window is the neighbours and the cell itself.
theorem windowSplit (l: Nat) (a: Nat) (m: Nat) (b: Nat) (rt: Nat): l + (a + m + b) + rt = l + (a + b) + rt + m :=
  calc l + (a + m + b) + rt
    _ = l + (a + b + m) + rt := rewrite Nat.addAssoc a m b, Nat.addComm m b, Nat.addAssoc a b m
    _ = l + (a + b) + m + rt := rewrite Nat.addAssoc l (a + b) m
    _ = l + (a + b) + rt + m := rewrite Nat.addAssoc (l + (a + b)) m rt, Nat.addComm m rt, Nat.addAssoc (l + (a + b)) rt m

theorem windowIsNeighbours (lines: List Text) (r: Nat) (c: Nat):
    colSum (parseGrid lines) r c + colSum (parseGrid lines) r (Succ c) + colSum (parseGrid lines) r (Succ (Succ c))
      = neighbours lines r c + bordered (parseGrid lines) (Succ r) (Succ c) :=
  rewrite Nat.addOne r, Nat.addOne c, Nat.addTwo r, Nat.addTwo c in
    windowSplit (colSum (parseGrid lines) r c) (bordered (parseGrid lines) r (Succ c)) (bordered (parseGrid lines) (Succ r) (Succ c))
      (bordered (parseGrid lines) (Succ (Succ r)) (Succ c)) (colSum (parseGrid lines) r (Succ (Succ c)))

-- What a round takes from one cell: 1 when it holds an accessible roll.
theorem taken: (a: Cell) -> (n: Nat) -> Cell.count a - Cell.count (keep a (n + Cell.count a)) = (if a == Roll && n < 4 then 1 else 0)
  | Floor, n                           => rfl
  | Roll,  0                           => rfl
  | Roll,  1                           => rfl
  | Roll,  2                           => rfl
  | Roll,  3                           => rfl
  | Roll,  Succ (Succ (Succ (Succ n))) => rewrite Nat.addOne n

-- The rolls of a rectangular grid, cell by cell.
theorem rollsCells (k: Nat) (grid: Grid) (rect: Rows k grid):
    Grid.rolls grid = List.sumBy (r => List.sumBy (c => bordered grid (Succ r) (Succ c)) (List.range k)) (List.range (List.length grid)) :=
  calc List.sumBy (row => List.sumBy Cell.count row) grid
    _ = List.sumBy (r => List.sumBy Cell.count (List.getOr Nil r grid)) (List.range (List.length grid)) := List.sumByGetOr (row => List.sumBy Cell.count row) Nil grid
    _ = List.sumBy (r => List.sumBy (c => bordered grid (Succ r) (Succ c)) (List.range k)) (List.range (List.length grid)) :=
        List.sumRangeCongr (r => List.sumBy Cell.count (List.getOr Nil r grid)) (r => List.sumBy (c => bordered grid (Succ r) (Succ c)) (List.range k)) (List.length grid) 0
          (r h1 h2 =>
            calc List.sumBy Cell.count (List.getOr Nil r grid)
              _ = List.sumBy (c => Cell.count (List.getOr Floor c (List.getOr Nil r grid))) (List.range (List.length (List.getOr Nil r grid))) := List.sumByGetOr Cell.count Floor (List.getOr Nil r grid)
              _ = List.sumBy (c => bordered grid (Succ r) (Succ c)) (List.range k) := rewrite rect r h2)

-- A round keeps the grid's shape.
theorem roundRows (k: Nat) (grid: Grid) (rect: Rows k grid): Rows k (roundFrom (List.replicate k Floor) (List.replicate k Floor) grid) :=
  r hr =>
    let gap := List.replicate k Floor
    let hr2: r < List.length grid := rewrite <- lengthRoundFrom gap gap grid in hr
    let lenA: List.length (List.getOr gap r (Cons gap grid)) = k := rowsLength k gap (List.lengthReplicate Floor k) (Cons gap grid) (rowsTop k grid rect) r
    let lenR: List.length (List.getOr gap r grid) = k := rowsLength k gap (List.lengthReplicate Floor k) grid rect r
    let lenB: List.length (List.getOr gap (Succ r) grid) = k := rowsLength k gap (List.lengthReplicate Floor k) grid rect (Succ r)
    rewrite roundFromAt gap gap grid r hr2,
      lengthPeelCells 0 (List.zipWith3 (a b c => Cell.count a + Cell.count b + Cell.count c) (List.getOr gap r (Cons gap grid)) (List.getOr gap r grid) (List.getOr gap (Succ r) grid)) (List.getOr gap r grid)
        (rewrite List.lengthZipWith3 (a b c => Cell.count a + Cell.count b + Cell.count c) (List.getOr gap r (Cons gap grid)) (List.getOr gap r grid) (List.getOr gap (Succ r) grid)
            (rewrite lenR, lenA) (rewrite lenB, lenA),
          lenA, lenR) in
      lenR

-- One cell: what a round takes is 1 exactly when the spec calls the roll accessible.
theorem takenCell (lines: List Text) (r: Nat) (c: Nat):
    bordered (parseGrid lines) (Succ r) (Succ c)
      - Cell.count (keep (cellOf (parseGrid lines) (Succ r) (Succ c))
          (colSum (parseGrid lines) r c + colSum (parseGrid lines) r (Succ c) + colSum (parseGrid lines) r (Succ (Succ c))))
      = (if accessible lines r c then 1 else 0) :=
  rewrite windowIsNeighbours lines r c in
    calc bordered (parseGrid lines) (Succ r) (Succ c) - Cell.count (keep (cellOf (parseGrid lines) (Succ r) (Succ c)) (neighbours lines r c + bordered (parseGrid lines) (Succ r) (Succ c)))
      _ = (if cellOf (parseGrid lines) (Succ r) (Succ c) == Roll && neighbours lines r c < 4 then 1 else 0)
          := taken (cellOf (parseGrid lines) (Succ r) (Succ c)) (neighbours lines r c)
      _ = (if accessible lines r c then 1 else 0) := rewrite Nat.addOne r, Nat.addOne c

-- The parsed grid of a rectangular input is rectangular.
theorem parsedRows (lines: List Text) (w: Nat) (rect: (r: Nat) -> r < List.length lines -> Text.length (List.getOr "" r lines) = w):
    Rows w (parseGrid lines) :=
  r hr => rewrite List.getOrMap parseLine "" r lines, List.lengthMap parseChar (Text.toList (List.getOr "" r lines)) in
    rect r (rewrite <- List.lengthMap parseLine lines in hr)

-- Part 1 is right for every rectangular grid: the printed answer is the
-- number of rolls with fewer than four rolls around them.
theorem part1Correct (lines: List Text) (w: Nat) (rect: (r: Nat) -> r < List.length lines -> Text.length (List.getOr "" r lines) = w):
    solvePart1 (parseGrid lines) = part1Spec lines :=
  match lines with
    | Nil         => rfl
    | Cons l rest =>
      let grid := parseGrid (Cons l rest)
      let gap := List.replicate w Floor
      let cell := (r: Nat) => (c: Nat) => cellOf grid (Succ r) (Succ c)
      let rows: Rows w grid := parsedRows (Cons l rest) w rect
      let a := (r: Nat) => (c: Nat) => bordered grid (Succ r) (Succ c)
      let window := (r: Nat) => (c: Nat) => colSum grid r c + colSum grid r (Succ c) + colSum grid r (Succ (Succ c))
      calc solvePart1 grid
        _ = Grid.rolls grid - Grid.rolls (roundFrom gap gap grid) := rewrite List.lengthMap parseChar (Text.toList l), rect 0 rfl
        _ = List.sumBy (r => List.sumBy (c => a r c) (List.range w)) (List.range (List.length grid))
              - List.sumBy (r => List.sumBy (c => bordered (roundFrom gap gap grid) (Succ r) (Succ c)) (List.range w)) (List.range (List.length grid))
            := rewrite rollsCells w grid rows, rollsCells w (roundFrom gap gap grid) (roundRows w grid rows) in
                 Eq.cong (t => List.sumBy (r => List.sumBy (c => a r c) (List.range w)) (List.range (List.length grid))
                                 - List.sumBy (r => List.sumBy (c => bordered (roundFrom gap gap grid) (Succ r) (Succ c)) (List.range w)) (List.range t))
                   (lengthRoundFrom gap gap grid)
        _ = List.sumBy (r => List.sumBy (c => a r c) (List.range w)) (List.range (List.length grid))
              - List.sumBy (r => List.sumBy (c => Cell.count (keep (cell r c) (window r c))) (List.range w)) (List.range (List.length grid))
            := rewrite List.sumRangeCongr
                 (r => List.sumBy (c => bordered (roundFrom gap gap grid) (Succ r) (Succ c)) (List.range w))
                 (r => List.sumBy (c => Cell.count (keep (cell r c) (window r c))) (List.range w)) (List.length grid) 0
                 (r h1 h2 => List.sumByCongr (c => bordered (roundFrom gap gap grid) (Succ r) (Succ c)) (c => Cell.count (keep (cell r c) (window r c)))
                    (c => Eq.cong Cell.count (cellRound w grid rows r h2 c)) (List.range w))
        _ = List.sumBy (r => List.sumBy (c => a r c - Cell.count (keep (cell r c) (window r c))) (List.range w)) (List.range (List.length grid))
            := rewrite List.sumBySub (r => List.sumBy (c => a r c) (List.range w)) (r => List.sumBy (c => Cell.count (keep (cell r c) (window r c))) (List.range w))
                   (r => List.sumByLe (c => a r c) (c => Cell.count (keep (cell r c) (window r c))) (c => keepLe (cell r c) (window r c)) (List.range w))
                   (List.range (List.length grid)) in
                 List.sumByCongr
                   (r => List.sumBy (c => a r c) (List.range w) - List.sumBy (c => Cell.count (keep (cell r c) (window r c))) (List.range w))
                   (r => List.sumBy (c => a r c - Cell.count (keep (cell r c) (window r c))) (List.range w))
                   (r => List.sumBySub (c => a r c) (c => Cell.count (keep (cell r c) (window r c))) (c => keepLe (cell r c) (window r c)) (List.range w))
                   (List.range (List.length grid))
        _ = List.sumBy (r => List.sumBy (c => if accessible (Cons l rest) r c then 1 else 0) (List.range w)) (List.range (List.length grid))
            := List.sumByCongr
                 (r => List.sumBy (c => a r c - Cell.count (keep (cell r c) (window r c))) (List.range w))
                 (r => List.sumBy (c => if accessible (Cons l rest) r c then 1 else 0) (List.range w))
                 (r => List.sumByCongr (c => a r c - Cell.count (keep (cell r c) (window r c))) (c => if accessible (Cons l rest) r c then 1 else 0)
                    (c => takenCell (Cons l rest) r c) (List.range w))
                 (List.range (List.length grid))
        _ = part1Spec (Cons l rest)
            := rewrite List.lengthMap parseLine rest in
                 List.sumRangeCongr
                   (r => List.sumBy (c => if accessible (Cons l rest) r c then 1 else 0) (List.range w))
                   (r => List.sumBy (c => if accessible (Cons l rest) r c then 1 else 0) (List.range (Text.length (List.getOr "" r (Cons l rest)))))
                   (List.length (Cons l rest)) 0
                   (r h1 h2 => rewrite rect r h2)
