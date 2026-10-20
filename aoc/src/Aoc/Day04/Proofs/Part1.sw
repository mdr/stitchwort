namespace Aoc.Day04.Proofs
import Aoc.Day04 (..)
import Std (Eq)

theorem parseCharBit (ch: Char): parseChar ch <= 1 :=
  match ch == '@' with
    | True  => rfl
    | False => rfl

theorem rollAtGrid (lines: List Text) (row: Nat) (col: Nat):
    rollAt lines row col = List.getOr 0 col (Cons 0 (List.getOr Nil row (Cons Nil (parseGrid lines)))) := rfl

-- General lemmas (to move to the library).

theorem PList.headOrGetOr (d: a): (xs: List a) -> List.headOr d xs = List.getOr d 0 xs
  | Nil       => rfl
  | Cons x xs => rfl

theorem PList.getOrZipWith3 (f: a -> b -> c -> e) (d1: a) (d2: b) (d3: c) (d: e) (hd: f d1 d2 d3 = d):
    (xs: List a) -> (ys: List b) -> (zs: List c) -> List.length ys = List.length xs -> List.length zs = List.length xs -> (i: Nat) ->
    List.getOr d i (List.zipWith3 f xs ys zs) = f (List.getOr d1 i xs) (List.getOr d2 i ys) (List.getOr d3 i zs)
  | Nil,       Nil,       Nil,       h1, h2, i      => Eq.sym hd
  | Nil,       Cons y ys, zs,        h1, h2, i      => Void.exfalso (Nat.succNotZero (List.length ys) h1)
  | Nil,       Nil,       Cons z zs, h1, h2, i      => Void.exfalso (Nat.succNotZero (List.length zs) h2)
  | Cons x xs, Nil,       zs,        h1, h2, i      => Void.exfalso (Nat.zeroNotSucc (List.length xs) h1)
  | Cons x xs, Cons y ys, Nil,       h1, h2, i      => Void.exfalso (Nat.zeroNotSucc (List.length xs) h2)
  | Cons x xs, Cons y ys, Cons z zs, h1, h2, Zero   => rfl
  | Cons x xs, Cons y ys, Cons z zs, h1, h2, Succ i =>
    PList.getOrZipWith3 f d1 d2 d3 d hd xs ys zs (Nat.succInjective (List.length ys) (List.length xs) h1) (Nat.succInjective (List.length zs) (List.length xs) h2) i

theorem PList.lengthZipWith3 (f: a -> b -> c -> e): (xs: List a) -> (ys: List b) -> (zs: List c) ->
    List.length ys = List.length xs -> List.length zs = List.length xs -> List.length (List.zipWith3 f xs ys zs) = List.length xs
  | Nil,       ys,        zs,        h1, h2 => rfl
  | Cons x xs, Nil,       zs,        h1, h2 => Void.exfalso (Nat.zeroNotSucc (List.length xs) h1)
  | Cons x xs, Cons y ys, Nil,       h1, h2 => Void.exfalso (Nat.zeroNotSucc (List.length xs) h2)
  | Cons x xs, Cons y ys, Cons z zs, h1, h2 =>
    rewrite PList.lengthZipWith3 f xs ys zs (Nat.succInjective (List.length ys) (List.length xs) h1) (Nat.succInjective (List.length zs) (List.length xs) h2)

-- A sum over a list is the sum over its indices.
theorem PList.sumByGetOr (f: a -> Nat) (d: a) (xs: List a): List.sumBy f xs = List.sumBy (i => f (List.getOr d i xs)) (List.range (List.length xs)) :=
  calc List.sumBy f xs
    _ = List.sumBy f (List.map (i => List.getOr d i xs) (List.range (List.length xs))) := rewrite List.mapGetOr d xs
    _ = List.sumBy (i => f (List.getOr d i xs)) (List.range (List.length xs)) := List.sumByMap f (i => List.getOr d i xs) (List.range (List.length xs))

-- Taking away a smaller sum term by term.
theorem PList.sumBySplit (f: a -> Nat) (g: a -> Nat) (h: (x: a) -> g x <= f x) (xs: List a):
    List.sumBy f xs = List.sumBy g xs + List.sumBy (x => f x - g x) xs :=
  calc List.sumBy f xs
    _ = List.sumBy (x => g x + (f x - g x)) xs := List.sumByCongr f (x => g x + (f x - g x)) (x => Eq.sym (Nat.addSubCancel (g x) (f x) (h x))) xs
    _ = List.sumBy g xs + List.sumBy (x => f x - g x) xs := List.sumByAdd g (x => f x - g x) xs

theorem PList.sumByLe (f: a -> Nat) (g: a -> Nat) (h: (x: a) -> g x <= f x) (xs: List a): List.sumBy g xs <= List.sumBy f xs :=
  rewrite PList.sumBySplit f g h xs in Nat.leAddRight (List.sumBy g xs) (List.sumBy (x => f x - g x) xs)

theorem PList.sumBySub (f: a -> Nat) (g: a -> Nat) (h: (x: a) -> g x <= f x) (xs: List a):
    List.sumBy f xs - List.sumBy g xs = List.sumBy (x => f x - g x) xs :=
  rewrite PList.sumBySplit f g h xs in Nat.addSubLeft (List.sumBy g xs) (List.sumBy (x => f x - g x) xs)

-- What a round leaves in a cell holding `roll`, whose 3 by 3 window holds
-- `window` rolls.
def keep (roll: Nat) (window: Nat): Nat := if roll == 1 && 5 <= window then 1 else 0

-- `peelCells` cell by cell: the window of cell i is the column sums at i - 1
-- (`left` for the first), i and i + 1.
theorem peelCellsAt (left: Nat): (cols: List Nat) -> (rolls: List Nat) -> List.length cols = List.length rolls -> (i: Nat) ->
    List.getOr 0 i (peelCells left cols rolls) = keep (List.getOr 0 i rolls) (List.getOr 0 i (Cons left cols) + List.getOr 0 i cols + List.getOr 0 (Succ i) cols)
  | Nil,               Nil,              h, i      => rfl
  | Nil,               Cons roll rolls,  h, i      => Void.exfalso (Nat.zeroNotSucc (List.length rolls) h)
  | Cons here columns, Nil,              h, i      => Void.exfalso (Nat.succNotZero (List.length columns) h)
  | Cons here columns, Cons roll rolls,  h, Zero   => rewrite PList.headOrGetOr 0 columns
  | Cons here columns, Cons roll rolls,  h, Succ i => peelCellsAt here columns rolls (Nat.succInjective (List.length columns) (List.length rolls) h) i

theorem lengthPeelCells (left: Nat): (cols: List Nat) -> (rolls: List Nat) -> List.length cols = List.length rolls ->
    List.length (peelCells left cols rolls) = List.length rolls
  | Nil,               Nil,              h => rfl
  | Nil,               Cons roll rolls,  h => Void.exfalso (Nat.zeroNotSucc (List.length rolls) h)
  | Cons here columns, Nil,              h => Void.exfalso (Nat.succNotZero (List.length columns) h)
  | Cons here columns, Cons roll rolls,  h => rewrite lengthPeelCells here columns rolls (Nat.succInjective (List.length columns) (List.length rolls) h)

-- `roundFrom` row by row: row r is peeled with the rows next to it.
theorem roundFromAt (gap: List Nat): (above: List Nat) -> (rows: Grid) -> (r: Nat) -> r < List.length rows ->
    List.getOr Nil r (roundFrom gap above rows) = peelRow (List.getOr gap r (Cons above rows)) (List.getOr gap r rows) (List.getOr gap (Succ r) rows)
  | above, Nil,           r,      h => Void.exfalso (Bool.falseNotTrue h)
  | above, Cons row rest, Zero,   h => rewrite PList.headOrGetOr gap rest
  | above, Cons row rest, Succ r, h => roundFromAt gap row rest r h

theorem lengthRoundFrom (gap: List Nat): (above: List Nat) -> (rows: Grid) -> List.length (roundFrom gap above rows) = List.length rows
  | above, Nil           => rfl
  | above, Cons row rest => rewrite lengthRoundFrom gap row rest

-- The missing rows (a row of 0s, or none at all) hold no rolls.
theorem gapCells (k: Nat): (rows: Grid) -> (r: Nat) -> (i: Nat) ->
    List.getOr 0 i (List.getOr (List.replicate k 0) r rows) = List.getOr 0 i (List.getOr Nil r rows)
  | Nil,           r,      i => List.getOrReplicate 0 i k
  | Cons row rest, Zero,   i => rfl
  | Cons row rest, Succ r, i => gapCells k rest r i

theorem gapCellsTop (k: Nat) (rows: Grid): (r: Nat) -> (i: Nat) ->
    List.getOr 0 i (List.getOr (List.replicate k 0) r (Cons (List.replicate k 0) rows)) = List.getOr 0 i (List.getOr Nil r (Cons Nil rows))
  | Zero,   i => List.getOrReplicate 0 i k
  | Succ r, i => gapCells k rows r i

-- Every row is w long (a precondition: the grid is rectangular).
def Rows (w: Nat) (rows: Grid): Prop := (r: Nat) -> r < List.length rows -> List.length (List.getOr Nil r rows) = w

theorem rowsLength (w: Nat) (gap: List Nat) (hg: List.length gap = w): (rows: Grid) -> Rows w rows -> (r: Nat) -> List.length (List.getOr gap r rows) = w
  | Nil,           h, r      => hg
  | Cons row rest, h, Zero   => h 0 rfl
  | Cons row rest, h, Succ r => rowsLength w gap hg rest (s hs => h (Succ s) hs) r

theorem rowsTop (k: Nat) (grid: Grid) (rect: Rows k grid): Rows k (Cons (List.replicate k 0) grid) :=
  s hs => match s with
    | Zero   => List.lengthReplicate 0 k
    | Succ t => rect t hs

-- The grid with an empty border, counted from 1 (as `rollAt`).
def bordered (grid: Grid) (row: Nat) (col: Nat): Nat := List.getOr 0 col (Cons 0 (List.getOr Nil row (Cons Nil grid)))

-- The column of three cells from row R down, in column C (bordered).
def colSum (grid: Grid) (row: Nat) (col: Nat): Nat := bordered grid row col + bordered grid (Succ row) col + bordered grid (Succ (Succ row)) col

-- The column sums `peelRow` adds up are the bordered grid's.
theorem colsAt (k: Nat) (grid: Grid) (rect: Rows k grid) (r: Nat): (col: Nat) ->
    List.getOr 0 col (Cons 0 (List.zipWith3 (a b c => a + b + c)
        (List.getOr (List.replicate k 0) r (Cons (List.replicate k 0) grid)) (List.getOr (List.replicate k 0) r grid) (List.getOr (List.replicate k 0) (Succ r) grid)))
      = colSum grid r col
  | Zero   => rfl
  | Succ i =>
    rewrite PList.getOrZipWith3 (a b c => a + b + c) 0 0 0 0 rfl
        (List.getOr (List.replicate k 0) r (Cons (List.replicate k 0) grid)) (List.getOr (List.replicate k 0) r grid) (List.getOr (List.replicate k 0) (Succ r) grid)
        (rewrite rowsLength k (List.replicate k 0) (List.lengthReplicate 0 k) grid rect r,
           rowsLength k (List.replicate k 0) (List.lengthReplicate 0 k) (Cons (List.replicate k 0) grid) (rowsTop k grid rect) r)
        (rewrite rowsLength k (List.replicate k 0) (List.lengthReplicate 0 k) grid rect (Succ r),
           rowsLength k (List.replicate k 0) (List.lengthReplicate 0 k) (Cons (List.replicate k 0) grid) (rowsTop k grid rect) r)
        i,
      gapCellsTop k grid r i, gapCells k grid r i, gapCells k grid (Succ r) i

-- One cell after a round.
theorem cellRound (k: Nat) (grid: Grid) (rect: Rows k grid) (r: Nat) (hr: r < List.length grid) (c: Nat):
    List.getOr 0 c (List.getOr Nil r (roundFrom (List.replicate k 0) (List.replicate k 0) grid))
      = keep (bordered grid (Succ r) (Succ c)) (colSum grid r c + colSum grid r (Succ c) + colSum grid r (Succ (Succ c))) :=
  let gap := List.replicate k 0
  let cols := List.zipWith3 (a b c => a + b + c) (List.getOr gap r (Cons gap grid)) (List.getOr gap r grid) (List.getOr gap (Succ r) grid)
  let lenA: List.length (List.getOr gap r (Cons gap grid)) = k := rowsLength k gap (List.lengthReplicate 0 k) (Cons gap grid) (rowsTop k grid rect) r
  let lenR: List.length (List.getOr gap r grid) = k := rowsLength k gap (List.lengthReplicate 0 k) grid rect r
  let lenB: List.length (List.getOr gap (Succ r) grid) = k := rowsLength k gap (List.lengthReplicate 0 k) grid rect (Succ r)
  let lenCols: List.length cols = List.length (List.getOr gap r grid) :=
    rewrite PList.lengthZipWith3 (a b c => a + b + c) (List.getOr gap r (Cons gap grid)) (List.getOr gap r grid) (List.getOr gap (Succ r) grid)
        (rewrite lenR, lenA) (rewrite lenB, lenA),
      lenA, lenR
  calc List.getOr 0 c (List.getOr Nil r (roundFrom gap gap grid))
    _ = List.getOr 0 c (peelCells 0 cols (List.getOr gap r grid)) := rewrite roundFromAt gap gap grid r hr
    _ = keep (List.getOr 0 c (List.getOr gap r grid)) (List.getOr 0 c (Cons 0 cols) + List.getOr 0 (Succ c) (Cons 0 cols) + List.getOr 0 (Succ (Succ c)) (Cons 0 cols))
        := peelCellsAt 0 cols (List.getOr gap r grid) lenCols c
    _ = keep (bordered grid (Succ r) (Succ c)) (colSum grid r c + colSum grid r (Succ c) + colSum grid r (Succ (Succ c)))
        := rewrite gapCells k grid r c, colsAt k grid rect r c, colsAt k grid rect r (Succ c), colsAt k grid rect r (Succ (Succ c))

-- A round never adds a roll.
theorem keepLe (a: Nat) (w: Nat): keep a w <= a :=
  match h: (a == 1 && 5 <= w) with
    | True  => rewrite Decidable.toBoolSound (Nat.decEq a 1) (Bool.andLeft (a == 1) (5 <= w) h) in Nat.leRefl 1
    | False => Nat.zeroLe a

-- The cells of the parsed grid are 0 or 1.
theorem parseBits: (cs: List Char) -> (c: Nat) -> List.getOr 0 c (List.map parseChar cs) <= 1
  | Nil,       c      => rfl
  | Cons x xs, Zero   => parseCharBit x
  | Cons x xs, Succ c => parseBits xs c

theorem rowBits: (lines: List Text) -> (r: Nat) -> (c: Nat) -> List.getOr 0 c (List.getOr Nil r (parseGrid lines)) <= 1
  | Nil,         r,      c => rfl
  | Cons l rest, Zero,   c => parseBits (Text.toList l) c
  | Cons l rest, Succ r, c => rowBits rest r c

theorem borderedBit (lines: List Text): (r: Nat) -> (c: Nat) -> bordered (parseGrid lines) r c <= 1
  | r,      Zero   => rfl
  | Zero,   Succ c => rfl
  | Succ r, Succ c => rowBits lines r c

theorem PNat.addTwo (n: Nat): n + 2 = Succ (Succ n) := rewrite Nat.addSucc n 1, Nat.addOne n

-- The window is the neighbours and the cell itself.
theorem windowSplit (l: Nat) (a: Nat) (m: Nat) (b: Nat) (rt: Nat): l + (a + m + b) + rt = l + (a + b) + rt + m :=
  calc l + (a + m + b) + rt
    _ = l + (a + b + m) + rt := rewrite Nat.addAssoc a m b, Nat.addComm m b, Nat.addAssoc a b m
    _ = l + (a + b) + m + rt := rewrite Nat.addAssoc l (a + b) m
    _ = l + (a + b) + rt + m := rewrite Nat.addAssoc (l + (a + b)) m rt, Nat.addComm m rt, Nat.addAssoc (l + (a + b)) rt m

theorem windowIsNeighbours (lines: List Text) (r: Nat) (c: Nat):
    colSum (parseGrid lines) r c + colSum (parseGrid lines) r (Succ c) + colSum (parseGrid lines) r (Succ (Succ c))
      = neighbours lines r c + bordered (parseGrid lines) (Succ r) (Succ c) :=
  rewrite Nat.addOne r, Nat.addOne c, PNat.addTwo r, PNat.addTwo c in
    windowSplit (colSum (parseGrid lines) r c) (bordered (parseGrid lines) r (Succ c)) (bordered (parseGrid lines) (Succ r) (Succ c))
      (bordered (parseGrid lines) (Succ (Succ r)) (Succ c)) (colSum (parseGrid lines) r (Succ (Succ c)))

-- What a round takes from one cell: 1 when it holds an accessible roll.
theorem taken: (a: Nat) -> (n: Nat) -> a <= 1 -> a - keep a (n + a) = (if a == 1 && n < 4 then 1 else 0)
  | 0,               n, h => rfl
  | 1,               0, h => rfl
  | 1,               1, h => rfl
  | 1,               2, h => rfl
  | 1,               3, h => rfl
  | 1,               Succ (Succ (Succ (Succ n))), h => rewrite Nat.addOne n
  | Succ (Succ a),   n, h => Void.exfalso (Bool.falseNotTrue h)

theorem PList.getOrMap (f: a -> b) (d: a): (i: Nat) -> (xs: List a) -> List.getOr (f d) i (List.map f xs) = f (List.getOr d i xs)
  | i,      Nil       => rfl
  | Zero,   Cons x xs => rfl
  | Succ i, Cons x xs => PList.getOrMap f d i xs

-- The rolls of a rectangular grid, cell by cell.
theorem rollsCells (k: Nat) (grid: Grid) (rect: Rows k grid):
    Grid.rolls grid = List.sumBy (r => List.sumBy (c => bordered grid (Succ r) (Succ c)) (List.range k)) (List.range (List.length grid)) :=
  calc List.sumBy List.sum grid
    _ = List.sumBy (r => List.sum (List.getOr Nil r grid)) (List.range (List.length grid)) := PList.sumByGetOr List.sum Nil grid
    _ = List.sumBy (r => List.sumBy (c => bordered grid (Succ r) (Succ c)) (List.range k)) (List.range (List.length grid)) :=
        List.sumRangeCongr (r => List.sum (List.getOr Nil r grid)) (r => List.sumBy (c => bordered grid (Succ r) (Succ c)) (List.range k)) (List.length grid) 0
          (r h1 h2 =>
            calc List.sum (List.getOr Nil r grid)
              _ = List.sumBy (x => x) (List.getOr Nil r grid)
              _ = List.sumBy (c => List.getOr 0 c (List.getOr Nil r grid)) (List.range (List.length (List.getOr Nil r grid))) := PList.sumByGetOr (x => x) 0 (List.getOr Nil r grid)
              _ = List.sumBy (c => bordered grid (Succ r) (Succ c)) (List.range k) := rewrite rect r h2)

-- A round keeps the grid's shape.
theorem roundRows (k: Nat) (grid: Grid) (rect: Rows k grid): Rows k (roundFrom (List.replicate k 0) (List.replicate k 0) grid) :=
  r hr =>
    let gap := List.replicate k 0
    let hr2: r < List.length grid := rewrite <- lengthRoundFrom gap gap grid in hr
    let lenA: List.length (List.getOr gap r (Cons gap grid)) = k := rowsLength k gap (List.lengthReplicate 0 k) (Cons gap grid) (rowsTop k grid rect) r
    let lenR: List.length (List.getOr gap r grid) = k := rowsLength k gap (List.lengthReplicate 0 k) grid rect r
    let lenB: List.length (List.getOr gap (Succ r) grid) = k := rowsLength k gap (List.lengthReplicate 0 k) grid rect (Succ r)
    rewrite roundFromAt gap gap grid r hr2,
      lengthPeelCells 0 (List.zipWith3 (a b c => a + b + c) (List.getOr gap r (Cons gap grid)) (List.getOr gap r grid) (List.getOr gap (Succ r) grid)) (List.getOr gap r grid)
        (rewrite PList.lengthZipWith3 (a b c => a + b + c) (List.getOr gap r (Cons gap grid)) (List.getOr gap r grid) (List.getOr gap (Succ r) grid)
            (rewrite lenR, lenA) (rewrite lenB, lenA),
          lenA, lenR) in
      lenR

-- One cell: what a round takes is 1 exactly when the spec calls the roll accessible.
theorem takenCell (lines: List Text) (r: Nat) (c: Nat):
    bordered (parseGrid lines) (Succ r) (Succ c)
      - keep (bordered (parseGrid lines) (Succ r) (Succ c))
          (colSum (parseGrid lines) r c + colSum (parseGrid lines) r (Succ c) + colSum (parseGrid lines) r (Succ (Succ c)))
      = (if accessible lines r c then 1 else 0) :=
  rewrite windowIsNeighbours lines r c in
    calc bordered (parseGrid lines) (Succ r) (Succ c) - keep (bordered (parseGrid lines) (Succ r) (Succ c)) (neighbours lines r c + bordered (parseGrid lines) (Succ r) (Succ c))
      _ = (if bordered (parseGrid lines) (Succ r) (Succ c) == 1 && neighbours lines r c < 4 then 1 else 0)
          := taken (bordered (parseGrid lines) (Succ r) (Succ c)) (neighbours lines r c) (borderedBit lines (Succ r) (Succ c))
      _ = (if accessible lines r c then 1 else 0) := rewrite Nat.addOne r, Nat.addOne c

-- The parsed grid of a rectangular input is rectangular.
theorem parsedRows (lines: List Text) (w: Nat) (rect: (r: Nat) -> r < List.length lines -> Text.length (List.getOr "" r lines) = w):
    Rows w (parseGrid lines) :=
  r hr => rewrite PList.getOrMap parseLine "" r lines, List.lengthMap parseChar (Text.toList (List.getOr "" r lines)) in
    rect r (rewrite <- List.lengthMap parseLine lines in hr)

-- Part 1 is right for every rectangular grid: the printed answer is the
-- number of rolls with fewer than four rolls around them.
theorem part1Correct (lines: List Text) (w: Nat) (rect: (r: Nat) -> r < List.length lines -> Text.length (List.getOr "" r lines) = w):
    solvePart1 (parseGrid lines) = part1Spec lines :=
  match lines with
    | Nil         => rfl
    | Cons l rest =>
      let grid := parseGrid (Cons l rest)
      let gap := List.replicate w 0
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
              - List.sumBy (r => List.sumBy (c => keep (a r c) (window r c)) (List.range w)) (List.range (List.length grid))
            := rewrite List.sumRangeCongr
                 (r => List.sumBy (c => bordered (roundFrom gap gap grid) (Succ r) (Succ c)) (List.range w))
                 (r => List.sumBy (c => keep (a r c) (window r c)) (List.range w)) (List.length grid) 0
                 (r h1 h2 => List.sumByCongr (c => bordered (roundFrom gap gap grid) (Succ r) (Succ c)) (c => keep (a r c) (window r c))
                    (c => cellRound w grid rows r h2 c) (List.range w))
        _ = List.sumBy (r => List.sumBy (c => a r c - keep (a r c) (window r c)) (List.range w)) (List.range (List.length grid))
            := rewrite PList.sumBySub (r => List.sumBy (c => a r c) (List.range w)) (r => List.sumBy (c => keep (a r c) (window r c)) (List.range w))
                   (r => PList.sumByLe (c => a r c) (c => keep (a r c) (window r c)) (c => keepLe (a r c) (window r c)) (List.range w))
                   (List.range (List.length grid)) in
                 List.sumByCongr
                   (r => List.sumBy (c => a r c) (List.range w) - List.sumBy (c => keep (a r c) (window r c)) (List.range w))
                   (r => List.sumBy (c => a r c - keep (a r c) (window r c)) (List.range w))
                   (r => PList.sumBySub (c => a r c) (c => keep (a r c) (window r c)) (c => keepLe (a r c) (window r c)) (List.range w))
                   (List.range (List.length grid))
        _ = List.sumBy (r => List.sumBy (c => if accessible (Cons l rest) r c then 1 else 0) (List.range w)) (List.range (List.length grid))
            := List.sumByCongr
                 (r => List.sumBy (c => a r c - keep (a r c) (window r c)) (List.range w))
                 (r => List.sumBy (c => if accessible (Cons l rest) r c then 1 else 0) (List.range w))
                 (r => List.sumByCongr (c => a r c - keep (a r c) (window r c)) (c => if accessible (Cons l rest) r c then 1 else 0)
                    (c => takenCell (Cons l rest) r c) (List.range w))
                 (List.range (List.length grid))
        _ = part1Spec (Cons l rest)
            := rewrite List.lengthMap parseLine rest in
                 List.sumRangeCongr
                   (r => List.sumBy (c => if accessible (Cons l rest) r c then 1 else 0) (List.range w))
                   (r => List.sumBy (c => if accessible (Cons l rest) r c then 1 else 0) (List.range (Text.length (List.getOr "" r (Cons l rest)))))
                   (List.length (Cons l rest)) 0
                   (r h1 h2 => rewrite rect r h2)
