-- Grids as lists of rows of any lengths (lines of text, say): the longest
-- row's length, and a transpose that pads every row to it first, so no
-- column loses a cell (Python's `zip_longest(*rows, fillvalue=...)`). The
-- lemmas read the result cell by cell: row r, column c of the input is row c,
-- column r of the output, `(.getOr c fill)` of row r, past the ends too.
-- And every cell with its row and column (`gridCells`). A file of its own,
-- so that programs using only the toolkit don't check these.

-- Every cell with its row and column, counting from 0, row by row:
-- `[['a', 'b'], ['c']].gridCells` is `[((0, 0), 'a'), ((0, 1), 'b'), ((1, 0), 'c')]`.
def List.gridCells (rows: List (List a)): List ((Nat, Nat), a) :=
  rows.withIndex |> .flatMap (((row, cells)) => cells.withIndex |> .map (((column, cell)) => ((row, column), cell)))

-- What `get` finds is somewhere in the list.
theorem List.getOfMem: (xs: List a) → (x: a) → x ∈ xs → ∃ (k: Nat) => List.get xs k = Some x
  | Nil, x, member => Void.exfalso member
  | Cons first rest, x, Inl same => Witness Zero (rewrite same in rfl)
  | Cons first rest, x, Inr later =>
    match List.getOfMem rest x later with
      | Witness k found => Witness (Succ k) found

-- `withIndex` pairs `x` with `i` exactly when `x` is element `i`.
theorem List.memWithIndex (xs: List a) (i: Nat) (x: a): Iff ((i, x) ∈ xs.withIndex) (List.get xs i = Some x) := {
  forward = member =>
    match List.getOfMem xs.withIndex (i, x) member with
      | Witness k found =>
        match c: List.get xs k with
          | None => Void.exfalso (Option.noneNotSome (i, x) (rewrite List.getWithIndex xs k, c at found))
          | Some y =>
            let same: (k, y) = (i, x) := Option.someInjective (k, y) (i, x) (rewrite List.getWithIndex xs k, c at found)
            rewrite <- Eq.cong Pair.fst same, <- Eq.cong Pair.snd same in c,
  backward = found => List.memOfGet xs.withIndex i (i, x) (rewrite List.getWithIndex xs i, found in rfl)
}

-- A grid has `cell` at `(row, column)` exactly when row `row` is some list
-- of cells whose element `column` is `cell`.
theorem List.memGridCells (rows: List (List a)) (row: Nat) (column: Nat) (cell: a):
    Iff (((row, column), cell) ∈ rows.gridCells) (∃ (cells: List a) => List.get rows row = Some cells ∧ List.get cells column = Some cell) := {
  forward = member =>
    List.anyElim _ _ rows.withIndex (List.memFlatMapElim _ ((row, column), cell) rows.withIndex member)
      (pair inRows inCells =>
        match pair with
          | (r, cells) =>
            List.anyElim _ _ cells.withIndex (List.memMapAny cells.withIndex _ ((row, column), cell) inCells)
              (entry inColumns same =>
                match entry with
                  | (c, x) =>
                    let rowSame: r = row := Eq.cong (e => e.fst.fst) same
                    let columnSame: c = column := Eq.cong (e => e.fst.snd) same
                    let cellSame: x = cell := Eq.cong Pair.snd same
                    Witness cells
                      (Both (rewrite <- rowSame in (List.memWithIndex rows r cells).forward inRows)
                        (rewrite <- columnSame, <- cellSame in (List.memWithIndex cells c x).forward inColumns)))),
  backward = found =>
    match found with
      | Witness cells (Both rowFound cellFound) =>
        List.memFlatMapIntro _ (row, cells) ((row, column), cell) rows.withIndex ((List.memWithIndex rows row cells).backward rowFound)
          (List.memMap cells.withIndex (column, cell) ((List.memWithIndex cells column cell).backward cellFound)
            ((entry: (Nat, a)) => ((row, entry.fst), entry.snd)))
}

test "gridCells" :=
  [['a', 'b'], ['c']].gridCells == [((0, 0), 'a'), ((0, 1), 'b'), ((1, 0), 'c')]
    ∧ (Nil: List (List Nat)).gridCells == [] ∧ [[], [7]].gridCells == [((1, 0), 7)]

-- The length of the longest row (0 for no rows). A right fold, so it runs
-- as a loop (stack-safe on many rows); `List.maxLengthCons` is its step.
def List.maxLength (rows: List (List a)): Nat := rows.foldRight 0 (row m => Nat.max row.length m)

theorem List.maxLengthCons (rows: List (List a)) (row: List a): List.maxLength (Cons row rows) = Nat.max (List.length row) (List.maxLength rows) :=
  List.foldRightCons rows row 0 (r m => Nat.max (List.length r) m)

-- The columns of rows of any lengths, as many as the longest row is long:
-- every row is padded on the right with `fill` to that length, then
-- transposed. `[[1], [2, 3]].transposeFill 0` is `[[1, 2], [0, 3]]`.
-- (`List.transpose` stops at the first row's length instead.)
def List.transposeFill (rows: List (List a)) (fill: a): List (List a) :=
  let width := rows.maxLength
  rows.map (row => row.padRight width fill) |> List.transpose

-- Lemmas.

-- No row is longer than `maxLength`: row r (Nil past the last row).
theorem List.lengthLeMaxLength: (rows: List (List a)) → (r: Nat) → List.length (List.getOr rows r Nil) ≤ List.maxLength rows
  | Nil, r => rfl
  | Cons x xs, Zero => rewrite List.maxLengthCons xs x in Nat.leMaxLeft (List.length x) (List.maxLength xs)
  | Cons x xs, Succ r =>
    calc List.length (List.getOr xs r Nil)
      _ ≤ List.maxLength xs := List.lengthLeMaxLength xs r
      _ ≤ Nat.max (List.length x) (List.maxLength xs) := Nat.leMaxRight (List.length x) (List.maxLength xs)
      _ = List.maxLength (Cons x xs) := Eq.sym (List.maxLengthCons xs x)

-- A row no longer than w, padded to w, is its first w cells read by index.
theorem List.padRightGetOr (row: List a) (fill: a) (w: Nat) (h: List.length row ≤ w):
    List.padRight row w fill = List.map (List.range w) (c => List.getOr row c fill) :=
  calc List.padRight row w fill
    _ = List.map (List.range (List.length (List.padRight row w fill))) (c => List.getOr (List.padRight row w fill) c fill)
      := Eq.sym (List.mapGetOr (List.padRight row w fill) fill)
    _ = List.map (List.range w) (c => List.getOr (List.padRight row w fill) c fill) := rewrite List.padRightLength row w fill h
    _ = List.map (List.range w) (c => List.getOr row c fill)
      := List.mapCong (List.range w) (c => List.getOr (List.padRight row w fill) c fill)
        (c => List.getOr row c fill) (c => List.getOrPadRight row fill w c)

theorem List.padRowsGetOr: (rows: List (List a)) → (fill: a) → (w: Nat) → ((r: Nat) → List.length (List.getOr rows r Nil) ≤ w) →
    List.map rows (row => List.padRight row w fill) = List.map rows (row => List.map (List.range w) (c => List.getOr row c fill))
  | Nil, fill, w, h => rfl
  | Cons row rest, fill, w, h => rewrite List.padRightGetOr row fill w (h 0), List.padRowsGetOr rest fill w (r => h (Succ r))

-- The whole result, column by column: column c is `getOr c fill` of every
-- row, for c up to `maxLength`.
theorem List.transposeFillColumns: (rows: List (List a)) → (fill: a) →
    List.transposeFill rows fill = List.map (List.range (List.maxLength rows)) (c => List.map rows (row => List.getOr row c fill))
  | Nil, fill => rfl
  | Cons r rs, fill =>
    calc List.transpose (List.map (Cons r rs) (row => List.padRight row (List.maxLength (Cons r rs)) fill))
      _ = List.transpose (List.map (Cons r rs) (row => List.map (List.range (List.maxLength (Cons r rs))) (c => List.getOr row c fill)))
        := Eq.cong List.transpose (List.padRowsGetOr (Cons r rs) fill (List.maxLength (Cons r rs)) (i => List.lengthLeMaxLength (Cons r rs) i))
      _ = List.map (List.range (List.maxLength (Cons r rs))) (c => List.map (Cons r rs) (row => List.getOr row c fill))
        := List.transposeGrid rs r (List.range (List.maxLength (Cons r rs))) (row c => List.getOr row c fill)

-- As many columns as the longest row is long...
theorem List.lengthTransposeFill (rows: List (List a)) (fill: a): List.length (List.transposeFill rows fill) = List.maxLength rows :=
  Eq.trans (Eq.cong List.length (List.transposeFillColumns rows fill))
    (Eq.trans (List.lengthMap (List.range (List.maxLength rows)) (c => List.map rows (row => List.getOr row c fill)))
      (List.lengthRangeFrom (List.maxLength rows) 0))

-- ...and column c (c < maxLength) is `getOr c fill` of every row.
theorem List.getOrTransposeFill (rows: List (List a)) (fill: a) (c: Nat) (h: c < List.maxLength rows):
    List.getOr (List.transposeFill rows fill) c Nil = List.map rows (row => List.getOr row c fill) :=
  calc List.getOr (List.transposeFill rows fill) c Nil
    _ = List.getOr (List.map (List.range (List.maxLength rows)) (c => List.map rows (row => List.getOr row c fill))) c Nil
      := rewrite List.transposeFillColumns rows fill
    _ = List.map rows (row => List.getOr row (c + 0) fill)
      := List.getOrMapRange (c => List.map rows (row => List.getOr row c fill)) Nil (List.maxLength rows) 0 c h
    _ = List.map rows (row => List.getOr row c fill) := rewrite Nat.addZero c

-- The cell lemma: row r of column c is column c of row r, read with `getOr`
-- and `fill` past the ends, at every r and c.
theorem List.transposeFillCell (rows: List (List a)) (fill: a) (c: Nat) (r: Nat):
    List.getOr (List.getOr (List.transposeFill rows fill) c Nil) r fill = List.getOr (List.getOr rows r Nil) c fill :=
  match t: Nat.leq (List.maxLength rows) c with
    | False =>
      calc List.getOr (List.getOr (List.transposeFill rows fill) c Nil) r fill
        _ = List.getOr (List.map rows (row => List.getOr row c fill)) r fill
          := rewrite List.getOrTransposeFill rows fill c (Nat.leqFalse (List.maxLength rows) c t)
        _ = List.getOr (List.getOr rows r Nil) c fill := List.getOrMap rows r Nil (row => List.getOr row c fill)
    | True =>
      calc List.getOr (List.getOr (List.transposeFill rows fill) c Nil) r fill
        _ = List.getOr Nil r fill
          := rewrite List.getOrPast (List.transposeFill rows fill) c Nil (rewrite List.lengthTransposeFill rows fill in t)
        _ = List.getOr (List.getOr rows r Nil) c fill
          := Eq.sym (List.getOrPast (List.getOr rows r Nil) c fill
            (Nat.leTrans (List.length (List.getOr rows r Nil)) (List.maxLength rows) c (List.lengthLeMaxLength rows r) t))

-- Every column is as long as the list of rows.
theorem List.lengthColumnTransposeFill (rows: List (List a)) (fill: a) (c: Nat) (h: c < List.maxLength rows):
    List.length (List.getOr (List.transposeFill rows fill) c Nil) = List.length rows :=
  rewrite List.getOrTransposeFill rows fill c h in List.lengthMap rows (row => List.getOr row c fill)

theorem List.transposeFillExample: List.transposeFill [[1], [2, 3]] 0 = [[1, 2], [0, 3]] := rfl

theorem List.maxLengthExample: List.maxLength [[1], [2, 3, 4], [5, 6]] = 3 := rfl

test "transposeFill" := [[1, 2, 3], [4], [5, 6]].transposeFill 0 == [[1, 4, 5], [2, 0, 6], [3, 0, 0]]
test "transposeFill, rectangular" := [[1, 2], [3, 4]].transposeFill 0 == [[1, 3], [2, 4]]
test "transposeFill, no rows" := (Nil: List (List Nat)).transposeFill 0 == []
test "transposeFill, empty rows" := [[], []].transposeFill 0 == ([]: List (List Nat))
test "transposeFill of characters" := [['a', 'b'], ['c']].transposeFill ' ' == [['a', 'c'], ['b', ' ']]
test "maxLength" := [[1], [2, 3, 4], [5, 6]].maxLength == 3 ∧ (Nil: List (List Nat)).maxLength == 0
