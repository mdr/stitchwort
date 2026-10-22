-- Grids as lists of rows of any lengths (lines of text, say): the longest
-- row's length, and a transpose that pads every row to it first, so no
-- column loses a cell (Python's `zip_longest(*rows, fillvalue=...)`). The
-- lemmas read the result cell by cell: row r, column c of the input is row c,
-- column r of the output, `List.getOr fill c` of row r, past the ends too.
-- A file of its own, so that programs using only the toolkit don't check
-- these.

-- The length of the longest row (0 for no rows).
def List.maxLength: List (List a) -> Nat
  | Nil       => 0
  | Cons r rs => Nat.max (List.length r) (List.maxLength rs)

-- The columns of rows of any lengths, as many as the longest row is long:
-- every row is padded on the right with `fill` to that length, then
-- transposed. `[[1], [2, 3]].transposeFill 0` is `[[1, 2], [0, 3]]`.
-- (`List.transpose` stops at the first row's length instead.)
def List.transposeFill (fill: a) (rows: List (List a)): List (List a) :=
  let width := List.maxLength rows
  List.transpose (List.map (row => List.padRight width fill row) rows)

-- Lemmas.

-- No row is longer than `maxLength`: row r (Nil past the last row).
theorem List.lengthLeMaxLength: (r: Nat) -> (rows: List (List a)) -> List.length (List.getOr Nil r rows) <= List.maxLength rows
  | r,      Nil       => rfl
  | Zero,   Cons x xs => Nat.leMaxLeft (List.length x) (List.maxLength xs)
  | Succ r, Cons x xs =>
    calc List.length (List.getOr Nil r xs)
      _ <= List.maxLength xs                             := List.lengthLeMaxLength r xs
      _ <= Nat.max (List.length x) (List.maxLength xs)   := Nat.leMaxRight (List.length x) (List.maxLength xs)

-- A row no longer than w, padded to w, is its first w cells read by index.
theorem List.padRightGetOr (fill: a) (w: Nat) (row: List a) (h: List.length row <= w):
    List.padRight w fill row = List.map (c => List.getOr fill c row) (List.range w) :=
  calc List.padRight w fill row
    _ = List.map (c => List.getOr fill c (List.padRight w fill row)) (List.range (List.length (List.padRight w fill row)))
        := Eq.sym (List.mapGetOr fill (List.padRight w fill row))
    _ = List.map (c => List.getOr fill c (List.padRight w fill row)) (List.range w) := rewrite List.padRightLength w fill row h
    _ = List.map (c => List.getOr fill c row) (List.range w)
        := List.mapCong (c => List.getOr fill c (List.padRight w fill row)) (c => List.getOr fill c row)
             (List.range w) (c => List.getOrPadRight fill w c row)

theorem List.padRowsGetOr (fill: a) (w: Nat): (rows: List (List a)) -> ((r: Nat) -> List.length (List.getOr Nil r rows) <= w) ->
    List.map (row => List.padRight w fill row) rows = List.map (row => List.map (c => List.getOr fill c row) (List.range w)) rows
  | Nil,           h => rfl
  | Cons row rest, h => rewrite List.padRightGetOr fill w row (h 0), List.padRowsGetOr fill w rest (r => h (Succ r))

-- The whole result, column by column: column c is `getOr fill c` of every
-- row, for c up to `maxLength`.
theorem List.transposeFillColumns (fill: a): (rows: List (List a)) ->
    List.transposeFill fill rows = List.map (c => List.map (row => List.getOr fill c row) rows) (List.range (List.maxLength rows))
  | Nil       => rfl
  | Cons r rs =>
    calc List.transpose (List.map (row => List.padRight (List.maxLength (Cons r rs)) fill row) (Cons r rs))
      _ = List.transpose (List.map (row => List.map (c => List.getOr fill c row) (List.range (List.maxLength (Cons r rs)))) (Cons r rs))
          := Eq.cong List.transpose (List.padRowsGetOr fill (List.maxLength (Cons r rs)) (Cons r rs) (i => List.lengthLeMaxLength i (Cons r rs)))
      _ = List.map (c => List.map (row => List.getOr fill c row) (Cons r rs)) (List.range (List.maxLength (Cons r rs)))
          := List.transposeGrid (row c => List.getOr fill c row) r rs (List.range (List.maxLength (Cons r rs)))

-- As many columns as the longest row is long...
theorem List.lengthTransposeFill (fill: a) (rows: List (List a)): List.length (List.transposeFill fill rows) = List.maxLength rows :=
  Eq.trans (Eq.cong List.length (List.transposeFillColumns fill rows))
    (Eq.trans (List.lengthMap (c => List.map (row => List.getOr fill c row) rows) (List.range (List.maxLength rows)))
      (List.lengthRangeFrom (List.maxLength rows) 0))

-- ...and column c (c < maxLength) is `getOr fill c` of every row.
theorem List.getOrTransposeFill (fill: a) (rows: List (List a)) (c: Nat) (h: c < List.maxLength rows):
    List.getOr Nil c (List.transposeFill fill rows) = List.map (row => List.getOr fill c row) rows :=
  calc List.getOr Nil c (List.transposeFill fill rows)
    _ = List.getOr Nil c (List.map (c => List.map (row => List.getOr fill c row) rows) (List.range (List.maxLength rows)))
        := rewrite List.transposeFillColumns fill rows
    _ = List.map (row => List.getOr fill (c + 0) row) rows
        := List.getOrMapRange (c => List.map (row => List.getOr fill c row) rows) Nil (List.maxLength rows) 0 c h
    _ = List.map (row => List.getOr fill c row) rows := rewrite Nat.addZero c

-- The cell lemma: row r of column c is column c of row r, read with `getOr`
-- and `fill` past the ends, at every r and c.
theorem List.transposeFillCell (fill: a) (rows: List (List a)) (c: Nat) (r: Nat):
    List.getOr fill r (List.getOr Nil c (List.transposeFill fill rows)) = List.getOr fill c (List.getOr Nil r rows) :=
  match t: Nat.leq (List.maxLength rows) c with
    | False =>
      calc List.getOr fill r (List.getOr Nil c (List.transposeFill fill rows))
        _ = List.getOr fill r (List.map (row => List.getOr fill c row) rows)
            := rewrite List.getOrTransposeFill fill rows c (Nat.leqFalse (List.maxLength rows) c t)
        _ = List.getOr fill c (List.getOr Nil r rows) := List.getOrMap (row => List.getOr fill c row) Nil r rows
    | True =>
      calc List.getOr fill r (List.getOr Nil c (List.transposeFill fill rows))
        _ = List.getOr fill r Nil
            := rewrite List.getOrPast Nil c (List.transposeFill fill rows) (rewrite List.lengthTransposeFill fill rows in t)
        _ = List.getOr fill c (List.getOr Nil r rows)
            := Eq.sym (List.getOrPast fill c (List.getOr Nil r rows)
                 (Nat.leTrans (List.length (List.getOr Nil r rows)) (List.maxLength rows) c (List.lengthLeMaxLength r rows) t))

-- Every column is as long as the list of rows.
theorem List.lengthColumnTransposeFill (fill: a) (rows: List (List a)) (c: Nat) (h: c < List.maxLength rows):
    List.length (List.getOr Nil c (List.transposeFill fill rows)) = List.length rows :=
  rewrite List.getOrTransposeFill fill rows c h in List.lengthMap (row => List.getOr fill c row) rows

theorem List.transposeFillExample: List.transposeFill 0 [[1], [2, 3]] = [[1, 2], [0, 3]] := rfl

theorem List.maxLengthExample: List.maxLength [[1], [2, 3, 4], [5, 6]] = 3 := rfl

test "transposeFill" := [[1, 2, 3], [4], [5, 6]].transposeFill 0 == [[1, 4, 5], [2, 0, 6], [3, 0, 0]]
test "transposeFill, rectangular" := [[1, 2], [3, 4]].transposeFill 0 == [[1, 3], [2, 4]]
test "transposeFill, no rows" := (Nil: List (List Nat)).transposeFill 0 == []
test "transposeFill, empty rows" := [[], []].transposeFill 0 == ([]: List (List Nat))
test "transposeFill of characters" := [['a', 'b'], ['c']].transposeFill ' ' == [['a', 'c'], ['b', ' ']]
test "maxLength" := [[1], [2, 3, 4], [5, 6]].maxLength == 3 && (Nil: List (List Nat)).maxLength == 0
