-- Grids as lists of rows of any lengths (lines of text, say): the longest
-- row's length, and a transpose that pads every row to it first, so no
-- column loses a cell (Python's `zip_longest(*rows, fillvalue=...)`). The
-- lemmas read the result cell by cell: row r, column c of the input is row c,
-- column r of the output, `(.getOr fill c)` of row r, past the ends too.
-- A file of its own, so that programs using only the toolkit don't check
-- these.

-- The length of the longest row (0 for no rows).
def List.maxLength: List (List a) -> Nat
  | Nil => 0
  | Cons row rows => Nat.max (List.length row) (List.maxLength rows)

-- The columns of rows of any lengths, as many as the longest row is long:
-- every row is padded on the right with `fill` to that length, then
-- transposed. `[[1], [2, 3]].transposeFill 0` is `[[1, 2], [0, 3]]`.
-- (`List.transpose` stops at the first row's length instead.)
def List.transposeFill (rows: List (List a)) (fill: a): List (List a) :=
  let width := List.maxLength rows
  List.transpose (List.map rows (row => List.padRight row width fill))

-- Lemmas.

-- No row is longer than `maxLength`: row r (Nil past the last row).
theorem List.lengthLeMaxLength: (rows: List (List a)) -> (r: Nat) -> List.length (List.getOr rows Nil r) <= List.maxLength rows
  | Nil, r => rfl
  | Cons x xs, Zero => Nat.leMaxLeft (List.length x) (List.maxLength xs)
  | Cons x xs, Succ r =>
    calc List.length (List.getOr xs Nil r)
      _ <= List.maxLength xs := List.lengthLeMaxLength xs r
      _ <= Nat.max (List.length x) (List.maxLength xs) := Nat.leMaxRight (List.length x) (List.maxLength xs)

-- A row no longer than w, padded to w, is its first w cells read by index.
theorem List.padRightGetOr (row: List a) (fill: a) (w: Nat) (h: List.length row <= w):
    List.padRight row w fill = List.map (List.range w) (c => List.getOr row fill c) :=
  calc List.padRight row w fill
    _ = List.map (List.range (List.length (List.padRight row w fill))) (c => List.getOr (List.padRight row w fill) fill c)
      := Eq.sym (List.mapGetOr (List.padRight row w fill) fill)
    _ = List.map (List.range w) (c => List.getOr (List.padRight row w fill) fill c) := rewrite List.padRightLength row w fill h
    _ = List.map (List.range w) (c => List.getOr row fill c)
      := List.mapCong (List.range w) (c => List.getOr (List.padRight row w fill) fill c)
        (c => List.getOr row fill c) (c => List.getOrPadRight row fill w c)

theorem List.padRowsGetOr: (rows: List (List a)) -> (fill: a) -> (w: Nat) -> ((r: Nat) -> List.length (List.getOr rows Nil r) <= w) ->
    List.map rows (row => List.padRight row w fill) = List.map rows (row => List.map (List.range w) (c => List.getOr row fill c))
  | Nil, fill, w, h => rfl
  | Cons row rest, fill, w, h => rewrite List.padRightGetOr row fill w (h 0), List.padRowsGetOr rest fill w (r => h (Succ r))

-- The whole result, column by column: column c is `getOr fill c` of every
-- row, for c up to `maxLength`.
theorem List.transposeFillColumns: (rows: List (List a)) -> (fill: a) ->
    List.transposeFill rows fill = List.map (List.range (List.maxLength rows)) (c => List.map rows (row => List.getOr row fill c))
  | Nil, fill => rfl
  | Cons r rs, fill =>
    calc List.transpose (List.map (Cons r rs) (row => List.padRight row (List.maxLength (Cons r rs)) fill))
      _ = List.transpose (List.map (Cons r rs) (row => List.map (List.range (List.maxLength (Cons r rs))) (c => List.getOr row fill c)))
        := Eq.cong List.transpose (List.padRowsGetOr (Cons r rs) fill (List.maxLength (Cons r rs)) (i => List.lengthLeMaxLength (Cons r rs) i))
      _ = List.map (List.range (List.maxLength (Cons r rs))) (c => List.map (Cons r rs) (row => List.getOr row fill c))
        := List.transposeGrid rs r (List.range (List.maxLength (Cons r rs))) (row c => List.getOr row fill c)

-- As many columns as the longest row is long...
theorem List.lengthTransposeFill (rows: List (List a)) (fill: a): List.length (List.transposeFill rows fill) = List.maxLength rows :=
  Eq.trans (Eq.cong List.length (List.transposeFillColumns rows fill))
    (Eq.trans (List.lengthMap (List.range (List.maxLength rows)) (c => List.map rows (row => List.getOr row fill c)))
      (List.lengthRangeFrom (List.maxLength rows) 0))

-- ...and column c (c < maxLength) is `getOr fill c` of every row.
theorem List.getOrTransposeFill (rows: List (List a)) (fill: a) (c: Nat) (h: c < List.maxLength rows):
    List.getOr (List.transposeFill rows fill) Nil c = List.map rows (row => List.getOr row fill c) :=
  calc List.getOr (List.transposeFill rows fill) Nil c
    _ = List.getOr (List.map (List.range (List.maxLength rows)) (c => List.map rows (row => List.getOr row fill c))) Nil c
      := rewrite List.transposeFillColumns rows fill
    _ = List.map rows (row => List.getOr row fill (c + 0))
      := List.getOrMapRange (c => List.map rows (row => List.getOr row fill c)) Nil (List.maxLength rows) 0 c h
    _ = List.map rows (row => List.getOr row fill c) := rewrite Nat.addZero c

-- The cell lemma: row r of column c is column c of row r, read with `getOr`
-- and `fill` past the ends, at every r and c.
theorem List.transposeFillCell (rows: List (List a)) (fill: a) (c: Nat) (r: Nat):
    List.getOr (List.getOr (List.transposeFill rows fill) Nil c) fill r = List.getOr (List.getOr rows Nil r) fill c :=
  match t: Nat.leq (List.maxLength rows) c with
    | False =>
      calc List.getOr (List.getOr (List.transposeFill rows fill) Nil c) fill r
        _ = List.getOr (List.map rows (row => List.getOr row fill c)) fill r
          := rewrite List.getOrTransposeFill rows fill c (Nat.leqFalse (List.maxLength rows) c t)
        _ = List.getOr (List.getOr rows Nil r) fill c := List.getOrMap rows Nil r (row => List.getOr row fill c)
    | True =>
      calc List.getOr (List.getOr (List.transposeFill rows fill) Nil c) fill r
        _ = List.getOr Nil fill r
          := rewrite List.getOrPast (List.transposeFill rows fill) Nil c (rewrite List.lengthTransposeFill rows fill in t)
        _ = List.getOr (List.getOr rows Nil r) fill c
          := Eq.sym (List.getOrPast (List.getOr rows Nil r) fill c
            (Nat.leTrans (List.length (List.getOr rows Nil r)) (List.maxLength rows) c (List.lengthLeMaxLength rows r) t))

-- Every column is as long as the list of rows.
theorem List.lengthColumnTransposeFill (rows: List (List a)) (fill: a) (c: Nat) (h: c < List.maxLength rows):
    List.length (List.getOr (List.transposeFill rows fill) Nil c) = List.length rows :=
  rewrite List.getOrTransposeFill rows fill c h in List.lengthMap rows (row => List.getOr row fill c)

theorem List.transposeFillExample: List.transposeFill [[1], [2, 3]] 0 = [[1, 2], [0, 3]] := rfl

theorem List.maxLengthExample: List.maxLength [[1], [2, 3, 4], [5, 6]] = 3 := rfl

test "transposeFill" := [[1, 2, 3], [4], [5, 6]].transposeFill 0 == [[1, 4, 5], [2, 0, 6], [3, 0, 0]]
test "transposeFill, rectangular" := [[1, 2], [3, 4]].transposeFill 0 == [[1, 3], [2, 4]]
test "transposeFill, no rows" := (Nil: List (List Nat)).transposeFill 0 == []
test "transposeFill, empty rows" := [[], []].transposeFill 0 == ([]: List (List Nat))
test "transposeFill of characters" := [['a', 'b'], ['c']].transposeFill ' ' == [['a', 'c'], ['b', ' ']]
test "maxLength" := [[1], [2, 3, 4], [5, 6]].maxLength == 3 && (Nil: List (List Nat)).maxLength == 0
