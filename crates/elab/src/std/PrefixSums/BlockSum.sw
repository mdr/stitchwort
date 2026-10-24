-- The summed-area table is right: `PrefixSums.block` of `PrefixSums.of rows`
-- is the sum of the cells in the block (`PrefixSums.blockSum`), whenever the
-- block is inside the grid. Kept out of PrefixSums.sw because the proofs
-- need `omega`.

-- Row r of the table, entry c: the entry of `above`, plus entry c of each of
-- the first r rows of sums.
theorem PrefixSums.tableAt (c: Nat): (above: List Nat) -> (sums: List (List Nat)) -> c < List.length above ->
    ((i: Nat) -> i < List.length sums -> c < List.length (List.getOr Nil i sums)) -> (r: Nat) -> r <= List.length sums ->
    List.getOr 0 c (List.getOr Nil r (PrefixSums.table above sums)) = List.getOr 0 c above + List.sumBy (i => List.getOr 0 c (List.getOr Nil i sums)) (List.range r)
  | above, Nil, ha, hs, Zero, hr => Eq.sym (Nat.addZero (List.getOr 0 c above))
  | above, Nil, ha, hs, Succ r, hr => Void.exfalso (Bool.falseNotTrue hr)
  | above, Cons row rest, ha, hs, Zero, hr => Eq.sym (Nat.addZero (List.getOr 0 c above))
  | above, Cons row rest, ha, hs, Succ r, hr =>
    let hrow: c < List.length row := hs 0 rfl
    let next := List.zipWith Nat.add above row
    let hnext: c < List.length next := List.lengthZipWithAtLeast Nat.add (Succ c) above row ha hrow
    rewrite PrefixSums.tableAt c next rest hnext (i hi => hs (Succ i) hi) r hr,
      List.getOrZipWithAdd c above row ha hrow,
      List.sumByRangeSucc (i => List.getOr 0 c (List.getOr Nil i (Cons row rest))) r
      in omega

-- Entry (r, c) of the table is the sum of the cells above row r and left of
-- column c.
theorem PrefixSums.atOf (rows: List (List Nat)) (r: Nat) (c: Nat) (hr: r <= List.length rows) (hc: c <= List.maxLength rows):
    PrefixSums.at (PrefixSums.of rows) r c = PrefixSums.blockSpec rows 0 r 0 c :=
  let width := List.maxLength rows
  let sums := List.map (row => PrefixSums.runningSums (List.padRight width 0 row)) rows
  let top := List.replicate (Succ width) 0
  let table := PrefixSums.table top sums
  -- Row i of the sums, inside the grid.
  let sumsAt: (i: Nat) -> i < List.length rows -> List.getOr Nil i sums = PrefixSums.runningSums (List.padRight width 0 (List.getOr Nil i rows)) :=
    i hi => List.getOrMapLt (row => PrefixSums.runningSums (List.padRight width 0 row)) Nil Nil i rows hi
  let paddedLength: (i: Nat) -> List.length (List.padRight width 0 (List.getOr Nil i rows)) = width :=
    i => List.padRightLength width 0 (List.getOr Nil i rows) (List.lengthLeMaxLength i rows)
  let sumsLength: (i: Nat) -> i < List.length sums -> c < List.length (List.getOr Nil i sums) :=
    i hi =>
      let inRows: i < List.length rows := rewrite List.lengthMap (row => PrefixSums.runningSums (List.padRight width 0 row)) rows at hi
      rewrite sumsAt i inRows, List.lengthScanLeft Nat.add 0 (List.padRight width 0 (List.getOr Nil i rows)), paddedLength i in hc
  let topLength: c < List.length top := rewrite List.lengthReplicate 0 width in hc
  let rowSum: (i: Nat) -> 0 <= i -> i < 0 + r ->
      List.getOr 0 c (List.getOr Nil i sums) = List.sumBy (j => PrefixSums.cell rows i j) (List.rangeFrom (c - 0) 0) :=
    i lo hi =>
      rewrite sumsAt i (omega), List.getOrScanAdd 0 (List.padRight width 0 (List.getOr Nil i rows)) c (rewrite paddedLength i in hc)
        in List.sumByCong (j => List.getOr 0 j (List.padRight width 0 (List.getOr Nil i rows))) (j => PrefixSums.cell rows i j) (List.range c)
          (j => List.getOrPadRight 0 width j (List.getOr Nil i rows))
  calc PrefixSums.at (PrefixSums.of rows) r c
    _ = Map.getOr 0 c (Map.getOr Map.empty r (Map.byPosition (List.map Map.byPosition table))) := rfl
    _ = Map.getOr 0 c (List.getOr Map.empty r (List.map Map.byPosition table)) := rewrite Map.getOrByPosition Map.empty r (List.map Map.byPosition table)
    _ = Map.getOr 0 c (Map.byPosition (List.getOr Nil r table)) := rewrite List.getOrMap Map.byPosition Nil r table
    _ = List.getOr 0 c (List.getOr Nil r table) := Map.getOrByPosition 0 c (List.getOr Nil r table)
    _ = List.getOr 0 c top + List.sumBy (i => List.getOr 0 c (List.getOr Nil i sums)) (List.range r) :=
      PrefixSums.tableAt c top sums topLength sumsLength r (rewrite List.lengthMap (row => PrefixSums.runningSums (List.padRight width 0 row)) rows in hr)
    _ = List.sumBy (i => List.getOr 0 c (List.getOr Nil i sums)) (List.range r) := rewrite List.getOrReplicate 0 c (Succ width) in rfl
    _ = PrefixSums.blockSpec rows 0 r 0 c :=
      List.sumByCongRange (i => List.getOr 0 c (List.getOr Nil i sums)) (i => List.sumBy (j => PrefixSums.cell rows i j) (List.rangeFrom (c - 0) 0)) r 0 rowSum

-- The block from four entries of the table is the sum of its cells.
theorem PrefixSums.blockSum (rows: List (List Nat)) (top: Nat) (bottom: Nat) (left: Nat) (right: Nat)
    (tb: top <= bottom) (bh: bottom <= List.length rows) (lr: left <= right) (rw: right <= List.maxLength rows):
    PrefixSums.block (PrefixSums.of rows) top bottom left right = PrefixSums.blockSpec rows top bottom left right :=
  let cell := PrefixSums.cell rows
  let upTo: Nat -> Nat -> Nat := r c => List.sumBy (j => cell r j) (List.rangeFrom c 0)
  let e1 := PrefixSums.atOf rows bottom right bh rw
  let e2 := PrefixSums.atOf rows top left (omega) (omega)
  let e3 := PrefixSums.atOf rows top right (omega) rw
  let e4 := PrefixSums.atOf rows bottom left bh (omega)
  let split1 := List.sumByRangeSplit (r => upTo r right) top bottom tb
  let split2 := List.sumByRangeSplit (r => upTo r left) top bottom tb
  let split3: List.sumBy (r => upTo r right) (List.rangeFrom (bottom - top) top)
      = List.sumBy (r => upTo r left) (List.rangeFrom (bottom - top) top) + PrefixSums.blockSpec rows top bottom left right :=
    calc List.sumBy (r => upTo r right) (List.rangeFrom (bottom - top) top)
      _ = List.sumBy (r => upTo r left + List.sumBy (j => cell r j) (List.rangeFrom (right - left) left)) (List.rangeFrom (bottom - top) top) :=
        List.sumByCong _ _ (List.rangeFrom (bottom - top) top) (r => List.sumByRangeSplit (j => cell r j) left right lr)
      _ = List.sumBy (r => upTo r left) (List.rangeFrom (bottom - top) top) + PrefixSums.blockSpec rows top bottom left right :=
        List.sumByAdd (r => upTo r left) (r => List.sumBy (j => cell r j) (List.rangeFrom (right - left) left)) (List.rangeFrom (bottom - top) top)
  omega
