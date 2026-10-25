-- The summed-area table is right: `PrefixSums.block` of `PrefixSums.of rows`
-- is the sum of the cells in the block (`PrefixSums.blockSum`), whenever the
-- block is inside the grid. Kept out of PrefixSums.sw because the proofs
-- need `omega`.

-- Row r of the table, entry c: the entry of `above`, plus entry c of each of
-- the first r rows of sums.
theorem PrefixSums.tableAt (c: Nat): (above: List Nat) -> (sums: List (List Nat)) -> c < List.length above ->
    ((i: Nat) -> i < List.length sums -> c < List.length (List.getOr sums Nil i)) -> (r: Nat) -> r <= List.length sums ->
    List.getOr (List.getOr (PrefixSums.table above sums) Nil r) 0 c = List.getOr above 0 c + List.sumBy (List.range r) (i => List.getOr (List.getOr sums Nil i) 0 c)
  | above, Nil, ha, hs, Zero, hr => Eq.sym (Nat.addZero (List.getOr above 0 c))
  | above, Nil, ha, hs, Succ r, hr => Void.exfalso (Bool.falseNotTrue hr)
  | above, Cons row rest, ha, hs, Zero, hr => Eq.sym (Nat.addZero (List.getOr above 0 c))
  | above, Cons row rest, ha, hs, Succ r, hr =>
    let hrow: c < List.length row := hs 0 rfl
    let next := List.zipWith above row Nat.add
    let hnext: c < List.length next := List.lengthZipWithAtLeast above (Succ c) row ha hrow Nat.add
    rewrite PrefixSums.tableAt c next rest hnext (i hi => hs (Succ i) hi) r hr,
      List.getOrZipWithAdd above c row ha hrow,
      List.sumByRangeSucc (i => List.getOr (List.getOr (Cons row rest) Nil i) 0 c) r
      in omega

-- Entry (r, c) of the table is the sum of the cells above row r and left of
-- column c.
theorem PrefixSums.atOf (rows: List (List Nat)) (r: Nat) (c: Nat) (hr: r <= List.length rows) (hc: c <= List.maxLength rows):
    PrefixSums.at (PrefixSums.of rows) r c = PrefixSums.blockSpec rows 0 r 0 c :=
  let width := List.maxLength rows
  let sums := List.map rows (row => PrefixSums.runningSums (List.padRight row width 0))
  let top := List.replicate (Succ width) 0
  let table := PrefixSums.table top sums
  -- Row i of the sums, inside the grid.
  let sumsAt: (i: Nat) -> i < List.length rows -> List.getOr sums Nil i = PrefixSums.runningSums (List.padRight (List.getOr rows Nil i) width 0) :=
    i hi => List.getOrMapLt rows Nil Nil i hi (row => PrefixSums.runningSums (List.padRight row width 0))
  let paddedLength: (i: Nat) -> List.length (List.padRight (List.getOr rows Nil i) width 0) = width :=
    i => List.padRightLength (List.getOr rows Nil i) width 0 (List.lengthLeMaxLength rows i)
  let sumsLength: (i: Nat) -> i < List.length sums -> c < List.length (List.getOr sums Nil i) :=
    i hi =>
      let inRows: i < List.length rows := rewrite List.lengthMap rows (row => PrefixSums.runningSums (List.padRight row width 0)) at hi
      rewrite sumsAt i inRows, List.lengthScanLeft (List.padRight (List.getOr rows Nil i) width 0) 0 Nat.add, paddedLength i in hc
  let topLength: c < List.length top := rewrite List.lengthReplicate 0 width in hc
  let rowSum: (i: Nat) -> 0 <= i -> i < 0 + r ->
      List.getOr (List.getOr sums Nil i) 0 c = List.sumBy (List.rangeFrom (c - 0) 0) (j => PrefixSums.cell rows i j) :=
    i lo hi =>
      rewrite sumsAt i (omega), List.getOrScanAdd (List.padRight (List.getOr rows Nil i) width 0) 0 c (rewrite paddedLength i in hc)
        in List.sumByCong (List.range c) (j => List.getOr (List.padRight (List.getOr rows Nil i) width 0) 0 j) (j => PrefixSums.cell rows i j)
          (j => List.getOrPadRight (List.getOr rows Nil i) 0 width j)
  calc PrefixSums.at (PrefixSums.of rows) r c
    _ = Map.getOr (Map.getOr (Map.byPosition (List.map table Map.byPosition)) Map.empty r) 0 c := rfl
    _ = Map.getOr (List.getOr (List.map table Map.byPosition) Map.empty r) 0 c := rewrite Map.getOrByPosition Map.empty r (List.map table Map.byPosition)
    _ = Map.getOr (Map.byPosition (List.getOr table Nil r)) 0 c := rewrite List.getOrMap table Nil r Map.byPosition
    _ = List.getOr (List.getOr table Nil r) 0 c := Map.getOrByPosition 0 c (List.getOr table Nil r)
    _ = List.getOr top 0 c + List.sumBy (List.range r) (i => List.getOr (List.getOr sums Nil i) 0 c) :=
      PrefixSums.tableAt c top sums topLength sumsLength r (rewrite List.lengthMap rows (row => PrefixSums.runningSums (List.padRight row width 0)) in hr)
    _ = List.sumBy (List.range r) (i => List.getOr (List.getOr sums Nil i) 0 c) := rewrite List.getOrReplicate 0 c (Succ width) in rfl
    _ = PrefixSums.blockSpec rows 0 r 0 c :=
      List.sumByCongRange (i => List.getOr (List.getOr sums Nil i) 0 c) (i => List.sumBy (List.rangeFrom (c - 0) 0) (j => PrefixSums.cell rows i j)) r 0 rowSum

-- The block from four entries of the table is the sum of its cells.
theorem PrefixSums.blockSum (rows: List (List Nat)) (top: Nat) (bottom: Nat) (left: Nat) (right: Nat)
    (tb: top <= bottom) (bh: bottom <= List.length rows) (lr: left <= right) (rw: right <= List.maxLength rows):
    PrefixSums.block (PrefixSums.of rows) top bottom left right = PrefixSums.blockSpec rows top bottom left right :=
  let cell := PrefixSums.cell rows
  let upTo: Nat -> Nat -> Nat := r c => List.sumBy (List.rangeFrom c 0) (j => cell r j)
  let e1 := PrefixSums.atOf rows bottom right bh rw
  let e2 := PrefixSums.atOf rows top left (omega) (omega)
  let e3 := PrefixSums.atOf rows top right (omega) rw
  let e4 := PrefixSums.atOf rows bottom left bh (omega)
  let split1 := List.sumByRangeSplit (r => upTo r right) top bottom tb
  let split2 := List.sumByRangeSplit (r => upTo r left) top bottom tb
  let split3: List.sumBy (List.rangeFrom (bottom - top) top) (r => upTo r right)
      = List.sumBy (List.rangeFrom (bottom - top) top) (r => upTo r left) + PrefixSums.blockSpec rows top bottom left right :=
    calc List.sumBy (List.rangeFrom (bottom - top) top) (r => upTo r right)
      _ = List.sumBy (List.rangeFrom (bottom - top) top) (r => upTo r left + List.sumBy (List.rangeFrom (right - left) left) (j => cell r j)) :=
        List.sumByCong (List.rangeFrom (bottom - top) top) _ _ (r => List.sumByRangeSplit (j => cell r j) left right lr)
      _ = List.sumBy (List.rangeFrom (bottom - top) top) (r => upTo r left) + PrefixSums.blockSpec rows top bottom left right :=
        List.sumByAdd (List.rangeFrom (bottom - top) top) (r => upTo r left) (r => List.sumBy (List.rangeFrom (right - left) left) (j => cell r j))
  omega
