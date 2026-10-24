-- Draft of library lemmas, to move to std.

namespace Aoc.Day09.Proofs
import Std (Bool, DecEq, Decidable, Eq, Iff, List, Map, Nat, Option, Or, PrefixSums, Void)

-- The fold starts at `start` and never goes down.
theorem DList.foldMaxGe: (start: Nat) -> (xs: List Nat) -> start <= List.foldLeft Nat.max start xs
  | start, Nil => Nat.leRefl start
  | start, Cons x xs => Nat.leTrans start (Nat.max start x) (List.foldLeft Nat.max (Nat.max start x) xs) (Nat.leMaxLeft start x) (DList.foldMaxGe (Nat.max start x) xs)

-- Every element is at most the largest.
theorem DList.leFoldMax (x: Nat): (start: Nat) -> (xs: List Nat) -> List.Mem x xs -> x <= List.foldLeft Nat.max start xs
  | start, Nil, m => Void.exfalso m
  | start, Cons y ys, Inl e => rewrite <- e in Nat.leTrans y (Nat.max start y) (List.foldLeft Nat.max (Nat.max start y) ys) (Nat.leMaxRight start y) (DList.foldMaxGe (Nat.max start y) ys)
  | start, Cons y ys, Inr m => DList.leFoldMax x (Nat.max start y) ys m

-- The largest is the start or one of the elements.
theorem DList.foldMaxMem: (start: Nat) -> (xs: List Nat) -> Or (List.foldLeft Nat.max start xs = start) (List.Mem (List.foldLeft Nat.max start xs) xs)
  | start, Nil => Inl rfl
  | start, Cons y ys =>
    match DList.foldMaxMem (Nat.max start y) ys with
      | Inr m => Inr (Inr m)
      | Inl e =>
        match h: Nat.leq start y with
          | True => Inr (Inl (Eq.sym e))
          | False => Inl e

-- dedup ---------------------------------------------------------------------

-- What `List.dedupAfter` keeps was in the list.
theorem DList.memDedupAfter [auto eq: DecEq a] (x: a): (previous: a) -> (xs: List a) -> List.Mem x (List.dedupAfter previous xs) -> List.Mem x xs
  | previous, Nil, m => m
  | previous, Cons y ys, m =>
    match e: y == previous with
      | True => Inr (DList.memDedupAfter x previous ys m)
      | False =>
        match m with
          | Inl q => Inl q
          | Inr rest => Inr (DList.memDedupAfter x y ys rest)

-- And it drops only elements equal to the one before.
theorem DList.memDedupAfterIntro [auto eq: DecEq a] (x: a): (previous: a) -> (xs: List a) -> List.Mem x xs ->
    Or (previous = x) (List.Mem x (List.dedupAfter previous xs))
  | previous, Nil, m => Void.exfalso m
  | previous, Cons y ys, m =>
    match e: y == previous with
      | True =>
        match m with
          | Inl q => Inl (Eq.trans (Eq.sym (DecEq.sound y previous e)) q)
          | Inr rest => DList.memDedupAfterIntro x previous ys rest
      | False =>
        match m with
          | Inl q => Inr (Inl q)
          | Inr rest =>
            match DList.memDedupAfterIntro x y ys rest with
              | Inl q => Inr (Inl q)
              | Inr later => Inr (Inr later)

-- `List.dedup` keeps every value.
theorem DList.memDedup [auto eq: DecEq a] (x: a): (xs: List a) -> Iff (List.Mem x (List.dedup xs)) (List.Mem x xs)
  | Nil => { forward = m => m, backward = m => m }
  | Cons y ys => {
      forward = m => match m with
        | Inl q => Inl q
        | Inr rest => Inr (DList.memDedupAfter x y ys rest),
      backward = m => match m with
        | Inl q => Inl q
        | Inr rest =>
          match DList.memDedupAfterIntro x y ys rest with
            | Inl q => Inl q
            | Inr later => Inr later
    }

-- `List.dedup` keeps a list sorted.
theorem DList.sortedDedupAfter [auto eq: DecEq a] (le: a -> a -> Bool): (previous: a) -> (xs: List a) -> List.Sorted le (Cons previous xs) ->
    List.Sorted le (Cons previous (List.dedupAfter previous xs))
  | previous, Nil, s => s
  | previous, Cons y ys, Both first rest =>
    match e: y == previous with
      | True => DList.sortedDedupAfter le previous ys (rewrite DecEq.sound y previous e at rest)
      | False => Both first (DList.sortedDedupAfter le y ys rest)

theorem DList.sortedDedup [auto eq: DecEq a] (le: a -> a -> Bool): (xs: List a) -> List.Sorted le xs -> List.Sorted le (List.dedup xs)
  | Nil, s => s
  | Cons y ys, s => DList.sortedDedupAfter le y ys s

-- `x == y` is false only for different values.
theorem DList.decEqFalse [auto eq: DecEq a] (x: a) (y: a) (h: (x == y) = False) (same: x = y): Void :=
  Bool.falseNotTrue (Eq.trans (Eq.sym h) (Decidable.toBoolOf (DecEq.decide x y) same))

-- indexOf -------------------------------------------------------------------

-- The element at `x`'s position is `x`.
theorem DList.getOrIndexOf [auto eq: DecEq a] (d: a) (x: a): (xs: List a) -> List.Mem x xs -> List.getOr d (List.indexOf x xs) xs = x
  | Nil, m => Void.exfalso m
  | Cons y ys, m =>
    match e: y == x with
      | True => DecEq.sound y x e
      | False =>
        match m with
          | Inl q => Void.exfalso (DList.decEqFalse y x e q)
          | Inr rest => DList.getOrIndexOf d x ys rest

-- An element's position is inside the list.
theorem DList.indexOfLt [auto eq: DecEq a] (x: a): (xs: List a) -> List.Mem x xs -> List.indexOf x xs < List.length xs
  | Nil, m => Void.exfalso m
  | Cons y ys, m =>
    match e: y == x with
      | True => rfl
      | False =>
        match m with
          | Inl q => Void.exfalso (DList.decEqFalse y x e q)
          | Inr rest => DList.indexOfLt x ys rest

-- sorted lists by position -------------------------------------------------

-- In a sorted list of numbers, an element is at most every later one.
theorem DList.sortedGetOrLe (d: Nat): (xs: List Nat) -> List.Sorted Nat.leq xs -> (i: Nat) -> (j: Nat) -> i <= j -> j < List.length xs ->
    List.getOr d i xs <= List.getOr d j xs
  | Nil, s, i, j, h, lt => Void.exfalso (Bool.falseNotTrue lt)
  | Cons x rest, s, Zero, Zero, h, lt => Nat.leRefl x
  | Cons x Nil, s, Zero, Succ j, h, lt => Void.exfalso (Bool.falseNotTrue lt)
  | Cons x (Cons y ys), Both first s, Zero, Succ j, h, lt =>
    Nat.leTrans x y (List.getOr d j (Cons y ys)) first (DList.sortedGetOrLe d (Cons y ys) s 0 j rfl lt)
  | Cons x rest, s, Succ i, Zero, h, lt => Void.exfalso (Bool.falseNotTrue h)
  | Cons x rest, Both first s, Succ i, Succ j, h, lt => DList.sortedGetOrLe d rest s i j h lt

-- A value of a sorted list that lies between the elements at positions i and
-- j (i <= j) is the element at a position from i to j: so anything true of
-- those elements is true of it.
theorem DList.sortedBetween (d: Nat) (p: Nat -> Prop) (xs: List Nat) (s: List.Sorted Nat.leq xs) (i: Nat) (j: Nat) (ij: i <= j) (jIn: j < List.length xs)
    (each: (k: Nat) -> i <= k -> k <= j -> p (List.getOr d k xs))
    (v: Nat) (m: List.Mem v xs) (above: List.getOr d i xs <= v) (below: v <= List.getOr d j xs): p v :=
  let k := List.indexOf v xs
  let at: List.getOr d k xs = v := DList.getOrIndexOf d v xs m
  let kIn: k < List.length xs := DList.indexOfLt v xs m
  match ki: Nat.leq i k with
    | True =>
      match kj: Nat.leq k j with
        | True => rewrite <- at in each k ki kj
        -- Past j: the element at j is at most v and at least it, so v is it.
        | False =>
          let up := DList.sortedGetOrLe d xs s j k (omega) kIn
          rewrite (omega [up, at, below]: v = List.getOr d j xs) in each j ij (Nat.leRefl j)
    -- Before i: the same, at i.
    | False =>
      let down := DList.sortedGetOrLe d xs s k i (omega) (omega)
      rewrite (omega [down, at, above]: v = List.getOr d i xs) in each i (Nat.leRefl i) ij

-- Map.byPosition --------------------------------------------------------------

-- No position below `s` is numbered from `s`.
theorem DMap.lookupLastBelow (k: Nat): (s: Nat) -> (xs: List a) -> k < s -> Map.lookupLast k (List.withIndexFrom s xs) = None
  | s, Nil, h => rfl
  | s, Cons x xs, h =>
    rewrite DMap.lookupLastBelow k (Succ s) xs (omega) in
      match c: Nat.compare k s with
        | Equal => omega [Nat.compareEqual k s c]
        | Less => rfl
        | Greater => rfl

-- Position s + i of the elements numbered from s is element i.
theorem DMap.lookupLastWithIndex (d: a): (s: Nat) -> (i: Nat) -> (xs: List a) ->
    Option.getOrElse d (Map.lookupLast (s + i) (List.withIndexFrom s xs)) = List.getOr d i xs
  | s, i, Nil => rfl
  | s, Zero, Cons x xs =>
    rewrite Nat.addZero s, DMap.lookupLastBelow s (Succ s) xs (Nat.leRefl (Succ s)), DNat.compareSelf s in rfl
  | s, Succ i, Cons x xs =>
    let ih: Option.getOrElse d (Map.lookupLast (Succ (s + i)) (List.withIndexFrom (Succ s) xs)) = List.getOr d i xs :=
      DMap.lookupLastWithIndex d (Succ s) i xs
    rewrite Nat.addSucc s i in
      match r: Map.lookupLast (Succ (s + i)) (List.withIndexFrom (Succ s) xs) with
        | Some v => ih
        | None =>
          match c: Nat.compare (Succ (s + i)) s with
            | Equal => omega [Nat.compareEqual (Succ (s + i)) s c]
            | Less => ih
            | Greater => ih

-- Looking up a position in `Map.byPosition xs` is `List.getOr` on `xs`,
-- inside the list and past its end.
theorem DMap.getOrByPosition (d: a) (i: Nat) (xs: List a): Map.getOr d i (Map.byPosition xs) = List.getOr d i xs :=
  rewrite Map.getFromList i (List.withIndex xs) in DMap.lookupLastWithIndex d 0 i xs

theorem DNat.compareSelf: (n: Nat) -> Nat.compare n n = Equal
  | Zero => rfl
  | Succ n => DNat.compareSelf n

-- prefix sums -----------------------------------------------------------------

-- A sum over the first n + 1 numbers is the first term and the sum over the rest.
theorem DList.sumByRangeSucc (f: Nat -> Nat) (n: Nat): List.sumBy f (List.range (Succ n)) = f 0 + List.sumBy (i => f (Succ i)) (List.range n) :=
  rewrite List.sumByCons f 0 (List.rangeFrom n 1), List.sumByRangeShift f n 0 in rfl

-- Running sums from `start`: entry c is `start` plus the first c elements.
theorem DList.getOrScanAdd: (start: Nat) -> (row: List Nat) -> (c: Nat) -> c <= List.length row ->
    List.getOr 0 c (List.scanLeft Nat.add start row) = start + List.sumBy (i => List.getOr 0 i row) (List.range c)
  | start, Nil, Zero, h => Eq.sym (Nat.addZero start)
  | start, Nil, Succ c, h => Void.exfalso (Bool.falseNotTrue h)
  | start, Cons x xs, Zero, h => Eq.sym (Nat.addZero start)
  | start, Cons x xs, Succ c, h =>
    rewrite DList.getOrScanAdd (Nat.add start x) xs c h, DList.sumByRangeSucc (i => List.getOr 0 i (Cons x xs)) c in omega

-- Adding two rows entry by entry.
theorem DList.getOrZipWithAdd: (c: Nat) -> (u: List Nat) -> (v: List Nat) -> c < List.length u -> c < List.length v ->
    List.getOr 0 c (List.zipWith Nat.add u v) = List.getOr 0 c u + List.getOr 0 c v
  | c, Nil, v, hu, hv => Void.exfalso (Bool.falseNotTrue hu)
  | c, Cons x xs, Nil, hu, hv => Void.exfalso (Bool.falseNotTrue hv)
  | Zero, Cons x xs, Cons y ys, hu, hv => rfl
  | Succ c, Cons x xs, Cons y ys, hu, hv => DList.getOrZipWithAdd c xs ys hu hv

theorem DList.lengthZipWithAtLeast (f: a -> b -> c): (n: Nat) -> (u: List a) -> (v: List b) -> n <= List.length u -> n <= List.length v ->
    n <= List.length (List.zipWith f u v)
  | Zero, u, v, hu, hv => rfl
  | Succ n, Nil, v, hu, hv => hu
  | Succ n, Cons x xs, Nil, hu, hv => hv
  | Succ n, Cons x xs, Cons y ys, hu, hv => DList.lengthZipWithAtLeast f n xs ys hu hv

-- Element i of a mapped list, inside it.
theorem DList.getOrMapLt (f: a -> b) (d: a) (e: b): (i: Nat) -> (xs: List a) -> i < List.length xs -> List.getOr e i (List.map f xs) = f (List.getOr d i xs)
  | i, Nil, h => Void.exfalso (Bool.falseNotTrue h)
  | Zero, Cons x xs, h => rfl
  | Succ i, Cons x xs, h => DList.getOrMapLt f d e i xs h

-- Row r of the table, entry c: the entry of `above`, plus entry c of each of
-- the first r rows of sums.
theorem DPrefixSums.tableAt (c: Nat): (above: List Nat) -> (sums: List (List Nat)) -> c < List.length above ->
    ((i: Nat) -> i < List.length sums -> c < List.length (List.getOr Nil i sums)) -> (r: Nat) -> r <= List.length sums ->
    List.getOr 0 c (List.getOr Nil r (PrefixSums.table above sums)) = List.getOr 0 c above + List.sumBy (i => List.getOr 0 c (List.getOr Nil i sums)) (List.range r)
  | above, Nil, ha, hs, Zero, hr => Eq.sym (Nat.addZero (List.getOr 0 c above))
  | above, Nil, ha, hs, Succ r, hr => Void.exfalso (Bool.falseNotTrue hr)
  | above, Cons row rest, ha, hs, Zero, hr => Eq.sym (Nat.addZero (List.getOr 0 c above))
  | above, Cons row rest, ha, hs, Succ r, hr =>
    let hrow: c < List.length row := hs 0 rfl
    let next := List.zipWith Nat.add above row
    let hnext: c < List.length next := DList.lengthZipWithAtLeast Nat.add (Succ c) above row ha hrow
    rewrite DPrefixSums.tableAt c next rest hnext (i hi => hs (Succ i) hi) r hr,
      DList.getOrZipWithAdd c above row ha hrow,
      DList.sumByRangeSucc (i => List.getOr 0 c (List.getOr Nil i (Cons row rest))) r
      in omega

theorem DList.lengthScanLeft (f: b -> a -> b): (start: b) -> (xs: List a) -> List.length (List.scanLeft f start xs) = Succ (List.length xs)
  | start, Nil => rfl
  | start, Cons x xs => Eq.cong Succ (DList.lengthScanLeft f (f start x) xs)

-- Entry (r, c) of the table is the sum of the cells above row r and left of
-- column c.
theorem DPrefixSums.atOf (rows: List (List Nat)) (r: Nat) (c: Nat) (hr: r <= List.length rows) (hc: c <= List.maxLength rows):
    PrefixSums.at (PrefixSums.of rows) r c = PrefixSums.blockSpec rows 0 r 0 c :=
  let width := List.maxLength rows
  let sums := List.map (row => PrefixSums.runningSums (List.padRight width 0 row)) rows
  let top := List.replicate (Succ width) 0
  let table := PrefixSums.table top sums
  -- Row i of the sums, inside the grid.
  let sumsAt: (i: Nat) -> i < List.length rows -> List.getOr Nil i sums = PrefixSums.runningSums (List.padRight width 0 (List.getOr Nil i rows)) :=
    i hi => DList.getOrMapLt (row => PrefixSums.runningSums (List.padRight width 0 row)) Nil Nil i rows hi
  let paddedLength: (i: Nat) -> List.length (List.padRight width 0 (List.getOr Nil i rows)) = width :=
    i => List.padRightLength width 0 (List.getOr Nil i rows) (List.lengthLeMaxLength i rows)
  let sumsLength: (i: Nat) -> i < List.length sums -> c < List.length (List.getOr Nil i sums) :=
    i hi =>
      let inRows: i < List.length rows := rewrite List.lengthMap (row => PrefixSums.runningSums (List.padRight width 0 row)) rows at hi
      rewrite sumsAt i inRows, DList.lengthScanLeft Nat.add 0 (List.padRight width 0 (List.getOr Nil i rows)), paddedLength i in hc
  let topLength: c < List.length top := rewrite List.lengthReplicate 0 width in hc
  let rowSum: (i: Nat) -> 0 <= i -> i < 0 + r ->
      List.getOr 0 c (List.getOr Nil i sums) = List.sumBy (j => PrefixSums.cell rows i j) (List.rangeFrom (c - 0) 0) :=
    i lo hi =>
      rewrite sumsAt i (omega), DList.getOrScanAdd 0 (List.padRight width 0 (List.getOr Nil i rows)) c (rewrite paddedLength i in hc)
        in List.sumByCong (j => List.getOr 0 j (List.padRight width 0 (List.getOr Nil i rows))) (j => PrefixSums.cell rows i j) (List.range c)
          (j => List.getOrPadRight 0 width j (List.getOr Nil i rows))
  calc PrefixSums.at (PrefixSums.of rows) r c
    _ = Map.getOr 0 c (Map.getOr Map.empty r (Map.byPosition (List.map Map.byPosition table))) := rfl
    _ = Map.getOr 0 c (List.getOr Map.empty r (List.map Map.byPosition table)) := rewrite DMap.getOrByPosition Map.empty r (List.map Map.byPosition table)
    _ = Map.getOr 0 c (Map.byPosition (List.getOr Nil r table)) := rewrite List.getOrMap Map.byPosition Nil r table
    _ = List.getOr 0 c (List.getOr Nil r table) := DMap.getOrByPosition 0 c (List.getOr Nil r table)
    _ = List.getOr 0 c top + List.sumBy (i => List.getOr 0 c (List.getOr Nil i sums)) (List.range r) :=
      DPrefixSums.tableAt c top sums topLength sumsLength r (rewrite List.lengthMap (row => PrefixSums.runningSums (List.padRight width 0 row)) rows in hr)
    _ = List.sumBy (i => List.getOr 0 c (List.getOr Nil i sums)) (List.range r) := rewrite List.getOrReplicate 0 c (Succ width) in rfl
    _ = PrefixSums.blockSpec rows 0 r 0 c :=
      List.sumRangeCongr (i => List.getOr 0 c (List.getOr Nil i sums)) (i => List.sumBy (j => PrefixSums.cell rows i j) (List.rangeFrom (c - 0) 0)) r 0 rowSum

-- A sum over the numbers below b is the sum below t and the sum from t up to b.
theorem DList.sumByRangeSplit (f: Nat -> Nat) (t: Nat) (b: Nat) (tb: t <= b):
    List.sumBy f (List.rangeFrom b 0) = List.sumBy f (List.rangeFrom t 0) + List.sumBy f (List.rangeFrom (b - t) t) :=
  calc List.sumBy f (List.rangeFrom b 0)
    _ = List.sumBy f (List.rangeFrom (t + (b - t)) 0) := Eq.cong (n => List.sumBy f (List.rangeFrom n 0)) (Eq.sym (Nat.addSubCancel t b tb))
    _ = List.sumBy f (List.append (List.rangeFrom t 0) (List.rangeFrom (b - t) (0 + t))) := Eq.cong (List.sumBy f) (List.rangeFromAppend t (b - t) 0)
    _ = List.sumBy f (List.rangeFrom t 0) + List.sumBy f (List.rangeFrom (b - t) t) := List.sumByAppend f (List.rangeFrom t 0) (List.rangeFrom (b - t) t)

-- The block from four entries of the table is the sum of its cells.
theorem DPrefixSums.blockSum (rows: List (List Nat)) (top: Nat) (bottom: Nat) (left: Nat) (right: Nat)
    (tb: top <= bottom) (bh: bottom <= List.length rows) (lr: left <= right) (rw: right <= List.maxLength rows):
    PrefixSums.block (PrefixSums.of rows) top bottom left right = PrefixSums.blockSpec rows top bottom left right :=
  let cell := PrefixSums.cell rows
  let upTo: Nat -> Nat -> Nat := r c => List.sumBy (j => cell r j) (List.rangeFrom c 0)
  let e1 := DPrefixSums.atOf rows bottom right bh rw
  let e2 := DPrefixSums.atOf rows top left (omega) (omega)
  let e3 := DPrefixSums.atOf rows top right (omega) rw
  let e4 := DPrefixSums.atOf rows bottom left bh (omega)
  let split1 := DList.sumByRangeSplit (r => upTo r right) top bottom tb
  let split2 := DList.sumByRangeSplit (r => upTo r left) top bottom tb
  let split3: List.sumBy (r => upTo r right) (List.rangeFrom (bottom - top) top)
      = List.sumBy (r => upTo r left) (List.rangeFrom (bottom - top) top) + PrefixSums.blockSpec rows top bottom left right :=
    calc List.sumBy (r => upTo r right) (List.rangeFrom (bottom - top) top)
      _ = List.sumBy (r => upTo r left + List.sumBy (j => cell r j) (List.rangeFrom (right - left) left)) (List.rangeFrom (bottom - top) top) :=
        List.sumByCong _ _ (List.rangeFrom (bottom - top) top) (r => DList.sumByRangeSplit (j => cell r j) left right lr)
      _ = List.sumBy (r => upTo r left) (List.rangeFrom (bottom - top) top) + PrefixSums.blockSpec rows top bottom left right :=
        List.sumByAdd (r => upTo r left) (r => List.sumBy (j => cell r j) (List.rangeFrom (right - left) left)) (List.rangeFrom (bottom - top) top)
  omega

-- all over between -----------------------------------------------------------

theorem DList.allBetweenElim (q: Nat -> Bool) (lo: Nat) (hi: Nat) (h: List.all q (List.between lo hi) = True) (k: Nat) (lk: lo <= k) (kh: k <= hi): q k = True :=
  List.allRangeElim q (hi + 1 - lo) lo h k lk (omega)

theorem DList.allBetweenIntro (q: Nat -> Bool) (lo: Nat) (hi: Nat) (h: (k: Nat) -> lo <= k -> k <= hi -> q k = True): List.all q (List.between lo hi) = True :=
  List.allRangeIntro q (hi + 1 - lo) lo (k lk kh => h k lk (omega))

-- sums of zero -----------------------------------------------------------------

-- A sum of numbers is 0 only if each is.
theorem DList.sumByZeroElim (f: a -> Nat): (xs: List a) -> List.sumBy f xs = 0 -> (x: a) -> List.Mem x xs -> f x = 0
  | Nil, h, x, m => Void.exfalso m
  | Cons y ys, h, x, Inl e => rewrite <- e in omega [List.sumByCons f y ys]
  | Cons y ys, h, x, Inr m => DList.sumByZeroElim f ys (omega [List.sumByCons f y ys]) x m

theorem DList.sumByZeroIntro (f: a -> Nat): (xs: List a) -> ((x: a) -> List.Mem x xs -> f x = 0) -> List.sumBy f xs = 0
  | Nil, h => rfl
  | Cons y ys, h => rewrite List.sumByCons f y ys in omega [h y (Inl rfl), DList.sumByZeroIntro f ys (x m => h x (Inr m))]

-- filtering what can't pass anyway ------------------------------------------

-- Dropping elements that fail `q`, when only elements that pass `q` can pass
-- `p`, changes neither `any p` nor `count p`.
theorem DList.anyFilter (p: a -> Bool) (q: a -> Bool) (h: (x: a) -> p x = True -> q x = True): (xs: List a) -> List.any p (List.filter q xs) = List.any p xs
  | Nil => rfl
  | Cons x xs =>
    match e: q x with
      | True => rewrite DList.anyFilter p q h xs in rfl
      | False =>
        match f: p x with
          | True => Void.exfalso (Bool.falseNotTrue (Eq.trans (Eq.sym e) (h x f)))
          | False => DList.anyFilter p q h xs

theorem DList.countFromFilter (p: a -> Bool) (q: a -> Bool) (h: (x: a) -> p x = True -> q x = True): (n: Nat) -> (xs: List a) ->
    List.foldLeft (k x => Nat.succIf k (p x)) n (List.filter q xs) = List.foldLeft (k x => Nat.succIf k (p x)) n xs
  | n, Nil => rfl
  | n, Cons x xs =>
    match e: q x with
      | True => DList.countFromFilter p q h (Nat.succIf n (p x)) xs
      | False =>
        match f: p x with
          | True => Void.exfalso (Bool.falseNotTrue (Eq.trans (Eq.sym e) (h x f)))
          | False => DList.countFromFilter p q h n xs

theorem DList.countFilter (p: a -> Bool) (q: a -> Bool) (h: (x: a) -> p x = True -> q x = True) (xs: List a): List.count p (List.filter q xs) = List.count p xs :=
  DList.countFromFilter p q h 0 xs

-- Bools ----------------------------------------------------------------------

-- Two Bools are equal when each is true if the other is.
theorem DBool.ext: (a: Bool) -> (b: Bool) -> (a = True -> b = True) -> (b = True -> a = True) -> a = b
  | True, True, f, g => rfl
  | True, False, f, g => Eq.sym (f rfl)
  | False, True, f, g => g rfl
  | False, False, f, g => rfl
