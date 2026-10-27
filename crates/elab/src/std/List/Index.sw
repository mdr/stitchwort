-- Lists by index: `List.getOr` (the element at an index, with a default) and
-- its lemmas for append, take, a block written n times, and equality by
-- index. A file of its own, so that programs using only the toolkit don't
-- check these.

-- The element at index i, or `fallback` past the end.
def List.getOr: List a → Nat → (fallback: a) → a
  | Nil, i, fallback => fallback
  | Cons x xs, Zero, fallback => x
  | Cons x xs, Succ i, fallback => List.getOr xs i fallback

theorem List.getOrExample: List.getOr [7, 8] 1 0 = 8 := rfl

theorem List.getOrAppendLeft: (xs: List a) → (i: Nat) → (d: a) → (ys: List a) → i < List.length xs →
    List.getOr (List.append xs ys) i d = List.getOr xs i d
  | Nil, i, d, ys, h => Void.exfalso (Bool.falseNotTrue h)
  | Cons x xs, Zero, d, ys, h => rfl
  | Cons x xs, Succ i, d, ys, h => List.getOrAppendLeft xs i d ys h

theorem List.getOrAppendRight: (xs: List a) → (i: Nat) → (d: a) → (ys: List a) → List.length xs ≤ i →
    List.getOr (List.append xs ys) i d = List.getOr ys (i - List.length xs) d
  | Nil, i, d, ys, h => rfl
  | Cons x xs, Zero, d, ys, h => Void.exfalso (Bool.falseNotTrue h)
  | Cons x xs, Succ i, d, ys, h => List.getOrAppendRight xs i d ys h

theorem List.getOrTake: (xs: List a) → (k: Nat) → (i: Nat) → (d: a) → i < k → List.getOr (List.take xs k) i d = List.getOr xs i d
  | xs, Zero, i, d, h => Void.exfalso (Bool.falseNotTrue h)
  | Nil, Succ k, i, d, h => rfl
  | Cons x xs, Succ k, Zero, d, h => rfl
  | Cons x xs, Succ k, Succ i, d, h => List.getOrTake xs k i d h

-- `getOr` is `List.get` with the fallback for `None` (`List.get`'s lemmas
-- are in Toolkit.sw) ...
theorem List.getOrGet: (xs: List a) → (k: Nat) → (d: a) → List.getOr xs k d = Option.getOrElse (List.get xs k) d
  | Nil, k, d => rfl
  | Cons x xs, Zero, d => rfl
  | Cons x xs, Succ k, d => List.getOrGet xs k d

-- ... so what `get` finds, `getOr` gives, whatever the fallback ...
theorem List.getOrOfGet: (xs: List a) → (k: Nat) → (d: a) → (v: a) → List.get xs k = Some v → List.getOr xs k d = v
  | Nil, k, d, v, h => Void.exfalso (Option.noneNotSome v h)
  | Cons x xs, Zero, d, v, h => Option.someInjective x v h
  | Cons x xs, Succ k, d, v, h => List.getOrOfGet xs k d v h

-- ... and within the list, `get` finds what `getOr` gives.
theorem List.getOfGetOr: (xs: List a) → (k: Nat) → (d: a) → k < List.length xs → List.get xs k = Some (List.getOr xs k d)
  | Nil, k, d, h => Void.exfalso (Bool.falseNotTrue h)
  | Cons x xs, Zero, d, h => rfl
  | Cons x xs, Succ k, d, h => List.getOfGetOr xs k d h

theorem List.getOrOfGetExample (xs: List Nat) (k: Nat) (v: Nat) (h: List.get xs k = Some v): List.getOr xs k 0 = List.getOr xs k 1 :=
  Eq.trans (List.getOrOfGet xs k 0 v h) (Eq.sym (List.getOrOfGet xs k 1 v h))

-- Lists of the same length that agree at every index are equal.
theorem List.extGetOr (d: a): (xs: List a) → (ys: List a) → List.length xs = List.length ys →
    ((i: Nat) → i < List.length xs → List.getOr xs i d = List.getOr ys i d) → xs = ys
  | Nil, Nil, e, h => rfl
  | Nil, Cons y ys, e, h => Void.exfalso (Nat.zeroNotSucc (List.length ys) e)
  | Cons x xs, Nil, e, h => Void.exfalso (Nat.succNotZero (List.length xs) e)
  | Cons x xs, Cons y ys, e, h =>
    Eq.trans (Eq.cong (z => Cons z xs) (h 0 rfl))
      (Eq.cong (Cons y) (List.extGetOr d xs ys (Nat.succInjective (List.length xs) (List.length ys) e) (i hi => h (Succ i) hi)))

-- Index i of a block of k elements written n times is index `i % k` of the block.
theorem List.getOrConcatReplicate (b: List a) (d: a) (k: Nat) [auto hk: k ≠ 0] (hb: List.length b = k): (n: Nat) → (i: Nat) → i < n * k →
    List.getOr (List.concat (List.replicate n b)) i d = List.getOr b (i % k) d
  | Zero, i, h => Void.exfalso (Bool.falseNotTrue h)
  | Succ n, i, h =>
    match t: Nat.leq k i with
      | False =>
        calc List.getOr (List.append b (List.concat (List.replicate n b))) i d
          _ = List.getOr b i d := List.getOrAppendLeft b i d (List.concat (List.replicate n b)) (Nat.ltCongRight i k (List.length b) (Eq.sym hb) (Nat.leqFalse k i t))
          _ = List.getOr b (i % k) d := Eq.cong (y => List.getOr b y d) (Eq.sym (Nat.modSmall i k (Nat.leqFalse k i t)))
      | True =>
        calc List.getOr (List.append b (List.concat (List.replicate n b))) i d
          _ = List.getOr (List.concat (List.replicate n b)) (i - List.length b) d
            := List.getOrAppendRight b i d (List.concat (List.replicate n b)) (Nat.leCongLeft k (List.length b) i (Eq.sym hb) t)
          _ = List.getOr (List.concat (List.replicate n b)) (i - k) d := Eq.cong (y => List.getOr (List.concat (List.replicate n b)) (i - y) d) hb
          _ = List.getOr b ((i - k) % k) d
            := List.getOrConcatReplicate b d k hb n (i - k) (Nat.subLtAdd i k (n * k) t (Nat.ltCongRight i (k + n * k) (n * k + k) (Nat.addComm k (n * k)) h))
          _ = List.getOr b (i % k) d
            := Eq.cong (y => List.getOr b y d) (Eq.trans (Eq.sym (Nat.addModSelf k (i - k))) (Eq.cong (y => y % k) (Nat.addSubCancel k i t)))

-- `getOr` past the end and after padding, and a list read off by index.
theorem List.getOrReplicate (x: a): (i: Nat) → (n: Nat) → List.getOr (List.replicate n x) i x = x
  | i, Zero => rfl
  | Zero, Succ n => rfl
  | Succ i, Succ n => List.getOrReplicate x i n

-- Copies of the default on the end change no index.
theorem List.getOrAppendReplicate: (xs: List a) → (x: a) → (k: Nat) → (i: Nat) → List.getOr (List.append xs (List.replicate k x)) i x = List.getOr xs i x
  | Nil, x, k, i => List.getOrReplicate x i k
  | Cons y ys, x, k, Zero => rfl
  | Cons y ys, x, k, Succ i => List.getOrAppendReplicate ys x k i

theorem List.getOrPadRight (xs: List a) (x: a) (n: Nat) (i: Nat): List.getOr (List.padRight xs n x) i x = List.getOr xs i x :=
  List.getOrAppendReplicate xs x (n - List.length xs) i

-- Past the end, the default.
theorem List.getOrPast: (xs: List a) → (i: Nat) → (d: a) → List.length xs ≤ i → List.getOr xs i d = d
  | Nil, i, d, h => rfl
  | Cons x xs, Zero, d, h => Void.exfalso (Bool.falseNotTrue h)
  | Cons x xs, Succ i, d, h => List.getOrPast xs i d h

-- A list is its elements read off by index.
theorem List.mapGetOr: (xs: List a) → (d: a) → List.map (List.range (List.length xs)) (i => List.getOr xs i d) = xs
  | Nil, d => rfl
  | Cons x xs, d =>
    calc List.map (List.rangeFrom (Succ (List.length xs)) 0) (i => List.getOr (Cons x xs) i d)
      _ = Cons x (List.map (List.rangeFrom (List.length xs) 1) (i => List.getOr (Cons x xs) i d))
      _ = Cons x (List.map (List.rangeFrom (List.length xs) 0) (i => List.getOr xs i d))
        := rewrite List.mapRangeShift (i => List.getOr (Cons x xs) i d) (List.length xs) 0
      _ = Cons x xs := rewrite List.mapGetOr xs d

-- `headOr` is index 0; `getOr` of a `map` and of a `zipWith3`; a sum over a
-- list as a sum over its indices.
theorem List.headOrGetOr: (xs: List a) → (d: a) → List.headOr xs d = List.getOr xs 0 d
  | Nil, d => rfl
  | Cons x xs, d => rfl

theorem List.getOrZipWith3 (f: a → b → c → e) (d1: a) (d2: b) (d3: c) (d: e) (hd: f d1 d2 d3 = d):
    (xs: List a) → (ys: List b) → (zs: List c) → List.length ys = List.length xs → List.length zs = List.length xs → (i: Nat) →
    List.getOr (List.zipWith3 xs ys zs f) i d = f (List.getOr xs i d1) (List.getOr ys i d2) (List.getOr zs i d3)
  | Nil, Nil, Nil, h1, h2, i => Eq.sym hd
  | Nil, Cons y ys, zs, h1, h2, i => Void.exfalso (Nat.succNotZero (List.length ys) h1)
  | Nil, Nil, Cons z zs, h1, h2, i => Void.exfalso (Nat.succNotZero (List.length zs) h2)
  | Cons x xs, Nil, zs, h1, h2, i => Void.exfalso (Nat.zeroNotSucc (List.length xs) h1)
  | Cons x xs, Cons y ys, Nil, h1, h2, i => Void.exfalso (Nat.zeroNotSucc (List.length xs) h2)
  | Cons x xs, Cons y ys, Cons z zs, h1, h2, Zero => rfl
  | Cons x xs, Cons y ys, Cons z zs, h1, h2, Succ i =>
    List.getOrZipWith3 f d1 d2 d3 d hd xs ys zs (Nat.succInjective (List.length ys) (List.length xs) h1) (Nat.succInjective (List.length zs) (List.length xs) h2) i

theorem List.getOrMap: (xs: List a) → (i: Nat) → (d: a) → (f: a → b) → List.getOr (List.map xs f) i (f d) = f (List.getOr xs i d)
  | Nil, i, d, f => rfl
  | Cons x xs, Zero, d, f => rfl
  | Cons x xs, Succ i, d, f => List.getOrMap xs i d f

-- Index i of `f` mapped over the run `s, s + 1, ..., s + n - 1` is `f (i + s)`.
theorem List.getOrMapRange (f: Nat → b) (d: b): (n: Nat) → (s: Nat) → (i: Nat) → i < n →
    List.getOr (List.map (List.rangeFrom n s) f) i d = f (i + s)
  | Zero, s, i, h => Void.exfalso (Bool.falseNotTrue h)
  | Succ n, s, Zero, h => rfl
  | Succ n, s, Succ i, h => rewrite <- Nat.addSucc i s in List.getOrMapRange f d n (Succ s) i h

theorem List.getOrMapRangeExample: List.getOr (List.map (List.rangeFrom 4 3) (i => i * i)) 2 0 = 25 := rfl

theorem List.sumByGetOr (xs: List a) (d: a) (f: a → Nat): List.sumBy xs f = List.sumBy (List.range (List.length xs)) (i => f (List.getOr xs i d)) :=
  calc List.sumBy xs f
    _ = List.sumBy (List.map (List.range (List.length xs)) (i => List.getOr xs i d)) f := rewrite List.mapGetOr xs d
    _ = List.sumBy (List.range (List.length xs)) (i => f (List.getOr xs i d)) := List.sumByMap (List.range (List.length xs)) f (i => List.getOr xs i d)

-- Each element with its index is each index with its element.
theorem List.withIndexFromRange: (xs: List a) → (d: a) → (s: Nat) →
    List.withIndexFrom s xs = List.map (List.range (List.length xs)) (i => MkPair (s + i) (List.getOr xs i d))
  | Nil, d, s => rfl
  | Cons x xs, d, s =>
    rewrite Nat.addZero s, List.withIndexFromRange xs d (Succ s),
      List.mapRangeShift (i => MkPair (s + i) (List.getOr (Cons x xs) i d)) (List.length xs) 0 in
      Eq.cong (Cons (MkPair s x))
        (List.mapCong (List.range (List.length xs)) (i => MkPair (Succ s + i) (List.getOr xs i d))
          (i => MkPair (s + Succ i) (List.getOr (Cons x xs) (Succ i) d)) (i => rewrite Nat.addSucc s i))

theorem List.withIndexRange (xs: List a) (d: a): List.withIndex xs = List.map (List.range (List.length xs)) (i => MkPair i (List.getOr xs i d)) :=
  List.withIndexFromRange xs d 0

test "List.withIndexRange" := ["a", "b"].withIndex == List.map (List.range 2) (i => MkPair i (List.getOr ["a", "b"] i ""))

-- The position of the first `x` in the list, counting from 0, or the list's
-- length if `x` isn't in it: `[5, 7, 5].indexOf 5` is 0, `.indexOf 9` is 3.
def List.indexOf [auto eq: DecEq a]: List a → (x: a) → Nat
  | Nil, x => 0
  | Cons y ys, x => if y == x then 0 else Succ (List.indexOf ys x)

test "List.indexOf" := [5, 7, 5].indexOf 7 == 1 ∧ [5, 7, 5].indexOf 5 == 0 ∧ [5, 7, 5].indexOf 9 == 3

-- Adding two rows entry by entry.
theorem List.getOrZipWithAdd: (u: List Nat) → (c: Nat) → (v: List Nat) → c < List.length u → c < List.length v →
    List.getOr (List.zipWith u v Nat.add) c 0 = List.getOr u c 0 + List.getOr v c 0
  | Nil, c, v, hu, hv => Void.exfalso (Bool.falseNotTrue hu)
  | Cons x xs, c, Nil, hu, hv => Void.exfalso (Bool.falseNotTrue hv)
  | Cons x xs, Zero, Cons y ys, hu, hv => rfl
  | Cons x xs, Succ c, Cons y ys, hu, hv => List.getOrZipWithAdd xs c ys hu hv

-- Element i of a mapped list, inside it.
theorem List.getOrMapLt: (xs: List a) → (i: Nat) → (d: a) → (e: b) → i < List.length xs → (f: a → b) → List.getOr (List.map xs f) i e = f (List.getOr xs i d)
  | Nil, i, d, e, h, f => Void.exfalso (Bool.falseNotTrue h)
  | Cons x xs, Zero, d, e, h, f => rfl
  | Cons x xs, Succ i, d, e, h, f => List.getOrMapLt xs i d e h f

-- Element i of each element with its index (counted from `start`), and of
-- `mapWithIndex`, inside the list.
theorem List.getOrWithIndexFrom (d: a) (fallback: Pair Nat a): (start: Nat) → (xs: List a) → (i: Nat) → i < List.length xs →
    List.getOr (List.withIndexFrom start xs) i fallback = MkPair (start + i) (List.getOr xs i d)
  | start, Nil, i, h => Void.exfalso (Bool.falseNotTrue h)
  | start, Cons x xs, Zero, h => rewrite Nat.addZero start in rfl
  | start, Cons x xs, Succ i, h => rewrite Nat.addSucc start i in List.getOrWithIndexFrom d fallback (Succ start) xs i h

theorem List.getOrWithIndex (xs: List a) (i: Nat) (d: a) (fallback: Pair Nat a) (h: i < List.length xs):
    List.getOr (List.withIndex xs) i fallback = MkPair i (List.getOr xs i d) :=
  List.getOrWithIndexFrom d fallback 0 xs i h

theorem List.getOrMapWithIndex (xs: List a) (i: Nat) (d: a) (e: b) (h: i < List.length xs) (f: Nat → a → b):
    List.getOr (List.mapWithIndex xs f) i e = f i (List.getOr xs i d) :=
  let long: i < List.length (List.withIndex xs) := rewrite List.lengthWithIndex xs in h
  Eq.trans (List.getOrMapLt (List.withIndex xs) i (MkPair 0 d) e long (pair => f pair.fst pair.snd))
    (Eq.cong (pair => f pair.fst pair.snd) (List.getOrWithIndex xs i d (MkPair 0 d) h))

test "List.getOrMapWithIndex" := List.getOr ([5, 6, 7].mapWithIndex (index x => index * x)) 2 0 == 14

-- Entry k of the running accumulations is the fold of the first k elements.
theorem List.getOrScanLeft (f: b → a → b) (d: b): (xs: List a) → (z: b) → (k: Nat) → k ≤ List.length xs →
    List.getOr (List.scanLeft xs z f) k d = List.foldLeft (List.take xs k) z f
  | Nil, z, Zero, h => rfl
  | Nil, z, Succ k, h => Void.exfalso (Bool.falseNotTrue h)
  | Cons x xs, z, Zero, h => rfl
  | Cons x xs, z, Succ k, h => List.getOrScanLeft f d xs (f z x) k h

-- Element k of `zipWith xs (scanLeft xs z f) g` is `g` of element k and the
-- fold of the elements before it: laying items end to end from `z`, item k
-- is placed after the first k.
theorem List.getOrZipWithScanLeft (f: b → a → b) (g: a → b → c) (dx: a) (dc: c): (xs: List a) → (z: b) → (k: Nat) → k < List.length xs →
    List.getOr (List.zipWith xs (List.scanLeft xs z f) g) k dc = g (List.getOr xs k dx) (List.foldLeft (List.take xs k) z f)
  | Nil, z, k, h => Void.exfalso (Bool.falseNotTrue h)
  | Cons x xs, z, Zero, h => rfl
  | Cons x xs, z, Succ k, h => List.getOrZipWithScanLeft f g dx dc xs (f z x) k h

-- The fold of the first k + 1 elements is one step after the fold of the
-- first k: neighbouring entries of a scan differ by one step.
theorem List.foldLeftTakeSucc (f: b → a → b) (d: a): (xs: List a) → (z: b) → (k: Nat) → k < List.length xs →
    List.foldLeft (List.take xs (Succ k)) z f = f (List.foldLeft (List.take xs k) z f) (List.getOr xs k d)
  | Nil, z, k, h => Void.exfalso (Bool.falseNotTrue h)
  | Cons x xs, z, Zero, h => rfl
  | Cons x xs, z, Succ k, h => List.foldLeftTakeSucc f d xs (f z x) k h

theorem List.getOrZipWithScanLeftExample:
    List.getOr (List.zipWith [2, 3, 4] (List.scanLeft [2, 3, 4] 10 (offset width => offset + width)) (width offset => (offset, width))) 2 (0, 0)
      = (List.foldLeft [2, 3] 10 (offset width => offset + width), 4) :=
  List.getOrZipWithScanLeft (offset width => offset + width) (width offset => (offset, width)) 0 (0, 0) [2, 3, 4] 10 2 rfl
