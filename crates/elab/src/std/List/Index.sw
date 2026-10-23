-- Lists by index: `List.getOr` (the element at an index, with a default) and
-- its lemmas for append, take, a block written n times, and equality by
-- index. A file of its own, so that programs using only the toolkit don't
-- check these.

-- The element at index i, or `fallback` past the end.
def List.getOr (fallback: a): Nat -> List a -> a
  | i, Nil => fallback
  | Zero, Cons x xs => x
  | Succ i, Cons x xs => List.getOr fallback i xs

theorem List.getOrExample: List.getOr 0 1 [7, 8] = 8 := rfl

theorem List.getOrAppendLeft (d: a): (i: Nat) -> (xs: List a) -> (ys: List a) -> i < List.length xs ->
    List.getOr d i (List.append xs ys) = List.getOr d i xs
  | i, Nil, ys, h => Void.exfalso (Bool.falseNotTrue h)
  | Zero, Cons x xs, ys, h => rfl
  | Succ i, Cons x xs, ys, h => List.getOrAppendLeft d i xs ys h

theorem List.getOrAppendRight (d: a): (i: Nat) -> (xs: List a) -> (ys: List a) -> List.length xs <= i ->
    List.getOr d i (List.append xs ys) = List.getOr d (i - List.length xs) ys
  | i, Nil, ys, h => rfl
  | Zero, Cons x xs, ys, h => Void.exfalso (Bool.falseNotTrue h)
  | Succ i, Cons x xs, ys, h => List.getOrAppendRight d i xs ys h

theorem List.getOrTake (d: a): (k: Nat) -> (i: Nat) -> (xs: List a) -> i < k -> List.getOr d i (List.take k xs) = List.getOr d i xs
  | Zero, i, xs, h => Void.exfalso (Bool.falseNotTrue h)
  | Succ k, i, Nil, h => rfl
  | Succ k, Zero, Cons x xs, h => rfl
  | Succ k, Succ i, Cons x xs, h => List.getOrTake d k i xs h

-- Lists of the same length that agree at every index are equal.
theorem List.extGetOr (d: a): (xs: List a) -> (ys: List a) -> List.length xs = List.length ys ->
    ((i: Nat) -> i < List.length xs -> List.getOr d i xs = List.getOr d i ys) -> xs = ys
  | Nil, Nil, e, h => rfl
  | Nil, Cons y ys, e, h => Void.exfalso (Nat.zeroNotSucc (List.length ys) e)
  | Cons x xs, Nil, e, h => Void.exfalso (Nat.succNotZero (List.length xs) e)
  | Cons x xs, Cons y ys, e, h =>
    Eq.trans (Eq.cong (z => Cons z xs) (h 0 rfl))
      (Eq.cong (Cons y) (List.extGetOr d xs ys (Nat.succInjective (List.length xs) (List.length ys) e) (i hi => h (Succ i) hi)))

-- Index i of a block of k elements written n times is index `i % k` of the block.
theorem List.getOrConcatReplicate (d: a) (b: List a) (k: Nat) [auto hk: k != 0] (hb: List.length b = k): (n: Nat) -> (i: Nat) -> i < n * k ->
    List.getOr d i (List.concat (List.replicate n b)) = List.getOr d (i % k) b
  | Zero, i, h => Void.exfalso (Bool.falseNotTrue h)
  | Succ n, i, h =>
    match t: Nat.leq k i with
      | False =>
        calc List.getOr d i (List.append b (List.concat (List.replicate n b)))
          _ = List.getOr d i b := List.getOrAppendLeft d i b (List.concat (List.replicate n b)) (Nat.ltCongRight i k (List.length b) (Eq.sym hb) (Nat.leqFalse k i t))
          _ = List.getOr d (i % k) b := Eq.cong (y => List.getOr d y b) (Eq.sym (Nat.modSmall i k (Nat.leqFalse k i t)))
      | True =>
        calc List.getOr d i (List.append b (List.concat (List.replicate n b)))
          _ = List.getOr d (i - List.length b) (List.concat (List.replicate n b))
            := List.getOrAppendRight d i b (List.concat (List.replicate n b)) (Nat.leCongLeft k (List.length b) i (Eq.sym hb) t)
          _ = List.getOr d (i - k) (List.concat (List.replicate n b)) := Eq.cong (y => List.getOr d (i - y) (List.concat (List.replicate n b))) hb
          _ = List.getOr d ((i - k) % k) b
            := List.getOrConcatReplicate d b k hb n (i - k) (Nat.subLtAdd i k (n * k) t (Nat.ltCongRight i (k + n * k) (n * k + k) (Nat.addComm k (n * k)) h))
          _ = List.getOr d (i % k) b
            := Eq.cong (y => List.getOr d y b) (Eq.trans (Eq.sym (Nat.addModSelf k (i - k))) (Eq.cong (y => y % k) (Nat.addSubCancel k i t)))

-- `getOr` past the end and after padding, and a list read off by index.
theorem List.getOrReplicate (x: a): (i: Nat) -> (n: Nat) -> List.getOr x i (List.replicate n x) = x
  | i, Zero => rfl
  | Zero, Succ n => rfl
  | Succ i, Succ n => List.getOrReplicate x i n

-- Copies of the default on the end change no index.
theorem List.getOrAppendReplicate (x: a) (k: Nat): (i: Nat) -> (xs: List a) -> List.getOr x i (List.append xs (List.replicate k x)) = List.getOr x i xs
  | i, Nil => List.getOrReplicate x i k
  | Zero, Cons y ys => rfl
  | Succ i, Cons y ys => List.getOrAppendReplicate x k i ys

theorem List.getOrPadRight (x: a) (n: Nat) (i: Nat) (xs: List a): List.getOr x i (List.padRight n x xs) = List.getOr x i xs :=
  List.getOrAppendReplicate x (n - List.length xs) i xs

-- Past the end, the default.
theorem List.getOrPast (d: a): (i: Nat) -> (xs: List a) -> List.length xs <= i -> List.getOr d i xs = d
  | i, Nil, h => rfl
  | Zero, Cons x xs, h => Void.exfalso (Bool.falseNotTrue h)
  | Succ i, Cons x xs, h => List.getOrPast d i xs h

-- A list is its elements read off by index.
theorem List.mapGetOr (d: a): (xs: List a) -> List.map (i => List.getOr d i xs) (List.range (List.length xs)) = xs
  | Nil => rfl
  | Cons x xs =>
    calc List.map (i => List.getOr d i (Cons x xs)) (List.rangeFrom (Succ (List.length xs)) 0)
      _ = Cons x (List.map (i => List.getOr d i (Cons x xs)) (List.rangeFrom (List.length xs) 1))
      _ = Cons x (List.map (i => List.getOr d i xs) (List.rangeFrom (List.length xs) 0))
        := rewrite List.mapRangeShift (i => List.getOr d i (Cons x xs)) (List.length xs) 0
      _ = Cons x xs := rewrite List.mapGetOr d xs

-- `headOr` is index 0; `getOr` of a `map` and of a `zipWith3`; a sum over a
-- list as a sum over its indices.
theorem List.headOrGetOr (d: a): (xs: List a) -> List.headOr d xs = List.getOr d 0 xs
  | Nil => rfl
  | Cons x xs => rfl

theorem List.getOrZipWith3 (f: a -> b -> c -> e) (d1: a) (d2: b) (d3: c) (d: e) (hd: f d1 d2 d3 = d):
    (xs: List a) -> (ys: List b) -> (zs: List c) -> List.length ys = List.length xs -> List.length zs = List.length xs -> (i: Nat) ->
    List.getOr d i (List.zipWith3 f xs ys zs) = f (List.getOr d1 i xs) (List.getOr d2 i ys) (List.getOr d3 i zs)
  | Nil, Nil, Nil, h1, h2, i => Eq.sym hd
  | Nil, Cons y ys, zs, h1, h2, i => Void.exfalso (Nat.succNotZero (List.length ys) h1)
  | Nil, Nil, Cons z zs, h1, h2, i => Void.exfalso (Nat.succNotZero (List.length zs) h2)
  | Cons x xs, Nil, zs, h1, h2, i => Void.exfalso (Nat.zeroNotSucc (List.length xs) h1)
  | Cons x xs, Cons y ys, Nil, h1, h2, i => Void.exfalso (Nat.zeroNotSucc (List.length xs) h2)
  | Cons x xs, Cons y ys, Cons z zs, h1, h2, Zero => rfl
  | Cons x xs, Cons y ys, Cons z zs, h1, h2, Succ i =>
    List.getOrZipWith3 f d1 d2 d3 d hd xs ys zs (Nat.succInjective (List.length ys) (List.length xs) h1) (Nat.succInjective (List.length zs) (List.length xs) h2) i

theorem List.getOrMap (f: a -> b) (d: a): (i: Nat) -> (xs: List a) -> List.getOr (f d) i (List.map f xs) = f (List.getOr d i xs)
  | i, Nil => rfl
  | Zero, Cons x xs => rfl
  | Succ i, Cons x xs => List.getOrMap f d i xs

-- Index i of `f` mapped over the run `s, s + 1, ..., s + n - 1` is `f (i + s)`.
theorem List.getOrMapRange (f: Nat -> b) (d: b): (n: Nat) -> (s: Nat) -> (i: Nat) -> i < n ->
    List.getOr d i (List.map f (List.rangeFrom n s)) = f (i + s)
  | Zero, s, i, h => Void.exfalso (Bool.falseNotTrue h)
  | Succ n, s, Zero, h => rfl
  | Succ n, s, Succ i, h => rewrite <- Nat.addSucc i s in List.getOrMapRange f d n (Succ s) i h

theorem List.getOrMapRangeExample: List.getOr 0 2 (List.map (i => i * i) (List.rangeFrom 4 3)) = 25 := rfl

theorem List.sumByGetOr (f: a -> Nat) (d: a) (xs: List a): List.sumBy f xs = List.sumBy (i => f (List.getOr d i xs)) (List.range (List.length xs)) :=
  calc List.sumBy f xs
    _ = List.sumBy f (List.map (i => List.getOr d i xs) (List.range (List.length xs))) := rewrite List.mapGetOr d xs
    _ = List.sumBy (i => f (List.getOr d i xs)) (List.range (List.length xs)) := List.sumByMap f (i => List.getOr d i xs) (List.range (List.length xs))

-- Each element with its index is each index with its element.
theorem List.withIndexFromRange (d: a): (s: Nat) -> (xs: List a) ->
    List.withIndexFrom s xs = List.map (i => MkPair (s + i) (List.getOr d i xs)) (List.range (List.length xs))
  | s, Nil => rfl
  | s, Cons x xs =>
    rewrite Nat.addZero s, List.withIndexFromRange d (Succ s) xs,
      List.mapRangeShift (i => MkPair (s + i) (List.getOr d i (Cons x xs))) (List.length xs) 0 in
      Eq.cong (Cons (MkPair s x))
        (List.mapCong (i => MkPair (Succ s + i) (List.getOr d i xs)) (i => MkPair (s + Succ i) (List.getOr d (Succ i) (Cons x xs)))
          (List.range (List.length xs)) (i => rewrite Nat.addSucc s i))

theorem List.withIndexRange (d: a) (xs: List a): List.withIndex xs = List.map (i => MkPair i (List.getOr d i xs)) (List.range (List.length xs)) :=
  List.withIndexFromRange d 0 xs

test "List.withIndexRange" := ["a", "b"].withIndex == List.map (i => MkPair i (List.getOr "" i ["a", "b"])) (List.range 2)
