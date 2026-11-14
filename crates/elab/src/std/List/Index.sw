--| Lists by index: `List.getOr` (the element at an index, with a default) and
--| its lemmas for append, take, a block written n times, and equality by
--| index.
-- A file of its own, so that programs using only the toolkit don't
-- check these.

--| The element at `index`, counting from 0, or `fallback` past the end. A result
--| equal to `fallback` doesn't say the index was past the end; use [`List.get`]
--| when that matters. O(index), and tail-recursive.
@[tailrec]
def List.getOr: (xs: List a) → (index: Nat) → (fallback: a) → a
  | [], i, fallback => fallback
  | [x, ..xs], Zero, fallback => x
  | [x, ..xs], Succ i, fallback => List.getOr xs i fallback

theorem List.getOrExample: List.getOr [7, 8] 1 0 = 8 := rfl

--| An element at an index below the length is in the list.
theorem List.getOrMem ∀ (xs: List a) (i: Nat) (fallback: a) (h: i < List.length xs): List.getOr xs i fallback ∈ xs :=
  match xs, i with
    | [x, ..rest], Zero => Inl rfl
    | [x, ..rest], Succ i => Inr (List.getOrMem rest i fallback h)

theorem List.getOrAppendLeft ∀ (xs: List a) (i: Nat) (d: a) (ys: List a)
    (h: i < List.length xs):
    List.getOr (List.append xs ys) i d = List.getOr xs i d :=
  match xs, i with
    | [x, ..xs], Zero => rfl
    | [x, ..xs], Succ i => List.getOrAppendLeft xs i d ys h

theorem List.getOrAppendRight ∀ (xs: List a) (i: Nat) (d: a) (ys: List a)
    (h: List.length xs ≤ i):
    List.getOr (List.append xs ys) i d = List.getOr ys (i - List.length xs) d :=
  match xs, i with
    | [], i => rfl
    | [x, ..xs], Succ i => List.getOrAppendRight xs i d ys h

theorem List.getOrTake ∀ (xs: List a) (k i: Nat) (d: a)
    (h: i < k):
    List.getOr (List.take xs k) i d = List.getOr xs i d :=
  match xs, k, i with
    | [], Succ k, i => rfl
    | [x, ..xs], Succ k, Zero => rfl
    | [x, ..xs], Succ k, Succ i => List.getOrTake xs k i d h

--| The first k + 1 elements are the first k, then the element at k.
theorem List.takeSucc ∀ (d: a) (xs: List a) (k: Nat)
    (h: k < List.length xs):
    List.take xs (Succ k) = List.append (List.take xs k) [List.getOr xs k d] :=
  match xs, k with
    | [x, ..xs], Zero => rfl
    | [x, ..xs], Succ k => Eq.cong (Cons x) (List.takeSucc d xs k h)

--| What is left after dropping k elements starts with the element at k, when
--| there is one.
theorem List.dropAt ∀ (d: a) (xs: List a) (k: Nat)
    (h: k < List.length xs):
    List.drop xs k = [List.getOr xs k d, ..List.drop xs (Succ k)] :=
  match xs, k with
    | [x, ..xs], Zero => rfl
    | [x, ..xs], Succ k => List.dropAt d xs k h

--| `getOr` is `List.get` with the fallback for `None` (`List.get`'s lemmas
--| are in Lemmas.sw).
theorem List.getOrGet ∀ (xs: List a) (k: Nat) (d: a): List.getOr xs k d = Option.getOrElse (List.get xs k) d :=
  match xs, k with
    | [], k => rfl
    | [x, ..xs], Zero => rfl
    | [x, ..xs], Succ k => List.getOrGet xs k d

--| What `get` finds, `getOr` gives, whatever the fallback.
theorem List.getOrOfGet ∀ (xs: List a) (k: Nat) (d v: a) (h: List.get xs k = Some v): List.getOr xs k d = v :=
  match xs, k with
    | [x, ..xs], Zero => Option.someInjective h
    | [x, ..xs], Succ k => List.getOrOfGet xs k d v h

--| Within the list, `get` finds what `getOr` gives.
theorem List.getOfGetOr ∀ (xs: List a) (k: Nat) (d: a)
    (h: k < List.length xs):
    List.get xs k = Some (List.getOr xs k d) :=
  match xs, k with
    | [x, ..xs], Zero => rfl
    | [x, ..xs], Succ k => List.getOfGetOr xs k d h

theorem List.getOrOfGetExample ∀ (xs: List Nat) (k v: Nat)
    (h: List.get xs k = Some v):
    List.getOr xs k 0 = List.getOr xs k 1 :=
  Eq.trans (List.getOrOfGet xs k 0 v h) (Eq.sym (List.getOrOfGet xs k 1 v h))

--| Lists of the same length that agree at every index are equal.
theorem List.extGetOr ∀ (d: a) (xs ys: List a)
    (e: List.length xs = List.length ys)
    (h: ∀ (i: Nat) => i < List.length xs → List.getOr xs i d = List.getOr ys i d):
    xs = ys :=
  match xs, ys with
    | [], [] => rfl
    | [], [y, ..ys] => Void.exfalso (Nat.zeroNotSucc (List.length ys) e)
    | [x, ..xs], [] => Void.exfalso (Nat.succNotZero (List.length xs) e)
    | [x, ..xs], [y, ..ys] =>
      Eq.trans
        (Eq.cong (z => [z, ..xs]) (h 0 rfl))
        (Eq.cong (Cons y) (List.extGetOr d xs ys (Nat.succInjective e) (i hi => h (Succ i) hi)))

--| Index i of a block of k elements written n times is index `i % k` of the block.
theorem List.getOrConcatReplicate ∀ (b: List a) (d: a) (k: Nat)
    [auto hk: k ≠ 0]
    (hb: List.length b = k) (n i: Nat)
    (h: i < n * k):
    List.getOr (List.concat (List.replicate n b)) i d = List.getOr b (i % k) d :=
  match n with
    | Succ n =>
      match t: Nat.leq k i with
        | False =>
          calc List.getOr (List.append b (List.concat (List.replicate n b))) i d
            _ = List.getOr b i d :=
              List.getOrAppendLeft b i d
                (List.concat (List.replicate n b))
                (Nat.ltCongRight i k (List.length b) (Eq.sym hb) t.read)
            _ = List.getOr b (i % k) d := Eq.cong (y => List.getOr b y d) (Eq.sym (Nat.modSmall i k t.read))
        | True =>
          calc List.getOr (List.append b (List.concat (List.replicate n b))) i d
            _ = List.getOr (List.concat (List.replicate n b)) (i - List.length b) d :=
              List.getOrAppendRight b i d
                (List.concat (List.replicate n b))
                (Nat.leCongLeft k (List.length b) i (Eq.sym hb) t)
            _ = List.getOr (List.concat (List.replicate n b)) (i - k) d :=
              Eq.cong (y => List.getOr (List.concat (List.replicate n b)) (i - y) d) hb
            _ = List.getOr b ((i - k) % k) d :=
              List.getOrConcatReplicate b d k hb n
                (i - k)
                (Nat.subLtAdd i k (n * k) t (Nat.ltCongRight i (k + n * k) (n * k + k) (Nat.addComm k (n * k)) h))
            _ = List.getOr b (i % k) d :=
              Eq.cong
                (y => List.getOr b y d)
                (Eq.trans (Eq.sym (Nat.addModSelf k (i - k))) (Eq.cong (y => y % k) (Nat.addSubCancel k i t)))

--| `getOr` past the end and after padding, and a list read off by index.
theorem List.getOrReplicate ∀ (x: a) (i n: Nat): List.getOr (List.replicate n x) i x = x := match i, n with
  | i, Zero => rfl
  | Zero, Succ n => rfl
  | Succ i, Succ n => List.getOrReplicate x i n

--| Copies of the default on the end change no index.
theorem List.getOrAppendReplicate ∀ (xs: List a) (x: a) (k i: Nat):
    List.getOr (List.append xs (List.replicate k x)) i x = List.getOr xs i x :=
  match xs, i with
    | [], i => List.getOrReplicate x i k
    | [y, ..ys], Zero => rfl
    | [y, ..ys], Succ i => List.getOrAppendReplicate ys x k i

theorem List.getOrPadRight ∀ (xs: List a) (x: a) (n i: Nat):
    List.getOr (List.padRight xs n x) i x = List.getOr xs i x :=
  List.getOrAppendReplicate xs x (n - List.length xs) i

--| Past the end, the default.
theorem List.getOrPast ∀ (xs: List a) (i: Nat) (d: a) (h: List.length xs ≤ i): List.getOr xs i d = d := match xs, i with
  | [], i => rfl
  | [x, ..xs], Succ i => List.getOrPast xs i d h

--| A list is its elements read off by index.
theorem List.mapGetOr ∀ (xs: List a) (d: a): List.map (List.range 0 (List.length xs)) (i => List.getOr xs i d) = xs :=
  match xs with
    | [] => rfl
    | [x, ..xs] =>
      calc List.map (List.rangeFrom (Succ (List.length xs)) 0) (i => List.getOr [x, ..xs] i d)
        _ = [x, ..List.map (List.rangeFrom (List.length xs) 1) (i => List.getOr [x, ..xs] i d)]
        _ = [x, ..List.map (List.rangeFrom (List.length xs) 0) (i => List.getOr xs i d)] :=
          rewrite List.mapRangeFromShift (i => List.getOr [x, ..xs] i d) (List.length xs) 0
        _ = [x, ..xs] := rewrite List.mapGetOr xs d

--| `headOr` is index 0; `getOr` of a `map` and of a `zipWith3`; a sum over a
--| list as a sum over its indices.
theorem List.headOrGetOr ∀ (xs: List a) (d: a): List.headOr xs d = List.getOr xs 0 d := match xs with
  | [] => rfl
  | [x, ..xs] => rfl

--| `headOr` is `head` with a fallback for `None`:
--| `xs.headOr d = xs.head.getOrElse d`.
theorem List.headOrHead ∀ (xs: List a) (d: a): List.headOr xs d = Option.getOrElse (List.head xs) d := match xs with
  | [] => rfl
  | [x, ..xs] => rfl

theorem List.getOrZipWith3 ∀ (f: a → b → c → e) (d1: a) (d2: b) (d3: c) (d: e)
    (hd: f d1 d2 d3 = d):
    ∀ (xs: List a) (ys: List b) (zs: List c) => List.length ys = List.length xs
      → List.length zs = List.length xs
      → ∀ (i: Nat) => List.getOr (List.zipWith3 xs ys zs f) i d
        = f (List.getOr xs i d1) (List.getOr ys i d2) (List.getOr zs i d3)
  | [], [], [], h1, h2, i => Eq.sym hd
  | [], [y, ..ys], zs, h1, h2, i => Void.exfalso (Nat.succNotZero (List.length ys) h1)
  | [], [], [z, ..zs], h1, h2, i => Void.exfalso (Nat.succNotZero (List.length zs) h2)
  | [x, ..xs], [], zs, h1, h2, i => Void.exfalso (Nat.zeroNotSucc (List.length xs) h1)
  | [x, ..xs], [y, ..ys], [], h1, h2, i => Void.exfalso (Nat.zeroNotSucc (List.length xs) h2)
  | [x, ..xs], [y, ..ys], [z, ..zs], h1, h2, Zero => rfl
  | [x, ..xs], [y, ..ys], [z, ..zs], h1, h2, Succ i =>
    List.getOrZipWith3 f d1 d2 d3 d hd xs ys zs (Nat.succInjective h1) (Nat.succInjective h2) i

theorem List.getOrMap ∀ (xs: List a) (i: Nat) (d: a) (f: a → b):
    List.getOr (List.map xs f) i (f d) = f (List.getOr xs i d) :=
  match xs, i with
    | [], i => rfl
    | [x, ..xs], Zero => rfl
    | [x, ..xs], Succ i => List.getOrMap xs i d f

--| Index i of `f` mapped over the run `s, s + 1, ..., s + n - 1` is `f (i + s)`.
theorem List.getOrMapRange ∀ (f: Nat → b) (d: b) (n s i: Nat)
    (h: i < n):
    List.getOr (List.map (List.rangeFrom n s) f) i d = f (i + s) :=
  match n, i with
    | Succ n, Zero => rfl
    | Succ n, Succ i => rewrite <- Nat.addSucc i s in List.getOrMapRange f d n (Succ s) i h

theorem List.getOrMapRangeExample: List.getOr (List.map (List.rangeFrom 4 3) (i => i * i)) 2 0 = 25 := rfl

theorem List.sumByGetOr ∀ (xs: List a) (d: a) (f: a → Nat):
    List.sumBy xs f = List.sumBy (List.range 0 (List.length xs)) (i => f (List.getOr xs i d)) :=
  calc List.sumBy xs f
    _ = List.sumBy (List.map (List.range 0 (List.length xs)) (i => List.getOr xs i d)) f := rewrite List.mapGetOr xs d
    _ = List.sumBy (List.range 0 (List.length xs)) (i => f (List.getOr xs i d)) :=
      List.sumByMap (List.range 0 (List.length xs)) f (i => List.getOr xs i d)

--| `withIndexFrom s xs` is each index of `xs`, plus `s`, with its element.
theorem List.withIndexFromRange ∀ (xs: List a) (d: a) (s: Nat):
    List.withIndexFrom s xs = List.map (List.range 0 (List.length xs)) (i => MkPair (s + i) (List.getOr xs i d)) :=
  match xs with
    | [] => rfl
    | [x, ..xs] =>
      rewrite Nat.addZero s,
          List.withIndexFromRange xs d (Succ s),
          List.mapRangeFromShift (i => MkPair (s + i) (List.getOr [x, ..xs] i d)) (List.length xs) 0 in
        Eq.cong
          (Cons (MkPair s x))
          (List.mapCong
            (List.range 0 (List.length xs))
            (i => MkPair (Succ s + i) (List.getOr xs i d))
            (i => MkPair (s + Succ i) (List.getOr [x, ..xs] (Succ i) d))
            (i => rewrite Nat.addSucc s i))

theorem List.withIndexRange ∀ (xs: List a) (d: a):
    List.withIndex xs = List.map (List.range 0 (List.length xs)) (i => MkPair i (List.getOr xs i d)) :=
  List.withIndexFromRange xs d 0

test "List.withIndexRange" :=
  ["a", "b"].withIndex == List.map (List.range 0 2) (i => MkPair i (List.getOr ["a", "b"] i ""))

--| The position of the first `x` in the list, counting from 0, or the list's
--| length if `x` isn't in it: `[5, 7, 5].indexOf 5` is 0, `.indexOf 9` is 3.
--| Test `< length` for membership ([`List.containsIndexOf`]); for the first
--| element satisfying a test, use [`List.findIndex`].
def List.indexOf [auto eq: DecEq a]: (xs: List a) → (x: a) → Nat
  | [], x => 0
  | [y, ..ys], x => if y == x then 0 else Succ (List.indexOf ys x)

test "List.indexOf" := [5, 7, 5].indexOf 7 == 1 ∧ [5, 7, 5].indexOf 5 == 0 ∧ [5, 7, 5].indexOf 9 == 3

--| Adding two rows entry by entry.
theorem List.getOrZipWithAdd ∀ (u: List Nat) (c: Nat) (v: List Nat)
    (hu: c < List.length u)
    (hv: c < List.length v):
    List.getOr (List.zipWith u v Nat.add) c 0 = List.getOr u c 0 + List.getOr v c 0 :=
  match u, c, v with
    | [x, ..xs], Zero, [y, ..ys] => rfl
    | [x, ..xs], Succ c, [y, ..ys] => List.getOrZipWithAdd xs c ys hu hv

--| Element i of a mapped list, inside it.
theorem List.getOrMapLt: ∀ (xs: List a) (i: Nat) (d: a) (e: b) => i < List.length xs
      → ∀ (f: a → b) => List.getOr (List.map xs f) i e = f (List.getOr xs i d)
  | [], i, d, e, h, f => cases
  | [x, ..xs], Zero, d, e, h, f => rfl
  | [x, ..xs], Succ i, d, e, h, f => List.getOrMapLt xs i d e h f

--| Element i of each element with its index (counted from `start`), and of
--| `mapWithIndex`, inside the list.
theorem List.getOrWithIndexFrom ∀ (d: a) (fallback: Pair Nat a) (start: Nat) (xs: List a) (i: Nat)
    (h: i < List.length xs):
    List.getOr (List.withIndexFrom start xs) i fallback = MkPair (start + i) (List.getOr xs i d) :=
  match xs, i with
    | [x, ..xs], Zero => rewrite Nat.addZero start in rfl
    | [x, ..xs], Succ i => rewrite Nat.addSucc start i in List.getOrWithIndexFrom d fallback (Succ start) xs i h

theorem List.getOrWithIndex ∀ (xs: List a) (i: Nat) (d: a) (fallback: Pair Nat a)
    (h: i < List.length xs):
    List.getOr (List.withIndex xs) i fallback = MkPair i (List.getOr xs i d) :=
  List.getOrWithIndexFrom d fallback 0 xs i h

theorem List.getOrMapWithIndex ∀ (xs: List a) (i: Nat) (d: a) (e: b)
    (h: i < List.length xs) (f: Nat → a → b):
    List.getOr (List.mapWithIndex xs f) i e = f i (List.getOr xs i d) :=
  let long: i < List.length (List.withIndex xs) := rewrite List.lengthWithIndex xs in h
  Eq.trans
    (List.getOrMapLt (List.withIndex xs) i (MkPair 0 d) e long (pair => f pair.fst pair.snd))
    (Eq.cong (pair => f pair.fst pair.snd) (List.getOrWithIndex xs i d (MkPair 0 d) h))

test "List.getOrMapWithIndex" := List.getOr ([5, 6, 7].mapWithIndex (index x => index * x)) 2 0 == 14

--| Entry k of the running accumulations is the fold of the first k elements.
theorem List.getOrScanLeft ∀ (f: b → a → b) (d: b) (xs: List a) (z: b) (k: Nat)
    (h: k ≤ List.length xs):
    List.getOr (List.scanLeft xs z f) k d = List.foldLeft (List.take xs k) z f :=
  match xs, k with
    | [], Zero => rfl
    | [x, ..xs], Zero => rfl
    | [x, ..xs], Succ k => List.getOrScanLeft f d xs (f z x) k h

--| Element k of `zipWith xs (scanLeft xs z f) g` is `g` of element k and the
--| fold of the elements before it. Laying items end to end from `z`, item k
--| is placed after the first k.
theorem List.getOrZipWithScanLeft ∀ (f: b → a → b) (g: a → b → c) (dx: a) (dc: c) (xs: List a) (z: b) (k: Nat)
    (h: k < List.length xs):
    List.getOr (List.zipWith xs (List.scanLeft xs z f) g) k dc
      = g (List.getOr xs k dx) (List.foldLeft (List.take xs k) z f) :=
  match xs, k with
    | [x, ..xs], Zero => rfl
    | [x, ..xs], Succ k => List.getOrZipWithScanLeft f g dx dc xs (f z x) k h

--| The fold of the first k + 1 elements is one step after the fold of the
--| first k: neighbouring entries of a scan differ by one step.
theorem List.foldLeftTakeSucc ∀ (f: b → a → b) (d: a) (xs: List a) (z: b) (k: Nat)
    (h: k < List.length xs):
    List.foldLeft (List.take xs (Succ k)) z f = f (List.foldLeft (List.take xs k) z f) (List.getOr xs k d) :=
  match xs, k with
    | [x, ..xs], Zero => rfl
    | [x, ..xs], Succ k => List.foldLeftTakeSucc f d xs (f z x) k h

theorem List.getOrZipWithScanLeftExample: List.getOr
      (List.zipWith [2, 3, 4] (List.scanLeft [2, 3, 4] 10 (offset width => offset + width)) (width offset =>
        (offset, width)))
      2
      (0, 0)
      = (List.foldLeft [2, 3] 10 (offset width => offset + width), 4) :=
  List.getOrZipWithScanLeft
    (offset width => offset + width)
    (width offset => (offset, width))
    0
    (0, 0)
    [2, 3, 4]
    10
    2
    rfl

-- sums over indices ------------------------------------------------------------

--| A sum whose terms are all 0.
theorem List.sumByRangeZero ∀ (f: Nat → Nat) (n: Nat)
    (zero: ∀ (j: Nat) => f j = 0):
    List.sumBy (List.range 0 n) f = 0 :=
  List.sumByZeroIntro (List.range 0 n) f (j _ => zero j)

--| A sum over a list is a sum over its indices, up to any bound at least its
--| length, with 0 past the end.
theorem List.sumByGet ∀ (g: a → Nat) (xs: List a) (n: Nat)
    (h: List.length xs ≤ n):
    List.sumBy xs g = List.sumBy (List.range 0 n) (j => Option.getOrElse (Option.map (List.get xs j) g) 0) :=
  match xs, n with
    | [], n => Eq.sym (List.sumByRangeZero _ n (j => rfl))
    | [x, ..xs], Succ n =>
      let each := (j: Nat) => Option.getOrElse (Option.map (List.get [x, ..xs] j) g) 0
      calc List.sumBy [x, ..xs] g
        _ = g x + List.sumBy xs g := List.sumByCons xs x g
        _ = each 0 + List.sumBy (List.range 0 n) (j => each (Succ j)) := rewrite List.sumByGet g xs n h
        _ = List.sumBy (List.range 0 (Succ n)) each := Eq.sym (List.sumByRangeSucc each n)

--| A sum over lists zipped in step is a sum over the indices, up to any bound
--| at least as long as the first list, with 0 where an element is missing.
theorem List.sumByZipWith ∀ (g: c → Nat) (f: a → b → c) (xs: List a) (ys: List b) (n: Nat)
    (h: List.length xs ≤ n):
    List.sumBy (List.zipWith xs ys f) g
      = List.sumBy (List.range 0 n) (j =>
        Option.getOrElse (Option.map2 (x y => g (f x y)) (List.get xs j) (List.get ys j)) 0) :=
  Eq.trans
    (List.sumByGet g (List.zipWith xs ys f) n (Nat.leTrans _ _ n (List.lengthZipWithLe f xs ys) h))
    (List.sumByCong (List.range 0 n) _ _ (j =>
      rewrite List.getZipWith f xs ys j,
          <- Option.map2FlatMap f (List.get ys j) (List.get xs j),
          Option.mapMap2 f g (List.get xs j) (List.get ys j) in
        rfl))

theorem List.sumByZipWith3 ∀ (g: d → Nat) (f: a → b → c → d) (xs: List a) (ys: List b) (zs: List c) (n: Nat)
    (h: List.length xs ≤ n):
    List.sumBy (List.zipWith3 xs ys zs f) g
      = List.sumBy (List.range 0 n) (j =>
        Option.getOrElse (Option.map3 (x y z => g (f x y z)) (List.get xs j) (List.get ys j) (List.get zs j)) 0) :=
  Eq.trans
    (List.sumByGet g (List.zipWith3 xs ys zs f) n (Nat.leTrans _ _ n (List.lengthZipWith3Le f xs ys zs) h))
    (List.sumByCong (List.range 0 n) _ _ (j =>
      rewrite List.getZipWith3 f xs ys zs j, Option.mapMap3 f g (List.get xs j) (List.get ys j) (List.get zs j) in rfl))

theorem List.sumByZipWith4 ∀ (g: e → Nat) (f: a → b → c → d → e) (xs: List a) (ys: List b) (zs: List c)
    (ws: List d) (n: Nat)
    (h: List.length xs ≤ n):
    List.sumBy (List.zipWith4 xs ys zs ws f) g
      = List.sumBy (List.range 0 n) (j =>
        Option.getOrElse
          (Option.map4 (x y z w => g (f x y z w)) (List.get xs j) (List.get ys j) (List.get zs j) (List.get ws j))
          0) :=
  Eq.trans
    (List.sumByGet g (List.zipWith4 xs ys zs ws f) n (Nat.leTrans _ _ n (List.lengthZipWith4Le f xs ys zs ws) h))
    (List.sumByCong (List.range 0 n) _ _ (j =>
      rewrite List.getZipWith4 f xs ys zs ws j,
          Option.mapMap4 f g (List.get xs j) (List.get ys j) (List.get zs j) (List.get ws j) in
        rfl))

theorem List.sumByZipWithExample: List.sumBy (List.zipWith [1, 2, 3] [10, 20] Nat.add) (x => x) = 33 :=
  List.sumByZipWith (x => x) Nat.add [1, 2, 3] [10, 20] 3 rfl

--| A sum over a range is the same over a longer one when the terms past the
--| shorter are 0.
theorem List.sumByRangeExtend ∀ (f: Nat → Nat) (n m: Nat)
    (le: n ≤ m)
    (zero: ∀ (j: Nat) => n ≤ j → f j = 0):
    List.sumBy (List.range 0 m) f = List.sumBy (List.range 0 n) f :=
  let rest :=
    List.sumByZeroIntro (List.rangeFrom (m - n) n) f (j mem => zero j (List.memRangeFrom j (m - n) n mem).left)
  calc List.sumBy (List.range 0 m) f
    _ = List.sumBy (List.range 0 n) f + List.sumBy (List.rangeFrom (m - n) n) f := List.sumByRangeSplit f n m le
    _ = List.sumBy (List.range 0 n) f := rewrite rest in omega

--| A sum over n + k indices whose first k terms are 0 is the sum of the rest,
--| counted from 0.
theorem List.sumByRangeSkipZeros ∀ (k: Nat) (f g: Nat → Nat) (n: Nat)
    (early: ∀ (i: Nat) => i < k → f i = 0)
    (later: ∀ (i: Nat) => f (k + i) = g i):
    List.sumBy (List.range 0 (n + k)) f = List.sumBy (List.range 0 n) g :=
  let first := List.sumByZeroIntro (List.range 0 k) f (i mem => early i (List.memRangeFrom i k 0 mem).right)
  let back: n + k - k = n := omega
  calc List.sumBy (List.range 0 (n + k)) f
    _ = List.sumBy (List.range 0 k) f + List.sumBy (List.rangeFrom (n + k - k) k) f :=
      List.sumByRangeSplit f k (n + k) omega
    _ = List.sumBy (List.rangeFrom n k) f := rewrite first, back in rfl
    _ = List.sumBy (List.range 0 n) (i => f (k + i)) := List.sumByRangeOffset f k n
    _ = List.sumBy (List.range 0 n) g := rewrite later _

--| `withIndexFrom s` of a list made by mapping over `withIndexFrom s`: the
--| indices are the same, so it is `withIndexFrom s xs` with each element
--| (index, element) pair sent to `(index, h pair)`.
theorem List.withIndexFromMap ∀ (s: Nat) (xs: List a) (h: (Nat, a) → b):
    List.withIndexFrom s (List.map (List.withIndexFrom s xs) h)
      = List.map (List.withIndexFrom s xs) (p => (p.fst, h p)) :=
  match xs with
    | [] => rfl
    | [x, ..rest] => Eq.cong (Cons (s, h (s, x))) (List.withIndexFromMap (Succ s) rest h)

--| Every index of `withIndexFrom t xs` is `t` or more.
theorem List.memWithIndexFromLe ∀ (t: Nat) (xs: List a) (p: (Nat, a))
    (member: p ∈ List.withIndexFrom t xs):
    t ≤ p.fst :=
  match xs, member with
    | [], member => Void.exfalso member
    | [x, ..rest], Inl same => rewrite <- same in Nat.leRefl t
    | [x, ..rest], Inr later =>
      let above := List.memWithIndexFromLe (Succ t) rest p later
      omega

--| `withIndexFrom s xs` has no repeats: its indices are all different.
theorem List.distinctWithIndexFrom ∀ (s: Nat) (xs: List a): List.Distinct (List.withIndexFrom s xs) := match xs with
  | [] => Trivial
  | [x, ..rest] =>
    Both
      (member =>
        let above := List.memWithIndexFromLe (Succ s) rest (s, x) member
        omega)
      (List.distinctWithIndexFrom (Succ s) rest)

--| `xs.withIndex` has no repeats, whether or not `xs` does.
theorem List.distinctWithIndex ∀ (xs: List a): List.Distinct xs.withIndex := List.distinctWithIndexFrom 0 xs

--| The positions `(s, t)`, `(s, t + 1)`, … of `withIndexFrom t xs` have no
--| repeats, for any fixed first part `s`.
theorem List.distinctWithIndexFromPaired ∀ (s: b) (t: Nat) (xs: List a):
    List.Distinct (List.map (List.withIndexFrom t xs) (p => (s, p.fst))) :=
  match xs with
    | [] => Trivial
    | [x, ..rest] =>
      Both
        (member =>
          Exists.elim (List.memMapElim (p => (s, p.fst)) (s, t) (List.withIndexFrom (Succ t) rest) member) (p both =>
            let above := List.memWithIndexFromLe (Succ t) rest p (And.left both)
            let same: p.fst = t := Eq.cong Pair.snd (And.right both)
            omega))
        (List.distinctWithIndexFromPaired s (Succ t) rest)
