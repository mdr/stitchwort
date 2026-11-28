--| Lemmas about filtering and searching: counts of distinct values,
--| `findMap`, `span`, `takeWhile`/`dropWhile`, maps of folds, and folds of
--| `Nat.max`, with the examples and tests that use them.

--| In a list without repeats, a value matches at most one element, and exactly
--| one when it is a member: `xs.count (== v)` is 1 if `xs.contains v` and 0 if
--| not. With [`List.lengthFilter`] this turns "the filter keeps exactly one"
--| into `xs.contains v`, e.g. for a fixed list of allowed names. The `Distinct`
--| argument for a literal list is `byDecision` (`import Std (byDecision)`);
--| it is not filled in by `auto`.
--| Example: `List.countEqDistinct "b" ["a", "b", "c"] byDecision` says
--| `["a", "b", "c"].count (== "b") = Bool.toNat (["a", "b", "c"].contains "b")`.
theorem List.countEqDistinct ∀ [auto eq: DecEq a] (v: a) (xs: List a)
    (h: List.Distinct xs):
    List.count xs (== v) = Bool.toNat (List.contains xs v) :=
  match xs, h with
    | [], d => byComputing
    | [y, ..ys], Both notMem d =>
      let finish: Bool.toNat (y == v) + Bool.toNat (List.contains ys v) = Bool.toNat (List.contains [y, ..ys] v) :=
        match same: y == v with
          | True =>
            match later: List.contains ys v with
              | True => Void.impossible (notMem (rewrite same.read then later.read))
              | False => byComputing
          | False => byComputing
      calc List.count [y, ..ys] (== v)
        _ = Bool.toNat (y == v) + List.count ys (== v) := List.countCons ys y (== v)
        _ = Bool.toNat (y == v) + Bool.toNat (List.contains ys v) :=
          Eq.cong (n => Bool.toNat (y == v) + n) (List.countEqDistinct v ys d)
        _ = Bool.toNat (List.contains [y, ..ys] v) := finish

--| What `(.find p)` finds passes any other test some element passes.
theorem List.findAny ∀ (xs: List a) (p q: a → Bool) (y: a)
    (qy: q y = True)
    (h: List.find xs p = Some y):
    List.any xs q = True :=
  match List.findSome xs p y h with | Both py m => Witness y (Both m qy)

--| With distinct keys, finding by an element's key finds that element (and
--| [`List.findKey`], std/List/SortLemmas.sw, says what is found has the key).
theorem List.findKeyDistinct ∀ [auto eq: DecEq k] (key: a → k):
    ∀ (xs: List a) => List.Distinct (List.map xs key) → ∀ (x: a) => x ∈ xs → List.find xs (y => key y == key x) = Some x
  | [], d, x, m => m.impossible
  | [z, ..zs], Both notMem d, x, Inl e => rewrite e, DecEq.refl (key x)
  | [z, ..zs], Both notMem d, x, Inr m =>
    match c: key z == key x with
      | True => Void.impossible (notMem (rewrite c.read then List.memMap zs x m key))
      | False => List.findKeyDistinct key zs d x m

theorem List.findKeyDistinctExample: List.find [(1, "a"), (2, "b")] (y => y.fst == 2) = Some (2, "b") :=
  List.findKeyDistinct Pair.fst
    [(1, "a"), (2, "b")]
    (Both
      (m =>
        match m with
          | Inl p => Nat.succNotZero 0 (Nat.succInjective p)
          | Inr v => v)
      (Both (m => m) Trivial))
    (2, "b")
    (Inr (Inl byComputing))

--| A key of part of the list is a key of the list.
theorem List.memMapOfSub ∀ (key: a → k) (s xs: List a)
    (sub: ∀ (y: a) => y ∈ s → y ∈ xs) (z: k)
    (m: z ∈ List.map s key):
    z ∈ List.map xs key :=
  List.anyElim (y => key y = z) (z ∈ List.map xs key) s (List.memMapAny s key z m) (y inS e =>
    rewrite <- e then List.memMap xs y (sub y inS) key)

--| Keeping some elements keeps their keys distinct.
theorem List.distinctMapFilter ∀ (xs: List a) (key: a → k) (p: a → Bool)
    (h: List.Distinct (List.map xs key)):
    List.Distinct (List.map (List.filter xs p) key) :=
  match xs, h with
    | [], d => Trivial
    | [x, ..xs], Both notMem d =>
      match e: p x with
        | True =>
          Both
            (m =>
              notMem
                (List.memMapOfSub key
                  (List.filter xs p)
                  xs
                  (y inFiltered =>
                    match List.memFilter xs p inFiltered with
                      | Both inXs py => inXs)
                  (key x)
                  m))
            (List.distinctMapFilter xs key p d)
        | False => List.distinctMapFilter xs key p d

--| Keeping some elements keeps them distinct.
theorem List.distinctFilter ∀ (xs: List a) (p: a → Bool) (h: List.Distinct xs): List.Distinct (List.filter xs p) :=
  match xs, h with
    | [], d => Trivial
    | [x, ..xs], Both notMem d =>
      match e: p x with
        | True => Both (m => notMem (List.memFilter xs p m).left) (List.distinctFilter xs p d)
        | False => List.distinctFilter xs p d

--| A key of a `filterMap`'s result is the key of an element it came from,
--| when each result has the key of its element.
theorem List.memMapFilterMap ∀ (f: a → Option b) (ka: a → k) (kb: b → k)
    (hk: ∀ (x: a) (y: b) => f x = Some y → kb y = ka x)
    (z: k) (xs: List a)
    (m: z ∈ List.map (List.filterMap xs f) kb):
    z ∈ List.map xs ka :=
  match xs with
    | [x, ..xs] =>
      match e: f x with
        | None => Inr (List.memMapFilterMap f ka kb hk z xs m)
        | Some y =>
          match m with
            | Inl q => Inl (Eq.trans (hk x y e).flipped q)
            | Inr r => Inr (List.memMapFilterMap f ka kb hk z xs r)

--| `filterMap` keeps keys distinct, when `f` keeps each element's key.
theorem List.distinctMapFilterMap ∀ (f: a → Option b) (ka: a → k) (kb: b → k)
    (hk: ∀ (x: a) (y: b) => f x = Some y → kb y = ka x) (xs: List a)
    (h: List.Distinct (List.map xs ka)):
    List.Distinct (List.map (List.filterMap xs f) kb) :=
  match xs, h with
    | [], d => Trivial
    | [x, ..xs], Both notMem d =>
      match e: f x with
        | None => List.distinctMapFilterMap f ka kb hk xs d
        | Some y =>
          Both
            (m => notMem (rewrite <- hk x y e then List.memMapFilterMap f ka kb hk (kb y) xs m))
            (List.distinctMapFilterMap f ka kb hk xs d)

--| Two lists with distinct keys and no key in common, joined, have distinct keys.
theorem List.distinctMapAppend ∀ (key: a → k) (xs ys: List a)
    (dx: List.Distinct (List.map xs key))
    (dy: List.Distinct (List.map ys key))
    (dj: List.Disjoint (List.map xs key) (List.map ys key)):
    List.Distinct (List.map (List.append xs ys) key) :=
  rewrite List.mapAppend xs ys key then List.distinctAppend (List.map xs key) (List.map ys key) dx dy dj

theorem List.distinctMapFilterExample: List.Distinct (List.map (List.filter [1, 2] (x => Nat.leq 2 x)) Succ) :=
  List.distinctMapFilter [1, 2] Succ (x => Nat.leq 2 x) List.distinctMapExample

--| `findMap` is the first of the `filterMap` results, found without building
--| the rest.
theorem List.findMapIsHeadFilterMap ∀ (xs: List a) (f: a → Option b):
    List.findMap xs f = List.head (List.filterMap xs f) :=
  match xs with
    | [] => byComputing
    | [x, ..xs] =>
      match f x with
        | None => List.findMapIsHeadFilterMap xs f
        | Some y => byComputing

--| What `List.findMap` finds, `f` gives for some element of the list; the
--| element that gave it is in the list ([`List.findMapIsHeadFilterMap`] says
--| which one, by way of `filterMap`).
theorem List.memOfFindMap ∀ (f: a → Option b) (xs: List a) (y: b)
    (found: List.findMap xs f = Some y):
    ∃ (x: a) => x ∈ xs ∧ f x = Some y :=
  match xs with
    | [x, ..xs] =>
      match c: f x with
        | Some z => Witness x (Both (Inl byComputing) (rewrite c then found))
        | None =>
          match List.memOfFindMap f xs y found with
            | Witness later (Both member made) => Witness later (Both (Inr member) made)

theorem List.lengthTails ∀ (xs: List a): List.length (List.tails xs) = Succ (List.length xs) := match xs with
  | [] => byComputing
  | [x, ..xs] => Eq.cong Succ (List.lengthTails xs)

theorem List.splitAtFst ∀ (xs: List a) (n: Nat): Pair.fst (List.splitAt xs n) = List.take xs n := byComputing

--| The loop's prefix is `takeWhile`'s, after what it had taken.
theorem List.spanOntoTakeDrop ∀ (p: a → Bool) (taken xs: List a):
    List.spanOnto taken p xs = MkPair (List.reverseOnto taken (List.takeWhile xs p)) (List.dropWhile xs p) :=
  match xs with
    | [] => byComputing
    | [x, ..xs] =>
      match p x with
        | True => List.spanOntoTakeDrop p [x, ..taken] xs
        | False => byComputing

--| `span` is `takeWhile` and `dropWhile`.
-- (its definition before it became one pass)
theorem List.spanTakeDrop ∀ (xs: List a) (p: a → Bool):
    List.span xs p = MkPair (List.takeWhile xs p) (List.dropWhile xs p) :=
  List.spanOntoTakeDrop p [] xs

theorem List.spanExample: List.span [1, 2, 3, 1] (x => Nat.leq x 2) = MkPair [1, 2] [3, 1] := byComputing

--| `takeWhile` over a prefix that passes: the prefix, then what passes after.
theorem List.takeWhileAppend ∀ (p: a → Bool) (rest prefix: List a)
    (all: List.all prefix p = True):
    List.takeWhile (List.append prefix rest) p = List.append prefix (List.takeWhile rest p) :=
  match prefix with
    | [] => byComputing
    | [x, ..xs] =>
      match p x with
        | True => Eq.cong (Cons x) (List.takeWhileAppend p rest xs all)

--| `dropWhile` over a prefix that passes drops it.
theorem List.dropWhileAppend ∀ (p: a → Bool) (rest prefix: List a)
    (all: List.all prefix p = True):
    List.dropWhile (List.append prefix rest) p = List.dropWhile rest p :=
  match prefix with
    | [] => byComputing
    | [x, ..xs] =>
      match p x with
        | True => List.dropWhileAppend p rest xs all

--| Where `takeWhile` takes nothing, `dropWhile` drops nothing.
theorem List.dropWhileStops ∀ (p: a → Bool) (xs: List a) (stops: List.takeWhile xs p = []): List.dropWhile xs p = xs :=
  match xs with
    | [] => byComputing
    | [x, ..xs] =>
      match p x with
        | False => byComputing

--| Where `takeWhile` took all of `read` from `read` followed by `rest`, it
--| takes nothing from `rest`: it stopped at `rest`'s start.
theorem List.takeWhileAppendStops ∀ (p: a → Bool) (read rest: List a)
    (taken: read = List.takeWhile (List.append read rest) p):
    List.takeWhile rest p = [] :=
  match read, taken with
    | [], taken => taken.flipped
    | [x, ..more], taken =>
      let unfolded: [x, ..more] = (if p x then [x, ..List.takeWhile (List.append more rest) p] else []) := taken
      match passed: p x with
        | True =>
          List.takeWhileAppendStops p more rest
            (List.consInjective x more (List.takeWhile (List.append more rest) p) unfolded)

--| What `takeWhile` takes and `dropWhile` leaves make up the list.
theorem List.takeWhileDropWhile ∀ (p: a → Bool) (xs: List a):
    List.append (List.takeWhile xs p) (List.dropWhile xs p) = xs :=
  match xs with
    | [] => byComputing
    | [x, ..xs] =>
      match p x with
        | True => Eq.cong (Cons x) (List.takeWhileDropWhile p xs)
        | False => byComputing

--| Taking from a mapped list while `p` holds is mapping what is taken from the
--| list while `p` of the mapped element holds.
theorem List.takeWhileMap ∀ (f: a → b) (p: b → Bool) (xs: List a):
    List.takeWhile (List.map xs f) p = List.map (List.takeWhile xs (x => p (f x))) f :=
  match xs with
    | [] => byComputing
    | [x, ..rest] => rewrite List.takeWhileMap f p rest then cases

--| Counting up from `start`, `takeWhile` stops by `cutoff` when nothing from
--| `cutoff` on passes, so any count reaching it gives the same.
theorem List.takeWhileRangeCutoff ∀ (p: Nat → Bool) (cutoff: Nat)
    (fails: ∀ (k: Nat) => cutoff ≤ k → p k = False) (n m start: Nat)
    (reachesN: cutoff ≤ start + n)
    (reachesM: cutoff ≤ start + m):
    List.takeWhile (List.rangeFrom n start) p = List.takeWhile (List.rangeFrom m start) p :=
  match n, m with
    | Zero, Zero => byComputing
    | Zero, Succ m => rewrite fails start arithmetic
    | Succ n, Zero => rewrite fails start arithmetic
    | Succ n, Succ m =>
      match passes: p start with
        | True => rewrite List.takeWhileRangeCutoff p cutoff fails n m (Succ start) arithmetic arithmetic
        | False => byComputing

--| Everything `takeWhile` takes passes.
theorem List.allTakeWhile ∀ (p: a → Bool) (xs: List a): List.all (List.takeWhile xs p) p = True := match xs with
  | [] => byComputing
  | [x, ..xs] =>
    match e: p x with
      | True => rewrite e then List.allTakeWhile p xs
      | False => byComputing

--| `span` of a prefix that passes, then a rest that starts with an element
--| that doesn't (or is empty), splits between the two.
theorem List.spanAppend ∀ (p: a → Bool) (taken rest: List a)
    (all: List.all taken p = True)
    (stops: List.takeWhile rest p = []):
    List.span (List.append taken rest) p = MkPair taken rest :=
  rewrite List.spanTakeDrop (List.append taken rest) p,
      List.takeWhileAppend p rest taken all,
      stops,
      List.appendNil taken,
      List.dropWhileAppend p rest taken all,
      List.dropWhileStops p rest stops

-- `map` through the other list functions (SW-198, day 8).

theorem List.mapAppend ∀ (xs ys: List a) (f: a → b):
    List.map (List.append xs ys) f = List.append (List.map xs f) (List.map ys f) :=
  match xs with
    | [] => byComputing
    | [x, ..xs] => rewrite List.mapAppend xs ys f

theorem List.takeMap ∀ (xs: List a) (k: Nat) (f: a → b): List.take (List.map xs f) k = List.map (List.take xs k) f :=
  match xs, k with
    | xs, Zero => byComputing
    | [], Succ k => byComputing
    | [x, ..xs], Succ k => rewrite List.takeMap xs k f

--| The first `k` of two lists combined are the first `k` of each combined.
theorem List.takeZipWith ∀ (f: a → b → c) (xs: List a) (ys: List b) (k: Nat):
    List.take (List.zipWith xs ys f) k = List.zipWith (List.take xs k) (List.take ys k) f :=
  match xs, ys, k with
    | xs, ys, Zero => byComputing
    | [], ys, Succ k => byComputing
    | [x, ..xs], [], Succ k => byComputing
    | [x, ..xs], [y, ..ys], Succ k => Eq.cong (Cons (f x y)) (List.takeZipWith f xs ys k)

theorem List.takeZipWithExample: List.take (List.zipWith [1, 2, 3] [10, 20, 30] Nat.add) 2
      = List.zipWith [1, 2] [10, 20] Nat.add :=
  List.takeZipWith Nat.add [1, 2, 3] [10, 20, 30] 2

theorem List.foldLeftMap ∀ (xs: List a) (z: c) (f: c → b → c) (g: a → b):
    List.foldLeft (List.map xs g) z f = List.foldLeft xs z (acc x => f acc (g x)) :=
  match xs with
    | [] => byComputing
    | [x, ..xs] => List.foldLeftMap xs (f z (g x)) f g

--| A fold over `zipWith` folds over the pairs, combining each as it goes.
theorem List.foldLeftZipWith ∀ (g: a → b → c) (f: d → c → d) (xs: List a) (ys: List b) (z: d):
    List.foldLeft (List.zipWith xs ys g) z f = List.foldLeft (List.zip xs ys) z (acc p => f acc (g p.fst p.snd)) :=
  match xs, ys with
    | [], ys => byComputing
    | [x, ..xs], [] => byComputing
    | [x, ..xs], [y, ..ys] => List.foldLeftZipWith g f xs ys (f z (g x y))

--| A fold over `zip xs ys` whose step uses only each pair's first element is
--| the fold over `xs`, when `ys` is at least as long.
theorem List.foldLeftZipLeft ∀ (step: c → Pair a b → c) (f: c → a → c)
    (same: ∀ (acc: c) (x: a) (y: b) => step acc (MkPair x y) = f acc x)
    (xs: List a) (ys: List b) (z: c)
    (le: List.length xs ≤ List.length ys):
    List.foldLeft (List.zip xs ys) z step = List.foldLeft xs z f :=
  match xs, ys with
    | [], ys => byComputing
    | [x, ..xs], [y, ..ys] => rewrite same z x y then List.foldLeftZipLeft step f same xs ys (f z x) le

theorem List.foldRightZipLeft ∀ (step: Pair a b → c → c) (f: a → c → c)
    (same: ∀ (x: a) (y: b) (acc: c) => step (MkPair x y) acc = f x acc)
    (xs: List a) (ys: List b) (z: c)
    (le: List.length xs ≤ List.length ys):
    List.foldRight (List.zip xs ys) z step = List.foldRight xs z f :=
  match xs, ys with
    | [], ys => byComputing
    | [x, ..xs], [y, ..ys] =>
      calc List.foldRight [MkPair x y, ..List.zip xs ys] z step
        _ = step (MkPair x y) (List.foldRight (List.zip xs ys) z step) :=
          List.foldRightCons (List.zip xs ys) (MkPair x y) z step
        _ = f x (List.foldRight (List.zip xs ys) z step) := same x y (List.foldRight (List.zip xs ys) z step)
        _ = f x (List.foldRight xs z f) := rewrite List.foldRightZipLeft step f same xs ys z le
        _ = List.foldRight [x, ..xs] z f := (List.foldRightCons xs x z f).flipped

test "List.foldLeftZipLeft" :=
  List.foldLeft (List.zip [1, 2, 3] ["a", "b", "c", "d"]) 0 (acc pair => acc + pair.fst) == 6

theorem List.anyMap ∀ (xs: List a) (p: b → Bool) (f: a → b): List.any (List.map xs f) p = List.any xs (x => p (f x)) :=
  match xs with
    | [] => byComputing
    | [x, ..xs] => rewrite List.anyMap xs p f

--| `List.all` of a `map` is `List.all` of the composed test. ([`List.allMap`] is about the proposition `List.All`.)
theorem List.allMapBool ∀ (xs: List a) (p: b → Bool) (f: a → b):
    List.all (List.map xs f) p = List.all xs (x => p (f x)) :=
  match xs with
    | [] => byComputing
    | [x, ..xs] => rewrite List.allMapBool xs p f

--| Some element of a `flatMap` passes exactly when some list it is made of
--| has one.
theorem List.anyFlatMap ∀ (f: a → List b) (p: b → Bool) (xs: List a):
    List.any (List.flatMap xs f) p = List.any xs (x => List.any (f x) p) :=
  match xs with
    | [] => byComputing
    | [x, ..xs] =>
      Eq.trans
        (List.anyAppend (f x) (List.flatMap xs f) p)
        (Eq.cong (later => List.any (f x) p ∨ later) (List.anyFlatMap f p xs))

--| `List.any` of an `∨` is the `∨` of the `List.any`s.
theorem List.anyOr ∀ (p q: a → Bool) (xs: List a): List.any xs (x => p x ∨ q x) = (List.any xs p ∨ List.any xs q) :=
  match xs with
    | [] => byComputing
    | [x, ..xs] => rewrite List.anyOr p q xs then cases

--| Two `List.any`s, in either order.
theorem List.anyComm ∀ (related: a → b → Bool) (ys: List b) (xs: List a):
    List.any xs (x => List.any ys (y => related x y)) = List.any ys (y => List.any xs (x => related x y)) :=
  match xs with
    | [] => Eq.flipped (List.anyFalse ys (y => False) (y => byComputing))
    | [x, ..xs] =>
      rewrite List.anyComm related ys xs then
        Eq.flipped (List.anyOr (y => related x y) (y => List.any xs (other => related other y)) ys)

theorem List.anyFlatMapExample: List.any (List.flatMap [1, 2] (x => [x, x * 10])) (== 20)
      = List.any [1, 2] (x => List.any [x, x * 10] (== 20)) :=
  List.anyFlatMap (x => [x, x * 10]) (== 20) [1, 2]

theorem List.countMap ∀ (xs: List a) (p: b → Bool) (f: a → b):
    List.count (List.map xs f) p = List.count xs (x => p (f x)) :=
  List.foldLeftMap xs 0 (n x => Nat.succIf n (p x)) f

theorem List.occurrencesMap ∀ (xs: List a) (f: a → b) (p: b → Bool):
    List.occurrences (List.map xs f) p = List.occurrences xs (x => p (f x)) :=
  match xs with
    | [] => byComputing
    | [x, ..xs] => rewrite List.occurrencesMap xs f p

--| Mapping both lists of a permutation keeps it one.
theorem List.permMap ∀ (xs ys: List a) (h: List.Perm xs ys) (f: a → b): List.Perm (List.map xs f) (List.map ys f) :=
  p => rewrite List.occurrencesMap xs f p, List.occurrencesMap ys f p then h (x => p (f x))

--| Counting what `(.filter keep)` kept is counting what passes both tests.
theorem List.occurrencesFilter ∀ (xs: List a) (keep p: a → Bool):
    List.occurrences (List.filter xs keep) p = List.occurrences xs (x => p x ∧ keep x) :=
  match xs with
    | [] => byComputing
    | [x, ..xs] =>
      match e: keep x with
        | True | False =>
          rewrite List.occurrencesFilter xs keep p then
            match p x with
              | True | False => byComputing

--| The first k numbers of a longer run.
theorem List.takeRangeFrom ∀ (k n s: Nat) (h: k ≤ n): List.take (List.rangeFrom n s) k = List.rangeFrom k s :=
  match k, n with
    | Zero, n => byComputing
    | Succ k, Succ n => rewrite List.takeRangeFrom k n (Succ s) h

--| The pairs of a mapped list are the list's pairs, mapped.
theorem List.pairsMap ∀ (xs: List a) (f: a → b):
    List.pairs (List.map xs f) = List.map (List.pairs xs) (p => MkPair (f (Pair.fst p)) (f (Pair.snd p))) :=
  match xs with
    | [] => byComputing
    | [x, ..xs] =>
      rewrite List.mapAppend (List.map xs (y => MkPair x y)) (List.pairs xs) (p =>
            MkPair (f (Pair.fst p)) (f (Pair.snd p))),
          List.mapMap xs (y => MkPair (f x) y) f,
          List.mapMap xs (p => MkPair (f (Pair.fst p)) (f (Pair.snd p))) (y => MkPair x y),
          List.pairsMap xs f

--| A `filterMap` that keeps every element, changed by `g`, is a `map`.
theorem List.filterMapSomeMem ∀ (xs: List a) (f: a → Option b) (g: a → b)
    (h: ∀ (x: a) => x ∈ xs → f x = Some (g x)):
    List.filterMap xs f = List.map xs g :=
  Eq.trans (List.filterMapCongMem xs f (x => Some (g x)) h) (List.filterMapSome xs g)

--| A `filterMap` that keeps every element as it is gives the list back.
theorem List.filterMapAll ∀ (f: a → Option a) (xs: List a)
    (h: ∀ (x: a) => x ∈ xs → f x = Some x):
    List.filterMap xs f = xs :=
  match xs with
    | [] => byComputing
    | [x, ..xs] => rewrite h x (Inl byComputing) then Eq.cong (Cons x) (List.filterMapAll f xs (y m => h y (Inr m)))

--| `filterMap` after `map`, when each element maps back to itself.
theorem List.filterMapMapSelf ∀ (g: a → b) (f: b → Option a) (xs: List a)
    (h: ∀ (x: a) => x ∈ xs → f (g x) = Some x):
    List.filterMap (List.map xs g) f = xs :=
  Eq.trans (List.filterMapMap xs f g) (List.filterMapAll (x => f (g x)) xs h)

test "List.pairsMap" :=
  (List.map [1, 2, 3] Succ).pairs == List.map [1, 2, 3].pairs (p => MkPair (Succ p.fst) (Succ p.snd))

-- the largest by folding Nat.max --------------------------------------------

--| The fold starts at `start` and never goes down.
theorem List.foldMaxGe ∀ (xs: List Nat) (start: Nat): start ≤ List.foldLeft xs start Nat.max := match xs with
  | [] => Nat.leRefl start
  | [x, ..xs] =>
    Nat.leTrans start
      (Nat.max start x)
      (List.foldLeft xs (Nat.max start x) Nat.max)
      (Nat.leMaxLeft start x)
      (List.foldMaxGe xs (Nat.max start x))

--| Every element is at most the largest.
theorem List.leFoldMax ∀ (xs: List Nat) (x start: Nat) (h: x ∈ xs): x ≤ List.foldLeft xs start Nat.max :=
  match xs, h with
    | [], m => m.impossible
    | [y, ..ys], Inl e =>
      rewrite <- e then
        Nat.leTrans y
          (Nat.max start y)
          (List.foldLeft ys (Nat.max start y) Nat.max)
          (Nat.leMaxRight start y)
          (List.foldMaxGe ys (Nat.max start y))
    | [y, ..ys], Inr m => List.leFoldMax ys x (Nat.max start y) m

--| The largest is the start or one of the elements.
theorem List.foldMaxMem ∀ (xs: List Nat) (start: Nat):
    (List.foldLeft xs start Nat.max = start) ∨ (List.foldLeft xs start Nat.max ∈ xs) :=
  match xs with
    | [] => Inl byComputing
    | [y, ..ys] =>
      match List.foldMaxMem ys (Nat.max start y) with
        | Inr m => Inr (Inr m)
        | Inl e =>
          match h: Nat.leq start y with
            | True => Inr (Inl e.flipped)
            | False => Inl e

-- lengths, and sums over ranges ---------------------------------------------

--| Zipping two lists of at least n elements gives at least n.
theorem List.lengthZipWithAtLeast: ∀ (u: List a) (n: Nat) (v: List b) => n ≤ List.length u
      → n ≤ List.length v
      → ∀ (f: a → b → c) => n ≤ List.length (List.zipWith u v f)
  | u, Zero, v, hu, hv, f => byComputing
  | [], Succ n, v, hu, hv, f => hu
  | [x, ..xs], Succ n, [], hu, hv, f => hv
  | [x, ..xs], Succ n, [y, ..ys], hu, hv, f => List.lengthZipWithAtLeast xs n ys hu hv f

--| A sum over the numbers below b is the sum below t and the sum from t up to b.
theorem List.sumByRangeSplit ∀ (f: Nat → Nat) (t b: Nat)
    (tb: t ≤ b):
    List.sumBy (List.rangeFrom b 0) f = List.sumBy (List.rangeFrom t 0) f + List.sumBy (List.rangeFrom (b - t) t) f :=
  calc List.sumBy (List.rangeFrom b 0) f
    _ = List.sumBy (List.rangeFrom (t + (b - t)) 0) f :=
      Eq.cong (n => List.sumBy (List.rangeFrom n 0) f) (Nat.addSubCancel t b tb).flipped
    _ = List.sumBy (List.append (List.rangeFrom t 0) (List.rangeFrom (b - t) (0 + t))) f :=
      Eq.cong (.sumBy f) (List.rangeFromAppend t (b - t) 0)
    _ = List.sumBy (List.rangeFrom t 0) f + List.sumBy (List.rangeFrom (b - t) t) f :=
      List.sumByAppend (List.rangeFrom t 0) (List.rangeFrom (b - t) t) f

-- sums of zero -----------------------------------------------------------------

--| A sum of numbers is 0 only if each is.
theorem List.sumByZeroElim: ∀ (xs: List a) (f: a → Nat) => List.sumBy xs f = 0 → ∀ (x: a) => x ∈ xs → f x = 0
  | [], f, h, x, m => m.impossible
  | [y, ..ys], f, h, x, Inl e =>
    rewrite <- e then (Nat.addEqZero (f y) (List.sumBy ys f) (Eq.trans (List.sumByCons ys y f).flipped h)).left
  | [y, ..ys], f, h, x, Inr m =>
    List.sumByZeroElim ys f
      (Nat.addEqZero (f y) (List.sumBy ys f) (Eq.trans (List.sumByCons ys y f).flipped h)).right
      x
      m

theorem List.sumByZeroIntro ∀ (xs: List a) (f: a → Nat) (h: ∀ (x: a) => x ∈ xs → f x = 0): List.sumBy xs f = 0 :=
  match xs with
    | [] => byComputing
    | [y, ..ys] => rewrite List.sumByCons ys y f, h y (Inl byComputing), List.sumByZeroIntro ys f (x m => h x (Inr m))

-- filtering what can't pass anyway ------------------------------------------

--| Dropping elements that fail `q`, when only elements that pass `q` can pass
--| `p`, changes neither `any p` nor `count p`.
theorem List.anyFilter ∀ (xs: List a) (p q: a → Bool)
    (h: ∀ (x: a) => p x = True → q x = True):
    List.any (List.filter xs q) p = List.any xs p :=
  match xs with
    | [] => byComputing
    | [x, ..xs] =>
      match e: q x with
        | True => rewrite List.anyFilter xs p q h
        | False =>
          match f: p x with
            | True => Void.impossible (Bool.falseNotTrue (Eq.trans e.flipped (h x f)))
            | False => List.anyFilter xs p q h

theorem List.countFromFilter ∀ (xs: List a) (n: Nat) (p q: a → Bool)
    (h: ∀ (x: a) => p x = True → q x = True):
    List.foldLeft (List.filter xs q) n (k x => Nat.succIf k (p x)) = List.foldLeft xs n (k x => Nat.succIf k (p x)) :=
  match xs with
    | [] => byComputing
    | [x, ..xs] =>
      match e: q x with
        | True => List.countFromFilter xs (Nat.succIf n (p x)) p q h
        | False =>
          match f: p x with
            | True => Void.impossible (Bool.falseNotTrue (Eq.trans e.flipped (h x f)))
            | False => List.countFromFilter xs n p q h

theorem List.countFilter ∀ (xs: List a) (p q: a → Bool)
    (h: ∀ (x: a) => p x = True → q x = True):
    List.count (List.filter xs q) p = List.count xs p :=
  List.countFromFilter xs 0 p q h

-- membership through zip, take, drop and filter ------------------------------

--| A pair in `List.zip xs ys` is an element of `xs` with one of `ys`.
theorem List.memZip ∀ (p: (a, b)) (xs: List a) (ys: List b) (h: p ∈ List.zip xs ys): (p.fst ∈ xs) ∧ (p.snd ∈ ys) :=
  match xs, ys, h with
    | [], ys, m => m.impossible
    | [x, ..xs], [], m => m.impossible
    | [x, ..xs], [y, ..ys], Inl e => rewrite <- e then Both (Inl byComputing) (Inl byComputing)
    | [x, ..xs], [y, ..ys], Inr m =>
      match List.memZip p xs ys m with
        | Both inXs inYs => Both (Inr inXs) (Inr inYs)

theorem List.memTake ∀ (xs: List a) (v: a) (n: Nat) (h: v ∈ List.take xs n): v ∈ xs := match xs, n, h with
  | xs, Zero, m => m.impossible
  | [], Succ n, m => m
  | [x, ..xs], Succ n, Inl e => Inl e
  | [x, ..xs], Succ n, Inr m => Inr (List.memTake xs v n m)

theorem List.memDrop ∀ (xs: List a) (v: a) (n: Nat) (m: v ∈ List.drop xs n): v ∈ xs := match xs, n with
  | xs, Zero => m
  | [x, ..xs], Succ n => Inr (List.memDrop xs v n m)

--| Filtering a mapped list is mapping the filtered list.
theorem List.filterOfMap ∀ (xs: List a) (q: b → Bool) (g: a → b):
    List.filter (List.map xs g) q = List.map (List.filter xs (x => q (g x))) g :=
  match xs with
    | [] => byComputing
    | [x, ..xs] =>
      match e: q (g x) with
        | True => rewrite List.filterOfMap xs q g
        | False => List.filterOfMap xs q g

--| A pair in `List.pairs xs` is two elements of `xs`.
theorem List.memPairs ∀ (p: (a, a)) (xs: List a) (m: p ∈ List.pairs xs): (p.fst ∈ xs) ∧ (p.snd ∈ xs) := match xs with
  | [x, ..xs] =>
    match List.memAppend p (List.map xs (y => (x, y))) (List.pairs xs) m with
      | Inl first =>
        List.anyElim
          (y => (x, y) = p)
          ((p.fst ∈ [x, ..xs]) ∧ (p.snd ∈ [x, ..xs]))
          xs
          (List.memMapAny xs (y => (x, y)) p first)
          (y inXs e => rewrite <- e then Both (Inl byComputing) (Inr inXs))
      | Inr later =>
        match List.memPairs p xs later with
          | Both one other => Both (Inr one) (Inr other)

--| A pair in a list mapped to pairs with a fixed first part: that part, and a member of the list.
theorem List.memMapPair ∀ (c u: a) (v: b) (xs: List b): ((u, v) ∈ List.map xs (y => (c, y))) ↔ ((u = c) ∧ (v ∈ xs)) := {
  forward = m =>
    Exists.elim (List.memMapElim (y => (c, y)) (u, v) xs m) (y both =>
      Both (Pair.mkInjectiveFst both.right).flipped (rewrite <- Pair.mkInjectiveSnd both.right then And.left both)),
  backward = both => rewrite And.left both then List.memMap xs v both.right (y => (c, y))
}

--| Taking apart a pair of `List.pairs (Cons x rest)`: `x` with a later element, or a pair of `rest`.
--| (Each way round, so a proof can use it both to take a pair apart and to put one together.)
theorem List.memPairsCons ∀ (u v x: a) (rest: List a):
    ((u, v) ∈ List.pairs [x, ..rest]) ↔ (((u = x) ∧ (v ∈ rest)) ∨ ((u, v) ∈ List.pairs rest)) :=
  {
    forward = m =>
      match List.memAppend (u, v) (List.map rest (y => (x, y))) (List.pairs rest) m with
        | Inl inMap => Inl ((List.memMapPair x u v rest).forward inMap)
        | Inr inRest => Inr inRest,
    backward = h =>
      match h with
        | Inl both =>
          List.memAppendLeft
            (u, v)
            (List.map rest (y => (x, y)))
            (List.pairs rest)
            ((List.memMapPair x u v rest).backward both)
        | Inr inRest => List.memAppendRight (u, v) (List.map rest (y => (x, y))) (List.pairs rest) inRest
  }

theorem List.memPairsConsExample: (1, 3) ∈ List.pairs [1, 2, 3] :=
  (List.memPairsCons 1 3 1 [2, 3]).backward (Inl (Both byComputing (Inr (Inl byComputing))))

--| The last element, if there is one, is an element.
theorem List.lastMem ∀ (xs: List a) (x: a) (h: List.last xs = Some x): x ∈ xs := match xs with
  | [y] => Inl (Option.someInjective h)
  | [y, z, ..zs] => Inr (List.lastMem [z, ..zs] x h)

theorem List.lastMemExample: 3 ∈ [1, 2, 3] := List.lastMem [1, 2, 3] 3 byComputing

--| The last element of a list with `x` added at the end is `x`.
theorem List.lastSnoc ∀ (x: a) (xs: List a): List.last (List.append xs [x]) = Some x := match xs with
  | [] | [_] => byComputing
  | [y, z, ..zs] => List.lastSnoc x [z, ..zs]

--| `filterMap` keeps `y` when an element maps to `Some y`.
theorem List.memFilterMapIntro ∀ (f: a → Option b) (x: a) (y: b) (xs: List a)
    (h: x ∈ xs)
    (e: f x = Some y):
    y ∈ List.filterMap xs f :=
  match xs, h with
    | [], m => m.impossible
    | [z, ..zs], Inl q => rewrite q, e then Inl byComputing
    | [z, ..zs], Inr m =>
      match c: f z with
        | None => List.memFilterMapIntro f x y zs m e
        | Some w => Inr (List.memFilterMapIntro f x y zs m e)

--| What `filterMap` keeps is `Some` of some element.
theorem List.memFilterMapElim ∀ (f: a → Option b) (y: b) (xs: List a)
    (m: y ∈ List.filterMap xs f):
    List.Any (x => f x = Some y) xs :=
  match xs with
    | [z, ..zs] =>
      match c: f z with
        | None => Inr (List.memFilterMapElim f y zs m)
        | Some w =>
          match m with
            | Inl q => Inl (Eq.cong Some q)
            | Inr r => Inr (List.memFilterMapElim f y zs r)

--| What `filterMap` keeps is exactly the `Some` results of the elements: `y` is in `xs.filterMap f`
--| just when some element `x` of `xs` has `f x = Some y`. This is [`List.memFilterMapIntro`] and
--| [`List.memFilterMapElim`] as one statement, to rewrite with. It holds for `filterMap (match some | …)`
--| as for any `f`.
theorem List.memFilterMap ∀ (f: a → Option b) (y: b) (xs: List a):
    (y ∈ List.filterMap xs f) ↔ (∃ (x: a) => (x ∈ xs) ∧ (f x = Some y)) :=
  {
    forward = m => List.anyMember (x => f x = Some y) xs (List.memFilterMapElim f y xs m),
    backward = found => Exists.elim found (x both => List.memFilterMapIntro f x y xs both.left both.right)
  }

--| `somes` keeps `y` exactly when `Some y` is an element.
theorem List.memSomes ∀ (y: a) (xs: List (Option a)): (y ∈ List.somes xs) ↔ (Some y ∈ xs) := {
  forward = m =>
    Exists.elim ((List.memFilterMap id y xs).forward m) (x both =>
      Eq.subst (z => z ∈ xs) (And.right both: x = Some y) both.left),
  backward = m => (List.memFilterMap id y xs).backward (Witness (Some y) (Both m (byComputing: id (Some y) = Some y)))
}

--| Everything `filterMap` keeps has `q` when every element's `Some` result
--| would; and back.
theorem List.allFilterMap ∀ (q: b → Prop) (f: a → Option b) (xs: List a)
    (h1: List.All (x => ∀ (y: b) => f x = Some y → q y) xs):
    List.All q (List.filterMap xs f) :=
  match xs, h1 with
    | [], h => Trivial
    | [z, ..zs], Both hz h =>
      match c: f z with
        | None => List.allFilterMap q f zs h
        | Some w => Both (hz w byComputing) (List.allFilterMap q f zs h)

theorem List.allFilterMapElim ∀ (q: b → Prop) (f: a → Option b) (xs: List a)
    (h: List.All q (List.filterMap xs f)):
    List.All (x => ∀ (y: b) => f x = Some y → q y) xs :=
  match xs with
    | [] => Trivial
    | [z, ..zs] =>
      match c: f z with
        | None => Both (y e => (Option.noneNotSome y e).impossible) (List.allFilterMapElim q f zs h)
        | Some w =>
          match h with
            | Both hw rest =>
              Both (y e => rewrite <- Option.someInjective e then hw) (List.allFilterMapElim q f zs rest)

theorem List.memFilterMapExample: 4 ∈ List.filterMap [1, 2, 3] (x => if x == 2 then Some (x * 2) else None) :=
  List.memFilterMapIntro (x => if x == 2 then Some (x * 2) else None) 2 4 [1, 2, 3] (Inr (Inl byComputing)) byComputing

--| Counting the values of a `filterMap` that pass `p` counts the elements
--| whose value passes: `(xs.filterMap f).count p = xs.count (x => (f x).any p)`.
--| An element with no value (`f x = None`) is counted by neither side.
theorem List.countFilterMap ∀ (f: a → Option b) (p: b → Bool) (xs: List a):
    (xs.filterMap f).count p = xs.count (x => (f x).any p) :=
  match xs with
    | [] => byComputing
    | [x, ..rest] =>
      rewrite List.countCons rest x (x => (f x).any p) then
        match f x with
          | None => rewrite List.countFilterMap f p rest
          | Some y => rewrite List.countCons (rest.filterMap f) y p, List.countFilterMap f p rest

--| Counting one value `wanted` among the results of a `filterMap` is counting
--| the elements that give `Some wanted`. The `==` form of
--| [`List.countFilterMap`].
theorem List.countFilterMapEq ∀ [auto eq: DecEq b] (f: a → Option b) (wanted: b) (xs: List a):
    (xs.filterMap f).count (== wanted) = xs.count (x => f x == Some wanted) :=
  match xs with
    | [] => byComputing
    | [x, ..rest] =>
      rewrite List.countCons rest x (y => f y == Some wanted) then
        match e: f x with
          | None => List.countFilterMapEq f wanted rest
          | Some found =>
            rewrite List.countCons (rest.filterMap f) found (== wanted), Option.someBeqSome found wanted then
              Eq.cong (count => Bool.toNat (found == wanted) + count) (List.countFilterMapEq f wanted rest)

--| `filterMap` keeps at most every element.
theorem List.lengthFilterMapLe ∀ (f: a → Option b) (xs: List a): (xs.filterMap f).length ≤ xs.length := match xs with
  | [] => byComputing
  | [x, ..rest] =>
    let shorter := List.lengthFilterMapLe f rest
    match f x with
      | None | Some _ => arithmetic

--| A `filterMap` to `Bool`s is as long as the number of elements that give
--| `Some True` plus the number that give `Some False`: every value it keeps is
--| one or the other.
theorem List.lengthFilterMapBool ∀ (f: a → Option Bool) (xs: List a):
    (xs.filterMap f).length = xs.count (x => f x == Some True) + xs.count (x => f x == Some False) :=
  match xs with
    | [] => byComputing
    | [x, ..rest] =>
      rewrite List.countCons rest x (x => f x == Some True), List.countCons rest x (x => f x == Some False) then
        match f x with
          | None => List.lengthFilterMapBool f rest
          | Some True => rewrite List.lengthFilterMapBool f rest
          | Some False => rewrite List.lengthFilterMapBool f rest then arithmetic

--| Mapping over a `concat` is the `concat` of mapping over each part.
theorem List.mapConcat ∀ (xss: List (List a)) (k: a → b): xss.concat.map k = (xss.map (xs => xs.map k)).concat :=
  match xss with
    | [] => byComputing
    | [xs, ..rest] => rewrite List.mapAppend xs (List.concat rest) k, List.mapConcat rest k

--| A list whose keys are distinct is distinct. The converse needs `key` to
--| be injective ([`List.distinctMap`]).
theorem List.distinctOfMap ∀ (key: a → k) (xs: List a) (h: List.Distinct (xs.map key)): List.Distinct xs :=
  match xs, h with
    | [], distinct => Trivial
    | [x, ..rest], Both fresh distinct =>
      Both (member => fresh (List.memMap rest x member key)) (List.distinctOfMap key rest distinct)

--| Putting an element not in a list with no repeats at its end leaves no
--| repeats. (`List.uniqueSnoc` is about the function `List.unique`.)
theorem List.distinctSnoc ∀ (xs: List a) (y: a) (out: y ∉ xs) (h: List.Distinct xs): List.Distinct (xs ++ [y]) :=
  match xs, h with
    | [], distinct => Both (m => m) Trivial
    | [x, ..xs], Both xOut distinct =>
      Both
        (m =>
          match List.memAppend x xs [y] m with
            | Inl inRest => xOut inRest
            | Inr (Inl same) => out (Inl same.flipped)
            | Inr (Inr none) => none)
        (List.distinctSnoc xs y (m => out (Inr m)) distinct)

--| Replacing one element of a list with no repeats by one that is not among
--| the others leaves no repeats: `before ++ [x, ..after]` becomes
--| `before ++ [y, ..after]` when `y` is not in `before ++ after`.
theorem List.distinctSwapMiddle ∀ (x y: a) (after before: List a)
    (h: List.Distinct (before ++ [x, ..after]))
    (fresh: y ∉ before ++ after):
    List.Distinct (before ++ [y, ..after]) :=
  match before, h with
    | [], Both notMem rest => Both fresh rest
    | [first, ..others], Both notMem rest =>
      let away: first ∉ others ++ [y, ..after] := inside =>
        match List.memAppend first others [y, ..after] inside with
          | Inl early => notMem (List.memAppendLeft first others [x, ..after] early)
          | Inr (Inl same) => fresh (Inl same.flipped)
          | Inr (Inr late) => notMem (List.memAppendRight first others [x, ..after] (Inr late))
      Both away (List.distinctSwapMiddle x y after others rest (inside => fresh (Inr inside)))

--| A `filterMap` whose function never gives the same value for two different
--| elements keeps a list free of repeats free of repeats. See
--| [`List.distinctMapFilterMap`] when only a key of the values is known to
--| be determined by the element.
theorem List.distinctFilterMap ∀ (f: a → Option b)
    (inj: ∀ (x z: a) (y: b) => f x = Some y → f z = Some y → x = z) (xs: List a)
    (h: List.Distinct xs):
    List.Distinct (List.filterMap xs f) :=
  match xs, h with
    | [], d => Trivial
    | [x, ..xs], Both notMem d =>
      match e: f x with
        | None => List.distinctFilterMap f inj xs d
        | Some y =>
          Both
            (m =>
              List.anyElim (z => f z = Some y) Void xs (List.memFilterMapElim f y xs m) (z inXs fz =>
                notMem (rewrite inj x z y e fz then inXs)))
            (List.distinctFilterMap f inj xs d)

--| What is in a suffix of a list is in the list: the elements of any member
--| of `xs.tails` are elements of `xs`.
theorem List.memOfMemTails ∀ (x: a) (xs later: List a) (h: later ∈ xs.tails) (inLater: x ∈ later): x ∈ xs :=
  match xs, h with
    | [], Inl same => rewrite Eq.flipped same at inLater then inLater
    | [], Inr none => none.impossible
    | [first, ..rest], Inl same => rewrite Eq.flipped same at inLater then inLater
    | [first, ..rest], Inr deeper => Inr (List.memOfMemTails x rest later deeper inLater)

--| What holds of every element and its image under `g` holds along a zip of
--| a list with that `zipWith`: `xs.zip (xs.zipWith ys g)` pairs each `x` with
--| `g x y` for the `y` in its place.
theorem List.allZipWithSelf ∀ (holds: a → c → Prop) (g: a → b → c) (each: ∀ (x: a) (y: b) => holds x (g x y))
    (xs: List a) (ys: List b):
    List.All (pair => holds pair.fst pair.snd) (xs.zip (xs.zipWith ys g)) :=
  match xs, ys with
    | [], ys => Trivial
    | [x, ..rest], [] => Trivial
    | [x, ..rest], [y, ..others] => Both (each x y) (List.allZipWithSelf holds g each rest others)

--| A member of a list of rows that all have length `n` has length `n`.
theorem List.allLengthMem ∀ [row: List a] (rows: List (List a)) (n: Nat)
    (h: List.AllLength n rows)
    (member: row ∈ rows):
    row.length = n :=
  match rows, h, member with
    | [], sized, member => member.impossible
    | [first, ..rest], Both sized more, Inl same => rewrite <- same then sized
    | [first, ..rest], Both sized more, Inr later => List.allLengthMem rest n more later

--| `reverseOnto` keeps every row the length `n`: reversing `xs` onto `acc`
--| gives rows all of length `n` when `xs` and `acc` have.
theorem List.allLengthReverseOnto ∀ (n: Nat) (xs acc: List (List a))
    (h: List.AllLength n xs)
    (accSized: List.AllLength n acc):
    List.AllLength n (List.reverseOnto xs acc) :=
  match xs, h with
    | [], sized => accSized
    | [x, ..rest], Both sized more => List.allLengthReverseOnto n rest [x, ..acc] more (Both sized accSized)

--| `List.all` and `List.any` (the `Bool`s a program computes) are `List.All`
--| and `List.Any` (the propositions proofs use), so a lemma needs only one
--| form.
theorem List.allToAll ∀ (p: a → Bool) (xs: List a) (h: List.all xs p = True): List.All (x => p x = True) xs :=
  match xs with
    | [] => Trivial
    | [x, ..xs] =>
      match c: p x with
        | True => Both byComputing (List.allToAll p xs h)

theorem List.allOfAll ∀ (p: a → Bool) (xs: List a) (h1: List.All (x => p x = True) xs): List.all xs p = True :=
  match xs, h1 with
    | [], h => byComputing
    | [x, ..xs], Both px h => rewrite px then List.allOfAll p xs h

theorem List.allIff ∀ (xs: List a) (p: a → Bool): List.all xs p = True ↔ List.All (x => p x = True) xs :=
  { forward = List.allToAll p xs, backward = List.allOfAll p xs }

--| `List.all` holds of each member.
theorem List.allMember ∀ (p: a → Bool) (xs: List a) (all: List.all xs p = True) (x: a) (member: x ∈ xs): p x = True :=
  List.allMem (y => p y = True) x xs (List.allToAll p xs all) member

theorem List.anyToAny ∀ (p: a → Bool) (xs: List a) (h: List.any xs p = True): List.Any (x => p x = True) xs :=
  match xs with
    | [x, ..xs] =>
      match c: p x with
        | True => Inl byComputing
        | False => Inr (List.anyToAny p xs h)

theorem List.anyOfAny ∀ (p: a → Bool) (xs: List a) (h1: List.Any (x => p x = True) xs): List.any xs p = True :=
  match xs, h1 with
    | [], h => h.impossible
    | [x, ..xs], Inl px => rewrite px
    | [x, ..xs], Inr h =>
      match c: p x with
        | True => byComputing
        | False => List.anyOfAny p xs h

theorem List.anyIff ∀ (xs: List a) (p: a → Bool): List.any xs p = True ↔ List.Any (x => p x = True) xs :=
  { forward = List.anyToAny p xs, backward = List.anyOfAny p xs }

--| Membership written with `any` and `==` is `x ∈ xs`. (`x ∈ xs` as a
--| `Bool` is `List.decMem`'s decision: its `sound` and
--| `complete` take it to the proposition and back.)
theorem List.anyEqIff ∀ [auto eq: DecEq a] (x: a) (xs: List a): List.any xs (== x) = True ↔ x ∈ xs := {
  forward = h => List.anyTrueElim xs (== x) (x ∈ xs) h (y m e => rewrite <- e.read then m),
  backward = m => List.anyOfMem xs (== x) x (DecEq.refl x) m
}

theorem List.allIffExample: List.All (x => Nat.leq 1 x = True) [1, 2, 3] :=
  (List.allIff [1, 2, 3] (x => Nat.leq 1 x)).forward byComputing

--| `any` is whether `find` finds something.
theorem List.anyFind ∀ (p: a → Bool) (xs: List a): List.any xs p = Option.isSome (List.find xs p) := match xs with
  | [] => byComputing
  | [x, ..xs] =>
    match c: p x with
      | True => byComputing
      | False => List.anyFind p xs
