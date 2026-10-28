-- Sorting: merge sort (`List.sortWith`, `List.sortBy`, `List.sort`,
-- `List.sortOn`), `List.dedup`, `List.removeFirst` and the small `Nat` helpers
-- that go with them, with their unit tests and the congruence lemmas that
-- `decreasing` and `rewrite` look up by name. The other lemmas are in
-- List/SortLemmas.sw, so a program that only sorts checks none of them.
--
-- A library file is written like the prelude: names are as they are in the
-- namespaces they go in (`List.sort` is `Std.List.sort`), so one file can add
-- to several namespaces. It is checked when a program uses something in it.

-- `x + (x + 1) + ... + (y - 1)`
def Nat.span (x: Nat) (y: Nat): Nat := List.sum (List.rangeFrom (y - x) x)

-- first + (first + 1) + ... + last: an arithmetic series, the number of
-- terms times their average. There are `last + 1 - first` terms, which is 0
-- when first > last (as in `List.between`), so then the sum is 0.
def Nat.sumBetween (first: Nat) (last: Nat): Nat := (first + last) * (last + 1 - first) / 2

test "Nat.sumBetween" := Nat.sumBetween 3 7 == 25 ∧ Nat.sumBetween 5 5 == 5 ∧ Nat.sumBetween 1 100 == 5050
test "Nat.sumBetween, reversed bounds" := Nat.sumBetween 5 3 == 0 ∧ Nat.sumBetween 7 3 == 0 ∧ Nat.sumBetween 1 0 == 0

-- `x` when the condition holds, else 0: a term a sum may leave out.
def Nat.keepIf (x: Nat): Bool → Nat
  | True => x
  | False => 0

theorem List.sumByCongRange [auto add: Add c] (f: Nat → c) (g: Nat → c): (c: Nat) → (s: Nat) → ((x: Nat) → s ≤ x → x < s + c → f x = g x) →
    List.sumBy (List.rangeFrom c s) f = List.sumBy (List.rangeFrom c s) g
  | Zero, s, h => rfl
  | Succ c, s, h =>
    Eq.trans (List.sumByCons (List.rangeFrom c (Succ s)) s f)
      (Eq.trans (Eq.cong (t => t + List.sumBy (List.rangeFrom c (Succ s)) f) (h s (Nat.leRefl s) (Nat.ltAddSuccSelf s c)))
        (Eq.trans (Eq.cong (t => g s + t) (List.sumByCongRange f g c (Succ s) (x hx1 hx2 => h x (Nat.leTrans s (Succ s) x (Nat.leSucc s) hx1) (Nat.ltAddSucc s c x hx2))))
          (Eq.sym (List.sumByCons (List.rangeFrom c (Succ s)) s g))))

-- The first number of the run `start .. start + count - 1` that passes `passes` (`start + count` if
-- none does): a least witness, found by computation. Nothing before it passes,
-- and if some `k` of the run passes, so does it, and it is at most `k`.
@[noReceiver]
def Nat.firstFrom (passes: Nat → Bool): Nat → Nat → Nat
  | Zero, start => start
  | Succ count, start => if passes start then start else Nat.firstFrom passes count (Succ start)

-- `True` for `Less` and `Equal`.
def Ordering.isLessEq: Ordering → Bool
  | Less => True
  | Equal => True
  | Greater => False

-- Merges two lists sorted by `le` ("may come before"), taking from the first
-- list on ties.
@[noReceiver]
def List.merge (le: a → a → Bool): List a → List a → List a
  | Nil, ys => ys
  | Cons x xs, Nil => Cons x xs
  | Cons x xs, Cons y ys =>
    if le x y then Cons x (List.merge le xs (Cons y ys)) else Cons y (List.merge le (Cons x xs) ys)

-- Bottom-up merge sort, structurally recursive throughout. The runs are kept
-- like the digits of a binary counter: slot `i` is empty or holds a sorted run
-- of 2^i elements, newest first. Adding an element carries: two runs of the
-- same size merge into the next slot. Each element takes part in about log n
-- merges, so sorting is O(n log n).
@[noReceiver]
def List.pushRun (le: a → a → Bool) (run: List a): List (Option (List a)) → List (Option (List a))
  | Nil => Cons (Some run) Nil
  | Cons None rest => Cons (Some run) rest
  | Cons (Some older) rest => Cons None (List.pushRun le (List.merge le older run) rest)

@[noReceiver]
def List.buildRuns (le: a → a → Bool) (runs: List (Option (List a))): List a → List (Option (List a))
  | Nil => runs
  | Cons x xs => List.buildRuns le (List.pushRun le (Cons x Nil) runs) xs

-- Merges the runs, older (earlier) ones on the left.
@[noReceiver]
def List.mergeRuns (le: a → a → Bool) (acc: List a): List (Option (List a)) → List a
  | Nil => acc
  | Cons None rest => List.mergeRuns le acc rest
  | Cons (Some older) rest => List.mergeRuns le (List.merge le older acc) rest

-- Sorts by `le`, which says whether its first argument may come before its
-- second (`Nat.leq` for ascending numbers). Stable: equal elements keep their
-- order. `List.sortWithSorted` and `List.sortWithPerm` say it's correct.
def List.sortWith (xs: List a) (le: a → a → Bool): List a := List.mergeRuns le Nil (List.buildRuns le Nil xs)

-- Sorts by a comparison, such as `Nat.compare` or `Text.compare`.
def List.sortBy (xs: List a) (cmp: a → a → Ordering): List a := List.sortWith xs (x y => Ordering.isLessEq (cmp x y))

-- Sorts into ascending order, by the type's `Ord` (docs/proposals/interfaces.md
-- §7.4): numbers, texts, lists, pairs, … Another order is passed by name,
-- `List.sort [ord := …] xs`.
def List.sort [auto ord: Ord a] (xs: List a): List a := List.sortBy xs Ord.compare

-- `List.LeHead le bound xs`: `bound` may come before the first element of `xs`, if any.
@[noReceiver]
def List.LeHead (le: a → a → Bool) (bound: a): List a → Prop
  | Nil => Unit
  | Cons y ys => le bound y = True

-- Each element may come before the next. For a transitive `le`, such as
-- `Nat.leq`, that orders every pair.
@[noReceiver]
def List.Sorted (le: a → a → Bool): List a → Prop
  | Nil => Unit
  | Cons x xs => And (List.LeHead le x xs) (List.Sorted le xs)

-- `rel` holds of each element and every later one.
@[noReceiver]
def List.Pairwise (rel: a → a → Prop): List a → Prop
  | Nil => Unit
  | Cons x xs => And (List.All (y => rel x y) xs) (List.Pairwise rel xs)

test "List.sort by Ord.reverse" := List.sort [ord := Ord.reverse] [1, 3, 2, 3] == [3, 3, 2, 1]

-- The list without its first `x`, or the list itself if `x` isn't in it
-- (Haskell's `Data.List.delete`).
def List.removeFirst [auto eq: DecEq a]: List a → a → List a
  | Nil, x => Nil
  | Cons y ys, x => if y == x then ys else Cons y (ys.removeFirst x)

test "List.removeFirst" := [1, 2, 1].removeFirst 1 == [2, 1] ∧ [1, 2].removeFirst 3 == [1, 2] ∧ [3, 1, 2].removeFirst 2 == [3, 1]

-- Counting with tests that agree on the list's elements (SW-198, day 8).
theorem List.countCongMem (xs: List a) (p1: a → Bool) (p2: a → Bool) (ep: (x: a) → (m: List.Mem x xs) → p1 x = p2 x): List.count xs p1 = List.count xs p2 :=
  rewrite List.countOccurrences xs p1, List.countOccurrences xs p2 in List.occurrencesCongMem xs p1 p2 ep

-- Sorting commutes with `map` when the comparison of the mapped elements is
-- that of the elements (SW-198, day 8): sorting pairs by a key, then taking
-- the keys, is sorting the keys. Proved through each step of the merge sort.
@[noReceiver]
def List.mapRuns (f: a → b): List (Option (List a)) → List (Option (List b))
  | Nil => Nil
  | Cons None rest => Cons None (List.mapRuns f rest)
  | Cons (Some older) rest => Cons (Some (List.map older f)) (List.mapRuns f rest)

theorem List.mergeMap (f: a → b) (le: b → b → Bool) (le2: a → a → Bool) (h: (x: a) → (y: a) → le2 x y = le (f x) (f y)):
    (xs: List a) → (ys: List a) → List.map (List.merge le2 xs ys) f = List.merge le (List.map xs f) (List.map ys f)
  | Nil, ys => rfl
  | Cons x xs, Nil => rfl
  | Cons x xs, Cons y ys =>
    rewrite h x y in
      List.mergeMapStep f (le (f x) (f y)) x y (List.merge le2 xs (Cons y ys)) (List.merge le2 (Cons x xs) ys)
        (List.merge le (List.map xs f) (List.map (Cons y ys) f)) (List.merge le (List.map (Cons x xs) f) (List.map ys f))
        (List.mergeMap f le le2 h xs (Cons y ys)) (List.mergeMap f le le2 h (Cons x xs) ys)

theorem List.mergeMapStep (f: a → b) (c: Bool) (x: a) (y: a) (l1: List a) (l2: List a) (r1: List b) (r2: List b)
    (e1: List.map l1 f = r1) (e2: List.map l2 f = r2):
    List.map (if c then Cons x l1 else Cons y l2) f = (if c then Cons (f x) r1 else Cons (f y) r2) :=
  match c with
    | True => rewrite e1 in rfl
    | False => rewrite e2 in rfl

theorem List.pushRunMap (f: a → b) (le: b → b → Bool) (le2: a → a → Bool) (h: (x: a) → (y: a) → le2 x y = le (f x) (f y)):
    (run: List a) → (c: List (Option (List a))) → List.mapRuns f (List.pushRun le2 run c) = List.pushRun le (List.map run f) (List.mapRuns f c)
  | run, Nil => rfl
  | run, Cons None rest => rfl
  | run, Cons (Some r) rest => rewrite List.pushRunMap f le le2 h (List.merge le2 r run) rest, List.mergeMap f le le2 h r run

theorem List.buildRunsMap (f: a → b) (le: b → b → Bool) (le2: a → a → Bool) (h: (x: a) → (y: a) → le2 x y = le (f x) (f y)):
    (c: List (Option (List a))) → (xs: List a) → List.mapRuns f (List.buildRuns le2 c xs) = List.buildRuns le (List.mapRuns f c) (List.map xs f)
  | c, Nil => rfl
  | c, Cons x xs => rewrite List.buildRunsMap f le le2 h (List.pushRun le2 (Cons x Nil) c) xs, List.pushRunMap f le le2 h (Cons x Nil) c

theorem List.mergeRunsMap (f: a → b) (le: b → b → Bool) (le2: a → a → Bool) (h: (x: a) → (y: a) → le2 x y = le (f x) (f y)):
    (acc: List a) → (c: List (Option (List a))) → List.map (List.mergeRuns le2 acc c) f = List.mergeRuns le (List.map acc f) (List.mapRuns f c)
  | acc, Nil => rfl
  | acc, Cons None rest => List.mergeRunsMap f le le2 h acc rest
  | acc, Cons (Some r) rest => rewrite List.mergeRunsMap f le le2 h (List.merge le2 r acc) rest, List.mergeMap f le le2 h r acc

theorem List.sortWithMap (xs: List a) (f: a → b) (le: b → b → Bool) (le2: a → a → Bool) (h: (x: a) → (y: a) → le2 x y = le (f x) (f y)):
    List.map (List.sortWith xs le2) f = List.sortWith (List.map xs f) le :=
  rewrite List.mergeRunsMap f le le2 h Nil (List.buildRuns le2 Nil xs), List.buildRunsMap f le le2 h Nil xs in rfl

theorem List.sortByMap (xs: List a) (f: a → b) (cmp: b → b → Ordering) (cmp2: a → a → Ordering) (h: (x: a) → (y: a) → cmp2 x y = cmp (f x) (f y)):
    List.map (List.sortBy xs cmp2) f = List.sortBy (List.map xs f) cmp :=
  List.sortWithMap xs f (x y => Ordering.isLessEq (cmp x y)) (x y => Ordering.isLessEq (cmp2 x y)) (x y => rewrite h x y in rfl)

theorem List.mapId: (xs: List a) → List.map xs (x => x) = xs
  | Nil => rfl
  | Cons x xs => rewrite List.mapId xs

-- Sorting by two comparisons that agree everywhere.
theorem List.sortByCong (xs: List a) (cmp1: a → a → Ordering) (cmp2: a → a → Ordering) (h: (x: a) → (y: a) → cmp1 x y = cmp2 x y):
    List.sortBy xs cmp1 = List.sortBy xs cmp2 :=
  calc List.sortBy xs cmp1
    _ = List.map (List.sortBy xs cmp1) (x => x) := Eq.sym (List.mapId (List.sortBy xs cmp1))
    _ = List.sortBy (List.map xs (x => x)) cmp2 := List.sortByMap xs (x => x) cmp2 cmp1 h
    _ = List.sortBy xs cmp2 := rewrite List.mapId xs

test "List.sortByMap" := List.map (List.sortBy [MkPair 3 "c", MkPair 1 "a"] (p q => Nat.compare p.fst q.fst)) (p => p.fst) == List.sortBy [3, 1] Nat.compare

-- Sorts by a key, ascending by the key's `Ord`, stable: elements with equal
-- keys keep their order. `xs |> .sortOn key`. The key's instance is resolved
-- once, at the call, not on each comparison.
def List.sortOn [auto ord: Ord k] (xs: List a) (key: a → k): List a := List.sortBy xs (x y => Ord.compare (key x) (key y))

test "List.sortOn" := List.sortOn [MkPair 3 "c", MkPair 1 "a", MkPair 3 "b", MkPair 2 "d"] (p => p.fst) == [MkPair 1 "a", MkPair 2 "d", MkPair 3 "c", MkPair 3 "b"]
test "List.sortOn by a tuple key" := List.sortOn [MkPair 2 1, MkPair 1 2, MkPair 1 1] (p => (p.snd, p.fst)) == [MkPair 1 1, MkPair 2 1, MkPair 1 2]
test "List.sortOn pipes" := ([3, 1, 2] |> .sortOn (n => 10 - n)) == [3, 2, 1]
test "List.sortOnMap" := List.map (List.sortOn [MkPair 3 "c", MkPair 1 "a"] (p => p.fst)) (p => p.fst) == List.sort [3, 1]

-- Drops each element equal to the one just before it (Rust's `Vec::dedup`),
-- so on a sorted list it drops every repeat: `[1, 1, 2, 3, 3].dedup` is
-- `[1, 2, 3]`. `List.sort` then `List.dedup` lists the different values in
-- order.
def List.dedup [auto eq: DecEq a]: List a → List a
  | Nil => Nil
  | Cons x xs => Cons x (List.dedupAfter x xs)

-- `List.dedup` after `previous`: the elements not equal to the one before.
@[noReceiver]
def List.dedupAfter [auto eq: DecEq a] (previous: a): List a → List a
  | Nil => Nil
  | Cons x xs => if x == previous then List.dedupAfter previous xs else Cons x (List.dedupAfter x xs)

test "List.dedup" := [1, 1, 2, 3, 3, 3].dedup == [1, 2, 3] ∧ [2, 1, 2].dedup == [2, 1, 2] ∧ (Nil: List Nat).dedup == Nil
test "List.dedup after sorting" := [3, 1, 3, 2, 1].sort.dedup == [1, 2, 3]
