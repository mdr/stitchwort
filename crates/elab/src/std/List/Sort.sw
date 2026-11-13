--| Sorting: merge sort (`List.sortWith`, `List.sortBy`, `List.sort`,
--| `List.sortOn`), `List.dedup`, `List.removeFirst` and the small `Nat` helpers
--| that go with them, with their unit tests and the congruence lemmas that
--| `decreasing` and `rewrite` look up by name. The other lemmas are in
--| List/SortLemmas.sw, so a program that only sorts checks none of them.
--
-- A library file is written like the prelude: names are as they are in the
-- namespaces they go in (`List.sort` is `Std.List.sort`), so one file can add
-- to several namespaces. It is checked when a program uses something in it.

--| The sum of the numbers from `x` up to, not including, `y`: `x + (x + 1) + ... + (y - 1)`.
def Nat.span (x: Nat) (y: Nat): Nat := List.sum (List.rangeFrom (y - x) x)

--| The sum of the numbers from `first` to `last`, both included, in one step
--| ([`Nat.sumBetweenCorrect`]). It is `first + (first + 1) + ... + last`, an
--| arithmetic series: the number of terms times their average. There are
--| `last + 1 - first` terms, which is 0 when first > last (as in
--| `List.range first (last + 1)`), so then the sum is 0.
def Nat.sumBetween (first: Nat) (last: Nat): Nat := (first + last) * (last + 1 - first) / 2

test "Nat.sumBetween" := Nat.sumBetween 3 7 == 25 ∧ Nat.sumBetween 5 5 == 5 ∧ Nat.sumBetween 1 100 == 5050
test "Nat.sumBetween, reversed bounds" := Nat.sumBetween 5 3 == 0 ∧ Nat.sumBetween 7 3 == 0 ∧ Nat.sumBetween 1 0 == 0

--| `x` when the condition holds, else 0: a term a sum may leave out.
def Nat.keepIf (x: Nat): (keep: Bool) → Nat
  | True => x
  | False => 0

--| The first number of the run `start .. start + count - 1` that passes `passes` (`start + count` if
--| none does): a least witness, found by computation. Nothing before it passes, and if some `k` of
--| the run passes, so does it, and it is at most `k`.
@[noReceiver]
@[tailrec]
def Nat.firstFrom (passes: Nat → Bool): (count: Nat) → (start: Nat) → Nat
  | Zero, start => start
  | Succ count, start => if passes start then start else Nat.firstFrom passes count (Succ start)

--| `True` for `Less` and `Equal`.
def Ordering.isLessEq: (ordering: Ordering) → Bool
  | Less => True
  | Equal => True
  | Greater => False

--| Merges two lists sorted by `le` ("may come before"), taking from the first
--| list on ties. The result is sorted ([`List.mergeSorted`]) and has the
--| elements of both ([`List.mergeCount`]).
@[noReceiver]
def List.merge (le: a → a → Bool): (xs: List a) → (ys: List a) → List a
  | [], ys => ys
  | [x, ..xs], [] => [x, ..xs]
  | [x, ..xs], [y, ..ys] =>
    if le x y then [x, ..List.merge le xs [y, ..ys]] else [y, ..List.merge le [x, ..xs] ys]

-- Bottom-up merge sort, structurally recursive throughout. The runs are kept
-- like the digits of a binary counter: slot `i` is empty or holds a sorted run
-- of 2^i elements, newest first. Adding an element carries: two runs of the
-- same size merge into the next slot. Each element takes part in about log n
-- merges, so sorting is O(n log n).

--| Adds a sorted run to the merge sort's slots, merging runs of the same size as a binary counter carries.
@[noReceiver]
def List.pushRun (le: a → a → Bool) (run: List a): (runs: List (Option (List a))) → List (Option (List a))
  | [] => [Some run]
  | [None, ..rest] => [Some run, ..rest]
  | [Some older, ..rest] => [None, ..List.pushRun le (List.merge le older run) rest]

--| The merge sort's slots after adding each element of the list as a run of one.
@[noReceiver]
@[tailrec]
def List.buildRuns (le: a → a → Bool) (runs: List (Option (List a))): (xs: List a) → List (Option (List a))
  | [] => runs
  | [x, ..xs] => List.buildRuns le (List.pushRun le [x] runs) xs

--| Merges the runs, older (earlier) ones on the left.
@[noReceiver]
@[tailrec]
def List.mergeRuns (le: a → a → Bool) (acc: List a): (runs: List (Option (List a))) → List a
  | [] => acc
  | [None, ..rest] => List.mergeRuns le acc rest
  | [Some older, ..rest] => List.mergeRuns le (List.merge le older acc) rest

--| Sorts by `le`, which says whether its first argument may come before its
--| second (`Nat.leq` for ascending numbers). Stable: equal elements keep their
--| order, in O(n log n). It is sorted, for a total `le` ([`List.sortWithSorted`]),
--| and a permutation of the list ([`List.sortWithPerm`]).
def List.sortWith (xs: List a) (le: a → a → Bool): List a := List.mergeRuns le [] (List.buildRuns le [] xs)

--| Sorts by a comparison, such as `Nat.compare` or `Text.compare`: stable, and
--| sorted ([`List.sortBySorted`]) and a permutation of the list ([`List.sortByPerm`]).
def List.sortBy (xs: List a) (cmp: a → a → Ordering): List a := List.sortWith xs (x y => Ordering.isLessEq (cmp x y))

--| Sorts into ascending order, by the type's `Ord`: numbers, texts, lists,
--| pairs, … Another order is passed by name, `List.sort [ord := …] xs`. Stable:
--| equal elements keep their order. The result is sorted ([`List.sortSorted`]),
--| a permutation ([`List.sortPerm`]), and as long ([`List.sortLength`]).
-- (docs/proposals/interfaces.md §7.4)
def List.sort [auto ord: Ord a] (xs: List a): List a := List.sortBy xs Ord.compare

--| `List.LeHead le bound xs`: `bound` may come before the first element of `xs`, if any.
@[noReceiver]
def List.LeHead (le: a → a → Bool) (bound: a): (xs: List a) → Prop
  | [] => Unit
  | [y, ..ys] => le bound y = True

--| Each element may come before the next. For a transitive `le`, such as
--| `Nat.leq`, that orders every pair.
@[noReceiver]
def List.Sorted (le: a → a → Bool): (xs: List a) → Prop
  | [] => Unit
  | [x, ..xs] => (List.LeHead le x xs) ∧ (List.Sorted le xs)

--| Whether `bound` may come before the first element of `xs`, if any:
--| `List.LeHead` as a `Bool` ([`List.isLeHeadIff`]).
@[noReceiver]
def List.isLeHead (le: a → a → Bool) (bound: a): (xs: List a) → Bool
  | [] => True
  | [y, ..ys] => le bound y

--| `List.isLeHead le bound xs` is `List.LeHead le bound xs` as a `Bool`.
@[reading]
theorem List.isLeHeadIff ∀ (le: a → a → Bool) (bound: a) (xs: List a): List.isLeHead le bound xs = True ↔ List.LeHead le bound xs :=
  match xs with
    | [] => { forward = h => Trivial, backward = h => rfl }
    | [y, ..ys] => { forward = h => h, backward = h => h }

--| Whether each element may come before the next: `List.Sorted` as a `Bool`
--| ([`List.isSortedByIff`]).
@[noReceiver]
def List.isSortedBy (le: a → a → Bool): (xs: List a) → Bool
  | [] => True
  | [x, ..xs] => List.isLeHead le x xs && List.isSortedBy le xs

--| `List.isSortedBy le xs` is `List.Sorted le xs` as a `Bool`.
@[reading]
theorem List.isSortedByIff ∀ (le: a → a → Bool) (xs: List a): List.isSortedBy le xs = True ↔ List.Sorted le xs :=
  match xs with
    | [] => { forward = h => Trivial, backward = h => rfl }
    | [x, ..rest] => {
      forward = h =>
        match h with
          | Both head more => Both ((List.isLeHeadIff le x rest).forward head) ((List.isSortedByIff le rest).forward more),
      backward = h =>
        match h with
          | Both head more => Both head ((List.isSortedByIff le rest).backward more)
    }

--| Decides `List.LeHead le bound xs` by `List.isLeHead`.
-- Its type spells out `List.LeHead`, as `List.decDistinct`'s does for `List.Distinct`.
instance List.decLeHead (le: a → a → Bool) (bound: a) (xs: List a): Decidable (List.LeHead le bound xs) :=
  { holds = List.isLeHead le bound xs, sound = (List.isLeHeadIff le bound xs).forward, complete = (List.isLeHeadIff le bound xs).backward }

--| Decides `List.Sorted le xs` by `List.isSortedBy`, so
--| `if List.Sorted Nat.leq xs` is a `Bool` where one is expected and
--| `check --counterexamples` can test lemmas that assume a list is sorted.
instance List.decSorted (le: a → a → Bool) (xs: List a): Decidable (List.Sorted le xs) :=
  { holds = List.isSortedBy le xs, sound = (List.isSortedByIff le xs).forward, complete = (List.isSortedByIff le xs).backward }

test "List.decSorted" := List.Sorted Nat.leq [1, 2, 2, 5] ∧ ¬(List.Sorted Nat.leq [1, 3, 2]) ∧ List.Sorted Nat.leq ([]: List Nat)

--| `rel` holds of each element and every later one.
@[noReceiver]
def List.Pairwise (rel: a → a → Prop): (xs: List a) → Prop
  | [] => Unit
  | [x, ..xs] => (List.All (y => rel x y) xs) ∧ (List.Pairwise rel xs)

test "List.sort by Ord.reverse" := List.sort [ord := Ord.reverse] [1, 3, 2, 3] == [3, 3, 2, 1]

--| The list without its first `x`, or the list itself if `x` isn't in it
--| (Haskell's `Data.List.delete`). With `x` in front it is a permutation of
--| the list ([`List.permRemoveFirst`]).
def List.removeFirst [auto eq: DecEq a]: (xs: List a) → (x: a) → List a
  | [], x => []
  | [y, ..ys], x => if y == x then ys else [y, ..ys.removeFirst x]

test "List.removeFirst" := [1, 2, 1].removeFirst 1 == [2, 1] ∧ [1, 2].removeFirst 3 == [1, 2] ∧ [3, 1, 2].removeFirst 2 == [3, 1]

--| `f` on every element of the merge sort's runs.
-- Sorting commutes with `map` when the comparison of the mapped elements is
-- that of the elements: sorting pairs by a key, then taking the keys, is
-- sorting the keys.
-- (SW-198, day 8)
-- Proved through each step of the merge sort.
@[noReceiver]
def List.mapRuns (f: a → b): (runs: List (Option (List a))) → List (Option (List b))
  | [] => []
  | [None, ..rest] => [None, ..List.mapRuns f rest]
  | [Some older, ..rest] => [Some (List.map older f), ..List.mapRuns f rest]

theorem List.mergeMap ∀ (f: a → b) (le: b → b → Bool) (le2: a → a → Bool) (h: ∀ (x y: a) => le2 x y = le (f x) (f y))
    (xs ys: List a): List.map (List.merge le2 xs ys) f = List.merge le (List.map xs f) (List.map ys f) :=
  match xs, ys with
    | [], ys => rfl
    | [x, ..xs], [] => rfl
    | [x, ..xs], [y, ..ys] =>
      rewrite h x y in
        List.mergeMapStep f (le (f x) (f y)) x y (List.merge le2 xs [y, ..ys]) (List.merge le2 [x, ..xs] ys)
          (List.merge le (List.map xs f) (List.map [y, ..ys] f)) (List.merge le (List.map [x, ..xs] f) (List.map ys f))
          (List.mergeMap f le le2 h xs [y, ..ys]) (List.mergeMap f le le2 h [x, ..xs] ys)

theorem List.mergeMapStep ∀ (f: a → b) (c: Bool) (x: a) (y: a) (l1: List a) (l2: List a) (r1: List b) (r2: List b)
    (e1: List.map l1 f = r1) (e2: List.map l2 f = r2):
    List.map (if c then [x, ..l1] else [y, ..l2]) f = (if c then [f x, ..r1] else [f y, ..r2]) := match c with
      | True => rewrite e1 in rfl
      | False => rewrite e2 in rfl

theorem List.pushRunMap ∀ (f: a → b) (le: b → b → Bool) (le2: a → a → Bool) (h: ∀ (x y: a) => le2 x y = le (f x) (f y))
    (run: List a) (c: List (Option (List a))): List.mapRuns f (List.pushRun le2 run c) = List.pushRun le (List.map run f) (List.mapRuns f c) :=
  match c with
    | [] => rfl
    | [None, ..rest] => rfl
    | [Some r, ..rest] => rewrite List.pushRunMap f le le2 h (List.merge le2 r run) rest, List.mergeMap f le le2 h r run

theorem List.buildRunsMap ∀ (f: a → b) (le: b → b → Bool) (le2: a → a → Bool) (h: ∀ (x y: a) => le2 x y = le (f x) (f y))
    (c: List (Option (List a))) (xs: List a): List.mapRuns f (List.buildRuns le2 c xs) = List.buildRuns le (List.mapRuns f c) (List.map xs f) :=
  match xs with
    | [] => rfl
    | [x, ..xs] => rewrite List.buildRunsMap f le le2 h (List.pushRun le2 [x] c) xs, List.pushRunMap f le le2 h [x] c

theorem List.mergeRunsMap ∀ (f: a → b) (le: b → b → Bool) (le2: a → a → Bool) (h: ∀ (x y: a) => le2 x y = le (f x) (f y))
    (acc: List a) (c: List (Option (List a))): List.map (List.mergeRuns le2 acc c) f = List.mergeRuns le (List.map acc f) (List.mapRuns f c) :=
  match c with
    | [] => rfl
    | [None, ..rest] => List.mergeRunsMap f le le2 h acc rest
    | [Some r, ..rest] => rewrite List.mergeRunsMap f le le2 h (List.merge le2 r acc) rest, List.mergeMap f le le2 h r acc

theorem List.sortWithMap ∀ (xs: List a) (f: a → b) (le: b → b → Bool) (le2: a → a → Bool) (h: ∀ (x y: a) => le2 x y = le (f x) (f y)):
    List.map (List.sortWith xs le2) f = List.sortWith (List.map xs f) le :=
  rewrite List.mergeRunsMap f le le2 h [] (List.buildRuns le2 [] xs), List.buildRunsMap f le le2 h [] xs in rfl

theorem List.sortByMap ∀ (xs: List a) (f: a → b) (cmp: b → b → Ordering) (cmp2: a → a → Ordering) (h: ∀ (x y: a) => cmp2 x y = cmp (f x) (f y)):
    List.map (List.sortBy xs cmp2) f = List.sortBy (List.map xs f) cmp :=
  List.sortWithMap xs f (x y => Ordering.isLessEq (cmp x y)) (x y => Ordering.isLessEq (cmp2 x y)) (x y => rewrite h x y in rfl)

theorem List.mapId ∀ (xs: List a): List.map xs (x => x) = xs := match xs with
  | [] => rfl
  | [x, ..xs] => rewrite List.mapId xs

--| Sorting by two comparisons that agree everywhere.
theorem List.sortByCong ∀ (xs: List a) (cmp1: a → a → Ordering) (cmp2: a → a → Ordering) (h: ∀ (x y: a) => cmp1 x y = cmp2 x y):
    List.sortBy xs cmp1 = List.sortBy xs cmp2 :=
  calc List.sortBy xs cmp1
    _ = List.map (List.sortBy xs cmp1) (x => x) := Eq.sym (List.mapId (List.sortBy xs cmp1))
    _ = List.sortBy (List.map xs (x => x)) cmp2 := List.sortByMap xs (x => x) cmp2 cmp1 h
    _ = List.sortBy xs cmp2 := rewrite List.mapId xs

test "List.sortByMap" := List.map (List.sortBy [MkPair 3 "c", MkPair 1 "a"] (p q => Nat.compare p.fst q.fst)) (p => p.fst) == List.sortBy [3, 1] Nat.compare

--| Sorts by a key, ascending by the key's `Ord`, stable: elements with equal
--| keys keep their order. `xs |> .sortOn key`. The key's instance is resolved
--| once, at the call, not on each comparison. A permutation of the list
--| ([`List.sortOnPerm`]).
def List.sortOn [auto ord: Ord k] (xs: List a) (key: a → k): List a := List.sortBy xs (x y => Ord.compare (key x) (key y))

test "List.sortOn" := List.sortOn [MkPair 3 "c", MkPair 1 "a", MkPair 3 "b", MkPair 2 "d"] (p => p.fst) == [MkPair 1 "a", MkPair 2 "d", MkPair 3 "c", MkPair 3 "b"]
test "List.sortOn by a tuple key" := List.sortOn [MkPair 2 1, MkPair 1 2, MkPair 1 1] (p => (p.snd, p.fst)) == [MkPair 1 1, MkPair 2 1, MkPair 1 2]
test "List.sortOn pipes" := ([3, 1, 2] |> .sortOn (n => 10 - n)) == [3, 2, 1]
test "List.sortOnMap" := List.map (List.sortOn [MkPair 3 "c", MkPair 1 "a"] (p => p.fst)) (p => p.fst) == List.sort [3, 1]

--| Drops each element equal to the one just before it (Rust's `Vec::dedup`),
--| so on a sorted list it drops every repeat: `[1, 1, 2, 3, 3].dedup` is
--| `[1, 2, 3]`. `List.sort` then `List.dedup` lists the different values in
--| order. It keeps the list's elements ([`List.memDedupIntro`],
--| [`List.memDedupElim`]) and keeps a sorted list sorted ([`List.sortedDedup`]).
def List.dedup [auto eq: DecEq a]: (xs: List a) → List a
  | [] => []
  | [x, ..xs] => [x, ..List.dedupAfter x xs]

--| `List.dedup` after `previous`: the elements not equal to the one before.
@[noReceiver]
def List.dedupAfter [auto eq: DecEq a] (previous: a): (xs: List a) → List a
  | [] => []
  | [x, ..xs] => if x == previous then List.dedupAfter previous xs else [x, ..List.dedupAfter x xs]

test "List.dedup" := [1, 1, 2, 3, 3, 3].dedup == [1, 2, 3] ∧ [2, 1, 2].dedup == [2, 1, 2] ∧ ([]: List Nat).dedup == []
test "List.dedup after sorting" := [3, 1, 3, 2, 1].sort.dedup == [1, 2, 3]
