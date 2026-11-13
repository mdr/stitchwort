--| `List.unique`: the elements without repeats, for a type with an
--| ordering, in O(n log n). A `Set` holds what has been seen, so each element
--| costs a lookup, not a scan of the elements kept before it as
--| `List.uniqueDecEq` (the `DecEq`-only version, std/List/Toolkit.sw) does.
--| The result is the same ([`List.uniqueUniqueDecEq`]), so what is proved
--| here for `uniqueDecEq` holds for `unique` too.
-- (SW-454, D1191)
-- The theorems are here, not beside `uniqueDecEq`, so that programs using the
-- list toolkit don't load the files they need.

--| One step of `List.unique`: `seen` is the set of elements kept so far, and
--| `acc` those elements, last first. A loop, so it is stack-safe on long lists.
@[noReceiver]
@[tailrec]
def List.uniqueLoop [auto ord: Ord a] (seen: Set a) (acc: List a): (xs: List a) → List a
  | [] => List.reverseOnto acc []
  | [x, ..xs] => if Set.contains seen x then List.uniqueLoop seen acc xs else List.uniqueLoop (Set.insert seen x) [x, ..acc] xs

--| The elements without repeats, keeping the first occurrence of each, in the
--| original order: `[3, 1, 3, 2, 1].unique` is `[3, 1, 2]`. It has exactly
--| the list's elements ([`List.memUnique`]). O(n log n); for a type with `==`
--| but no ordering, `List.uniqueDecEq`.
def List.unique [auto ord: Ord a] (xs: List a): List a := List.uniqueLoop Set.empty [] xs

-- What `uniqueFrom` (so `uniqueDecEq`) keeps: elements of the list, none of
-- them in `seen`, none twice, and every element of the list not in `seen`.

theorem List.anyConsSelf ∀ [auto eq: DecEq a] (y: a) (s: List a): List.any [y, ..s] (== y) = True :=
  match e: y == y with
    | True => rfl
    | False => Void.exfalso (e.read rfl)

theorem List.anyTailFalse ∀ (p: a → Bool) (y: a) (s: List a) (h: List.any [y, ..s] p = False): List.any s p = False :=
  match e: p y with
    | False => h

theorem List.memUniqueFromElim ∀ [auto eq: DecEq a] (x: a) (seen xs: List a) (m: x ∈ List.uniqueFrom seen xs): x ∈ xs :=
  match xs with
    | [y, ..ys] =>
      match c: List.any seen (== y) with
        | True => Inr (List.memUniqueFromElim x seen ys m)
        | False =>
          match m with
            | Inl q => Inl q
            | Inr later => Inr (List.memUniqueFromElim x [y, ..seen] ys later)

theorem List.memUniqueFromIntro ∀ [auto eq: DecEq a] (x: a) (seen xs: List a) (m: x ∈ xs):
    List.any seen (== x) = True ∨ x ∈ List.uniqueFrom seen xs := match xs with
      | [y, ..ys] =>
        match c: List.any seen (== y) with
          | True =>
            match m with
              | Inl q => Inl (rewrite <- q in c)
              | Inr later => List.memUniqueFromIntro x seen ys later
          | False =>
            match m with
              | Inl q => Inr (Inl q)
              | Inr later =>
                match List.memUniqueFromIntro x [y, ..seen] ys later with
                  | Inr inRest => Inr (Inr inRest)
                  | Inl hit =>
                    match d: y == x with
                      | True => Inr (Inl d.read)
                      | False => Inl hit

theorem List.uniqueFromFresh ∀ [auto eq: DecEq a] (z: a) (seen xs: List a) (m: z ∈ List.uniqueFrom seen xs): List.any seen (== z) = False :=
  match xs with
    | [y, ..ys] =>
      match c: List.any seen (== y) with
        | True => List.uniqueFromFresh z seen ys m
        | False =>
          match m with
            | Inl q => rewrite <- q in c
            | Inr later => List.anyTailFalse (== z) y seen (List.uniqueFromFresh z [y, ..seen] ys later)

theorem List.uniqueFromNoRepeats ∀ [auto eq: DecEq a] (seen xs: List a): List.Distinct (List.uniqueFrom seen xs) :=
  match xs with
    | [] => Trivial
    | [y, ..ys] =>
      match c: List.any seen (== y) with
        | True => List.uniqueFromNoRepeats seen ys
        | False =>
          Both (m => Bool.trueNotFalse (Eq.trans (Eq.sym (List.anyConsSelf y seen)) (List.uniqueFromFresh y [y, ..seen] ys m)))
            (List.uniqueFromNoRepeats [y, ..seen] ys)

--| `uniqueDecEq` keeps exactly the list's elements.
theorem List.memUniqueDecEq ∀ [auto eq: DecEq a] (x: a) (xs: List a): x ∈ List.uniqueDecEq xs ↔ x ∈ xs := {
  forward = m => List.memUniqueFromElim x [] xs m,
  backward = m =>
    match List.memUniqueFromIntro x [] xs m with
      | Inl none => cases
      | Inr found => found
}

--| `uniqueDecEq` keeps each element once.
theorem List.uniqueDecEqNoRepeats ∀ [auto eq: DecEq a] (xs: List a): List.Distinct (List.uniqueDecEq xs) := List.uniqueFromNoRepeats [] xs

-- The loop is `uniqueFrom` when the set has the same elements as the list
-- `uniqueFrom` keeps.

theorem List.uniqueSeenInsert ∀ [auto ord: Ord a] (seen: Set a) (seenList: List a) (same: ∀ (z: a) => Set.contains seen z = List.any seenList (== z))
    (x: a) (z: a): Set.contains (Set.insert seen x) z = List.any [x, ..seenList] (== z) := match e: x == z with
      | True => rewrite e.read in Set.containsInsert z seen
      | False => rewrite Set.containsInsertOther seen x z (eq => e.read (Eq.sym eq)) in same z

theorem List.uniqueLoopFrom [auto ord: Ord a]: ∀ (seen: Set a) (seenList: List a) => (∀ (z: a) => Set.contains seen z = List.any seenList (== z)) →
    ∀ (acc xs: List a) => List.uniqueLoop seen acc xs = List.reverseOnto acc (List.uniqueFrom seenList xs)
  | seen, seenList, same, acc, [] => rfl
  | seen, seenList, same, acc, [x, ..xs] =>
    match c: Set.contains seen x with
      | True =>
        match d: List.any seenList (== x) with
          | True => List.uniqueLoopFrom seen seenList same acc xs
          | False => Void.exfalso (Bool.trueNotFalse (Eq.trans (Eq.sym c) (Eq.trans (same x) d)))
      | False =>
        match d: List.any seenList (== x) with
          | True => Void.exfalso (Bool.falseNotTrue (Eq.trans (Eq.sym c) (Eq.trans (same x) d)))
          | False =>
            List.uniqueLoopFrom (Set.insert seen x) [x, ..seenList] (z => List.uniqueSeenInsert seen seenList same x z) [x, ..acc] xs

--| `unique` is `uniqueDecEq`, deciding `==` by the ordering's equality.
theorem List.uniqueUniqueDecEq ∀ [auto ord: Ord a] (xs: List a): List.unique xs = List.uniqueDecEq [eq := ord.eq] xs :=
  List.uniqueLoopFrom Set.empty [] (z => rfl) [] xs

--| `unique` keeps exactly the list's elements.
theorem List.memUnique ∀ [auto ord: Ord a] (x: a) (xs: List a): x ∈ List.unique xs ↔ x ∈ xs :=
  rewrite List.uniqueUniqueDecEq xs in List.memUniqueDecEq [eq := ord.eq] x xs

--| `unique` keeps each element once.
theorem List.distinctUnique ∀ [auto ord: Ord a] (xs: List a): List.Distinct (List.unique xs) :=
  rewrite List.uniqueUniqueDecEq xs in List.uniqueDecEqNoRepeats [eq := ord.eq] xs

-- What `uniqueFrom` keeps of lists built up: a list with no repeats and
-- nothing seen is kept whole; elements all seen are all dropped; elements
-- appended that are seen or earlier are dropped; a new element appended is
-- kept.

--| An element seen before is still seen after another is added in front.
theorem List.anyConsEqTrue ∀ [auto eq: DecEq a] (x: a) (y: a) (seen: List a) (h: List.any seen (== y) = True): List.any [x, ..seen] (== y) = True :=
  match d: x == y with
    | True => rfl
    | False => h

theorem List.anyConsEqFalse ∀ [auto eq: DecEq a] (x: a) (y: a) (seen: List a) (ne: x ≠ y) (h: List.any seen (== y) = False):
    List.any [x, ..seen] (== y) = False := match d: x == y with
      | True => Void.exfalso (ne d.read)
      | False => h

theorem List.uniqueFromKeep ∀ [auto eq: DecEq a] (seen xs: List a) (h: List.Distinct xs)
    (fresh: ∀ (z: a) => List.Mem z xs → List.any seen (== z) = False): List.uniqueFrom seen xs = xs :=
  match xs, h with
    | [], d => rfl
    | [y, ..ys], Both notMem d =>
      rewrite fresh y (Inl rfl) in
      Eq.cong (Cons y)
        (List.uniqueFromKeep [y, ..seen] ys d (z m =>
          List.anyConsEqFalse y z seen (e => notMem (rewrite e in m)) (fresh z (Inr m))))

theorem List.uniqueFromSeen ∀ [auto eq: DecEq a] (seen ys: List a)
    (h: ∀ (y: a) => List.Mem y ys → List.any seen (== y) = True): List.uniqueFrom seen ys = [] := match ys with
      | [] => rfl
      | [y, ..ys] => rewrite h y (Inl rfl) in List.uniqueFromSeen seen ys (z m => h z (Inr m))

theorem List.uniqueFromAppendSeen ∀ [auto eq: DecEq a] (seen xs ys: List a)
    (cov: ∀ (y: a) => List.Mem y ys → (List.any seen (== y) = True) ∨ (List.Mem y xs)):
    List.uniqueFrom seen (List.append xs ys) = List.uniqueFrom seen xs := match xs with
      | [] =>
        List.uniqueFromSeen seen ys (y m =>
          match cov y m with
            | Inl s => s
            | Inr none => Void.exfalso none)
      | [x, ..xs] =>
        match c: List.any seen (== x) with
          | True =>
            List.uniqueFromAppendSeen seen xs ys (y m =>
              match cov y m with
                | Inl s => Inl s
                | Inr (Inl q) => Inl (rewrite <- q in c)
                | Inr (Inr later) => Inr later)
          | False =>
            Eq.cong (Cons x)
              (List.uniqueFromAppendSeen [x, ..seen] xs ys (y m =>
                match cov y m with
                  | Inl s =>
                    Inl (List.anyConsEqTrue x y seen s)
                  | Inr (Inl q) => Inl (rewrite <- q in List.anyConsSelf x seen)
                  | Inr (Inr later) => Inr later))

theorem List.uniqueFromSnoc ∀ [auto eq: DecEq a] (y: a) (seen xs: List a) (out: ¬(List.Mem y xs))
    (fresh: List.any seen (== y) = False): List.uniqueFrom seen (List.append xs [y]) = List.append (List.uniqueFrom seen xs) [y] :=
  match xs with
    | [] => rewrite fresh in rfl
    | [x, ..xs] =>
      match c: List.any seen (== x) with
        | True => List.uniqueFromSnoc y seen xs (m => out (Inr m)) fresh
        | False =>
          Eq.cong (Cons x)
            (List.uniqueFromSnoc y [x, ..seen] xs (m => out (Inr m))
              (List.anyConsEqFalse x y seen (e => out (Inl e)) fresh))

--| A list with no repeats is its own `unique`.
theorem List.uniqueOfDistinct ∀ [auto ord: Ord a] (xs: List a) (d: List.Distinct xs): List.unique xs = xs :=
  rewrite List.uniqueUniqueDecEq xs in List.uniqueFromKeep [eq := ord.eq] [] xs d (z m => rfl)

--| `unique` twice is `unique` once.
theorem List.uniqueUnique ∀ [auto ord: Ord a] (xs: List a): List.unique (List.unique xs) = List.unique xs :=
  List.uniqueOfDistinct (List.unique xs) (List.distinctUnique xs)

--| Appending elements the list has already doesn't change its `unique`.
theorem List.uniqueAppendSeen ∀ [auto ord: Ord a] (xs: List a) (ys: List a) (sub: ∀ (y: a) => List.Mem y ys → List.Mem y xs):
    List.unique (List.append xs ys) = List.unique xs :=
  rewrite List.uniqueUniqueDecEq (List.append xs ys), List.uniqueUniqueDecEq xs in
  List.uniqueFromAppendSeen [eq := ord.eq] [] xs ys (y m => Inr (sub y m))

--| Appending a new element appends it to the list's `unique`.
theorem List.uniqueSnoc ∀ [auto ord: Ord a] (xs: List a) (y: a) (out: ¬(List.Mem y xs)):
    List.unique (List.append xs [y]) = List.append (List.unique xs) [y] :=
  rewrite List.uniqueUniqueDecEq (List.append xs [y]), List.uniqueUniqueDecEq xs in
  List.uniqueFromSnoc [eq := ord.eq] y [] xs out rfl

theorem List.uniqueAppendSeenExample ∀ (xs: List Nat): List.unique (List.append xs xs) = List.unique xs :=
  List.uniqueAppendSeen xs xs (y m => m)

--| Whether no element appears twice: `List.Distinct` as a `Bool`
--| ([`List.isDistinctIff`]). A `Set` holds what has been seen, so it is
--| O(n log n) and stops at the first repeat.
@[noReceiver]
@[tailrec]
def List.isDistinctFrom [auto ord: Ord a] (seen: Set a): (xs: List a) → Bool
  | [] => True
  | [x, ..rest] => if Set.contains seen x then False else List.isDistinctFrom (Set.insert seen x) rest

--| Whether no element appears twice, in O(n log n): `List.Distinct` as a `Bool` ([`List.isDistinctIff`]).
def List.isDistinct [auto ord: Ord a] (xs: List a): Bool := List.isDistinctFrom Set.empty xs

--| What has been seen is not ahead in a list that passes.
theorem List.isDistinctSeenNotAhead ∀ [auto ord: Ord a] (seen: Set a) (x: a) (isSeen: Set.contains seen x = True)
    (xs: List a) (ok: List.isDistinctFrom seen xs = True): ¬(List.Mem x xs) := match xs with
      | [] => member => member
      | [next, ..rest] => member =>
        match c: Set.contains seen next with
          | False =>
            match member with
              | Inl same => Bool.falseNotTrue (Eq.trans (Eq.sym c) (rewrite same in isSeen))
              | Inr later => List.isDistinctSeenNotAhead (Set.insert seen next) x (Set.containsInsertMono seen next x isSeen) rest ok later

--| Passing means no repeats.
theorem List.isDistinctFromSound ∀ [auto ord: Ord a] (seen: Set a) (xs: List a) (ok: List.isDistinctFrom seen xs = True): List.Distinct xs :=
  match xs with
    | [] => Trivial
    | [next, ..rest] =>
      match c: Set.contains seen next with
        | False =>
          Both (List.isDistinctSeenNotAhead (Set.insert seen next) next (Set.containsInsert next seen) rest ok)
            (List.isDistinctFromSound (Set.insert seen next) rest ok)

--| No repeats, and nothing seen already, passes.
theorem List.isDistinctFromComplete ∀ [auto ord: Ord a] (seen: Set a) (xs: List a) (distinct: List.Distinct xs)
    (unseen: ∀ (x: a) => List.Mem x xs → Set.contains seen x = False): List.isDistinctFrom seen xs = True :=
  match xs with
    | [] => rfl
    | [next, ..rest] =>
      rewrite unseen next (Inl rfl)
      in List.isDistinctFromComplete (Set.insert seen next) rest (And.right distinct) (x member =>
        rewrite Set.containsInsertOther seen next x (same => And.left distinct (rewrite <- same in member))
        in unseen x (Inr member))

@[reading]
theorem List.isDistinctIff ∀ [auto ord: Ord a] (xs: List a): List.isDistinct xs = True ↔ List.Distinct xs := {
  forward = ok => List.isDistinctFromSound Set.empty xs ok,
  backward = distinct => List.isDistinctFromComplete Set.empty xs distinct (x member => rfl)
}

--| `List.isDistinct xs` is `False` exactly when some element repeats.
@[reading]
theorem List.isDistinctReadsFalse ∀ [auto ord: Ord a] (xs: List a): List.isDistinct xs = False ↔ ¬(List.Distinct xs) :=
  match c: List.isDistinct xs with
    | True => { forward = h => Void.exfalso (Bool.trueNotFalse h), backward = no => Void.exfalso (no (Iff.forward (List.isDistinctIff xs) c)) }
    | False => { forward = h distinct => Bool.falseNotTrue (Eq.trans (Eq.sym c) (Iff.backward (List.isDistinctIff xs) distinct)), backward = no => rfl }

test "List.unique" := [3, 1, 3, 2, 1].unique == [3, 1, 2]
test "List.unique empty" := ([]: List Nat).unique == []
test "List.unique all repeats" := [4, 4, 4].unique == [4]
test "List.unique already distinct keeps the order" := [2, 5, 1].unique == [2, 5, 1]
test "List.unique keeps first occurrences in order" := ["b", "a", "b", "c", "a"].unique == ["b", "a", "c"]
-- (Here rather than in std/Text/Text.sw: this file needs that one, through `Set`.)
test "List.unique texts" := ["a", "b", "a"].unique == ["a", "b"]
test "List.isDistinct" := [3, 1, 2].isDistinct && ![3, 1, 3].isDistinct && ([]: List Nat).isDistinct
test "List.unique agrees with uniqueDecEq" := [5, 2, 5, 9, 2, 0].unique == [5, 2, 5, 9, 2, 0].uniqueDecEq
