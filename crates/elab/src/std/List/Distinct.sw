-- `List.distinct`: the elements without repeats, for a type with an
-- ordering, in O(n log n) (SW-454, D1191). A `Set` holds what has been seen,
-- so each element costs a lookup, not a scan of the elements kept before it
-- as `List.distinctEq` (the `DecEq`-only version, std/List/Toolkit.sw) does.
-- The result is the same (`List.distinctIsDistinctEq`), so what is proved
-- here for `distinctEq` holds for `distinct` too. The theorems are here, not
-- beside `distinctEq`, so that programs using the list toolkit don't load
-- the files they need.

-- One step of `List.distinct`: `seen` is the set of elements kept so far, and
-- `acc` those elements, last first. A loop, so it is stack-safe on long lists.
@[noReceiver]
def List.distinctLoop [auto ord: Ord a] (seen: Set a) (acc: List a): List a → List a
  | Nil => List.reverseOnto acc Nil
  | Cons x xs => if Set.contains seen x then List.distinctLoop seen acc xs else List.distinctLoop (Set.insert seen x) (Cons x acc) xs

-- The elements without repeats, keeping the first occurrence of each, in the
-- original order. `xs` is the main value: `xs.distinct`. `[3, 1, 3, 2,
-- 1].distinct` is `[3, 1, 2]`. O(n log n); for a type with `==` but no
-- ordering, `List.distinctEq`.
def List.distinct [auto ord: Ord a] (xs: List a): List a := List.distinctLoop Set.empty Nil xs

-- What `distinctFrom` (so `distinctEq`) keeps: elements of the list, none of
-- them in `seen`, none twice, and every element of the list not in `seen`.

theorem List.anyConsSelf [auto eq: DecEq a] (y: a) (s: List a): List.any (Cons y s) (== y) = True :=
  match e: y == y with
    | True => rfl
    | False => Void.exfalso (DecEq.soundFalse y y e rfl)

theorem List.anyTailFalse (p: a → Bool) (y: a) (s: List a) (h: List.any (Cons y s) p = False): List.any s p = False :=
  match e: p y with
    | True => Void.exfalso (Bool.trueNotFalse h)
    | False => h

theorem List.memDistinctFromElim [auto eq: DecEq a] (x: a): (seen: List a) → (xs: List a) → x ∈ List.distinctFrom seen xs → x ∈ xs
  | seen, Nil, m => m
  | seen, Cons y ys, m =>
    match c: List.any seen (== y) with
      | True => Inr (List.memDistinctFromElim x seen ys m)
      | False =>
        match m with
          | Inl q => Inl q
          | Inr later => Inr (List.memDistinctFromElim x (Cons y seen) ys later)

theorem List.memDistinctFromIntro [auto eq: DecEq a] (x: a): (seen: List a) → (xs: List a) → x ∈ xs →
    List.any seen (== x) = True ∨ x ∈ List.distinctFrom seen xs
  | seen, Nil, m => Void.exfalso m
  | seen, Cons y ys, m =>
    match c: List.any seen (== y) with
      | True =>
        match m with
          | Inl q => Inl (rewrite <- q in c)
          | Inr later => List.memDistinctFromIntro x seen ys later
      | False =>
        match m with
          | Inl q => Inr (Inl q)
          | Inr later =>
            match List.memDistinctFromIntro x (Cons y seen) ys later with
              | Inr inRest => Inr (Inr inRest)
              | Inl hit =>
                match d: y == x with
                  | True => Inr (Inl (DecEq.sound y x d))
                  | False => Inl hit

theorem List.distinctFromFresh [auto eq: DecEq a] (z: a): (seen: List a) → (xs: List a) → z ∈ List.distinctFrom seen xs → List.any seen (== z) = False
  | seen, Nil, m => Void.exfalso m
  | seen, Cons y ys, m =>
    match c: List.any seen (== y) with
      | True => List.distinctFromFresh z seen ys m
      | False =>
        match m with
          | Inl q => rewrite <- q in c
          | Inr later => List.anyTailFalse (== z) y seen (List.distinctFromFresh z (Cons y seen) ys later)

theorem List.distinctFromNoRepeats [auto eq: DecEq a]: (seen: List a) → (xs: List a) → List.Distinct (List.distinctFrom seen xs)
  | seen, Nil => Trivial
  | seen, Cons y ys =>
    match c: List.any seen (== y) with
      | True => List.distinctFromNoRepeats seen ys
      | False =>
        Both (m => Bool.trueNotFalse (Eq.trans (Eq.sym (List.anyConsSelf y seen)) (List.distinctFromFresh y (Cons y seen) ys m)))
          (List.distinctFromNoRepeats (Cons y seen) ys)

-- `distinctEq` keeps exactly the list's elements ...
theorem List.memDistinctEq [auto eq: DecEq a] (x: a) (xs: List a): x ∈ List.distinctEq xs ↔ x ∈ xs := {
  forward = m => List.memDistinctFromElim x Nil xs m,
  backward = m =>
    match List.memDistinctFromIntro x Nil xs m with
      | Inl none => Void.exfalso (Bool.falseNotTrue none)
      | Inr found => found
}

-- ... each once.
theorem List.distinctEqNoRepeats [auto eq: DecEq a] (xs: List a): List.Distinct (List.distinctEq xs) := List.distinctFromNoRepeats Nil xs

-- The loop is `distinctFrom` when the set has the same elements as the list
-- `distinctFrom` keeps.

theorem List.distinctSeenInsert [auto ord: Ord a] (seen: Set a) (seenList: List a) (same: (z: a) → Set.contains seen z = List.any seenList (== z))
    (x: a) (z: a): Set.contains (Set.insert seen x) z = List.any (Cons x seenList) (== z) :=
  match e: x == z with
    | True => rewrite DecEq.sound x z e in Set.containsInsert z seen
    | False => rewrite Set.containsInsertOther seen x z (eq => DecEq.soundFalse x z e (Eq.sym eq)) in same z

theorem List.distinctLoopFrom [auto ord: Ord a]: (seen: Set a) → (seenList: List a) → ((z: a) → Set.contains seen z = List.any seenList (== z)) →
    (acc: List a) → (xs: List a) → List.distinctLoop seen acc xs = List.reverseOnto acc (List.distinctFrom seenList xs)
  | seen, seenList, same, acc, Nil => rfl
  | seen, seenList, same, acc, Cons x xs =>
    match c: Set.contains seen x with
      | True =>
        match d: List.any seenList (== x) with
          | True => List.distinctLoopFrom seen seenList same acc xs
          | False => Void.exfalso (Bool.trueNotFalse (Eq.trans (Eq.sym c) (Eq.trans (same x) d)))
      | False =>
        match d: List.any seenList (== x) with
          | True => Void.exfalso (Bool.falseNotTrue (Eq.trans (Eq.sym c) (Eq.trans (same x) d)))
          | False =>
            List.distinctLoopFrom (Set.insert seen x) (Cons x seenList) (z => List.distinctSeenInsert seen seenList same x z) (Cons x acc) xs

-- `distinct` is `distinctEq`, deciding `==` by the ordering's equality.
theorem List.distinctIsDistinctEq [auto ord: Ord a] (xs: List a): List.distinct xs = List.distinctEq [eq := ord.eq] xs :=
  List.distinctLoopFrom Set.empty Nil (z => rfl) Nil xs

-- So it keeps exactly the list's elements ...
theorem List.memDistinct [auto ord: Ord a] (x: a) (xs: List a): x ∈ List.distinct xs ↔ x ∈ xs :=
  rewrite List.distinctIsDistinctEq xs in List.memDistinctEq [eq := ord.eq] x xs

-- ... each once.
theorem List.distinctNoRepeats [auto ord: Ord a] (xs: List a): List.Distinct (List.distinct xs) :=
  rewrite List.distinctIsDistinctEq xs in List.distinctEqNoRepeats [eq := ord.eq] xs

test "List.distinct" := [3, 1, 3, 2, 1].distinct == [3, 1, 2]
test "List.distinct empty" := (Nil: List Nat).distinct == Nil
test "List.distinct all repeats" := [4, 4, 4].distinct == [4]
test "List.distinct already distinct keeps the order" := [2, 5, 1].distinct == [2, 5, 1]
test "List.distinct keeps first occurrences in order" := ["b", "a", "b", "c", "a"].distinct == ["b", "a", "c"]
-- (Here rather than in std/Text/Text.sw: this file needs that one, through `Set`.)
test "List.distinct texts" := ["a", "b", "a"].distinct == ["a", "b"]
test "List.distinct agrees with distinctEq" := [5, 2, 5, 9, 2, 0].distinct == [5, 2, 5, 9, 2, 0].distinctEq
