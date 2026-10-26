-- Combining lists by a key (SW-584): `List.differenceBy` keeps the items of
-- one list whose key no item of another has, and `List.appendNewBy` is the
-- first list, then the second's items whose key is new. A file of its own,
-- so that programs using only the toolkit don't check these.
--
-- Neither removes repeats within a list. `differenceBy` is lodash's
-- `differenceBy`. `appendNewBy` is not lodash's `unionBy` (nor Haskell's
-- `unionBy`), which also drops the repeats within each list: the two agree
-- when each list's keys are distinct, the case `List.distinctKeysAppendNewBy`
-- is about. For a list of records updated from another, `appendNewBy` keeps
-- every record of the first and adds those of the second it doesn't have.

-- The items of `xs` whose key isn't the key of any item of `ys`, in order,
-- repeats kept: `[1, 12, 5].differenceBy [22] (n => n % 10)` is `[1, 5]`.
-- O(length xs × length ys). `ys`'s keys are listed once, not once per item.
def List.differenceBy [auto eq: DecEq k] (xs: List a) (ys: List a) (key: a → k): List a :=
  let keys := ys.map key
  xs.filter (x => key x ∉ keys)

-- `xs`, then the items of `ys` whose key isn't the key of any item of `xs`:
-- `[1, 12].appendNewBy [21, 3, 32] (n => n % 10)` is `[1, 12, 3]`.
-- O(length xs × length ys).
def List.appendNewBy [auto eq: DecEq k] (xs: List a) (ys: List a) (key: a → k): List a :=
  List.append xs (List.differenceBy ys xs key)

-- `differenceBy` is a `filter` with `∉`, as written.
theorem List.differenceByIsFilter [auto eq: DecEq k] (xs: List a) (ys: List a) (key: a → k):
    List.differenceBy xs ys key = List.filter xs (x => key x ∉ List.map ys key) :=
  rfl

-- What the filter keeps says its key is new.
theorem List.notMemOfNotIn [auto eq: DecEq k] (z: k) (zs: List k) (h: Bool.not (z ∈ zs) = True): z ∉ zs :=
  Decidable.toBoolFalse (List.decMem z zs)
    (match d: Decidable.toBool (List.decMem z zs) with
      | True => Void.exfalso (Bool.falseNotTrue h)
      | False => rfl)

theorem List.notInOfNotMem [auto eq: DecEq k] (z: k) (zs: List k) (out: z ∉ zs): Bool.not (z ∈ zs) = True :=
  rewrite Decidable.toBoolOfNot (List.decMem z zs) out in rfl

-- What `differenceBy` keeps: the items of `xs` whose key no item of `ys` has.
theorem List.memDifferenceBy [auto eq: DecEq k] (x: a) (xs: List a) (ys: List a) (key: a → k):
    x ∈ List.differenceBy xs ys key ↔ x ∈ xs ∧ key x ∉ List.map ys key := {
  forward = m =>
    match List.memFilter xs (y => key y ∉ List.map ys key) x m with
      | Both inXs keep => Both inXs (List.notMemOfNotIn (key x) (List.map ys key) keep),
  backward = h =>
    match h with
      | Both inXs out => List.memFilterIntro xs (y => key y ∉ List.map ys key) x inXs (List.notInOfNotMem (key x) (List.map ys key) out)
}

-- What `appendNewBy` has: the items of `xs`, and those of `ys` whose key no
-- item of `xs` has.
theorem List.memAppendNewBy [auto eq: DecEq k] (x: a) (xs: List a) (ys: List a) (key: a → k):
    x ∈ List.appendNewBy xs ys key ↔ x ∈ xs ∨ (x ∈ ys ∧ key x ∉ List.map xs key) := {
  forward = m =>
    match List.memAppend x xs (List.differenceBy ys xs key) m with
      | Inl inXs => Inl inXs
      | Inr inNew => Inr ((List.memDifferenceBy x ys xs key).forward inNew),
  backward = h =>
    match h with
      | Inl inXs => List.memAppendLeft x xs (List.differenceBy ys xs key) inXs
      | Inr found => List.memAppendRight x xs (List.differenceBy ys xs key) ((List.memDifferenceBy x ys xs key).backward found)
}

-- No key of `differenceBy xs ys key` is a key of `ys`.
theorem List.disjointKeysDifferenceBy [auto eq: DecEq k] (xs: List a) (ys: List a) (key: a → k):
    List.Disjoint (List.map ys key) (List.map (List.differenceBy xs ys key) key) :=
  List.allOfMem (z => z ∉ List.map (List.differenceBy xs ys key) key) (List.map ys key) (z inYs m =>
    List.anyElim (y => key y = z) Void (List.differenceBy xs ys key) (List.memMapAny (List.differenceBy xs ys key) key z m)
      (y inNew e =>
        match (List.memDifferenceBy y xs ys key).forward inNew with
          | Both inXs out => out (rewrite e in inYs)))

-- With the keys of each list distinct, the keys of `appendNewBy` are
-- distinct: what it's for, merging two keyed collections.
theorem List.distinctKeysAppendNewBy [auto eq: DecEq k] (xs: List a) (ys: List a) (key: a → k)
    (dx: List.Distinct (List.map xs key)) (dy: List.Distinct (List.map ys key)):
    List.Distinct (List.map (List.appendNewBy xs ys key) key) :=
  List.distinctMapAppend key xs (List.differenceBy ys xs key) dx
    (List.distinctMapFilter ys key (y => key y ∉ List.map xs key) dy)
    (List.disjointKeysDifferenceBy ys xs key)

-- `differenceBy` keeps nothing when every key of `xs` is a key of `ys` ...
theorem List.differenceByCovered [auto eq: DecEq k] (xs: List a) (ys: List a) (key: a → k)
    (covered: (x: a) → x ∈ xs → key x ∈ List.map ys key): List.differenceBy xs ys key = Nil :=
  List.filterNone (x => key x ∉ List.map ys key) xs (x m =>
    rewrite Decidable.toBoolOf (List.decMem (key x) (List.map ys key)) (covered x m) in rfl)

-- ... and everything when no key of `xs` is.
theorem List.differenceByDisjoint [auto eq: DecEq k] (xs: List a) (ys: List a) (key: a → k)
    (apart: (x: a) → x ∈ xs → key x ∉ List.map ys key): List.differenceBy xs ys key = xs :=
  List.filterAll (x => key x ∉ List.map ys key) xs (x m => List.notInOfNotMem (key x) (List.map ys key) (apart x m))

-- So `appendNewBy` adds nothing when `ys` has no new key ...
theorem List.appendNewByCovered [auto eq: DecEq k] (xs: List a) (ys: List a) (key: a → k)
    (covered: (y: a) → y ∈ ys → key y ∈ List.map xs key): List.appendNewBy xs ys key = xs :=
  rewrite List.differenceByCovered ys xs key covered in List.appendNil xs

-- ... so it is idempotent: a list merged with itself is itself, whatever
-- its keys.
theorem List.appendNewBySelf [auto eq: DecEq k] (xs: List a) (key: a → k): List.appendNewBy xs xs key = xs :=
  List.appendNewByCovered xs xs key (x m => List.memMap xs x m key)

theorem List.differenceByExample: List.differenceBy [1, 12, 5] [22] (n => n % 10) = [1, 5] := rfl

theorem List.appendNewByExample: List.appendNewBy [1, 12] [21, 3, 32] (n => n % 10) = [1, 12, 3] := rfl

-- Merging `[1, 2]` and `[2, 3]` (the successors of `[1, 2]`) by the
-- numbers themselves, no number is there twice.
theorem List.distinctKeysAppendNewByExample: List.Distinct (List.map (List.appendNewBy [1, 2] (List.map [1, 2] Succ) (n => n)) (n => n)) :=
  List.distinctKeysAppendNewBy [1, 2] (List.map [1, 2] Succ) (n => n) List.distinctExample List.distinctMapExample

theorem List.memDifferenceByExample: 5 ∈ List.differenceBy [1, 12, 5] [22] (n => n % 10) :=
  (List.memDifferenceBy 5 [1, 12, 5] [22] (n => n % 10)).backward (Both (Inr (Inr (Inl rfl)))
    (List.notMemOfNotIn [eq := Nat.instDecEq] (5 % 10) (List.map [22] (n => n % 10)) rfl))

theorem List.appendNewBySelfExample (xs: List Nat): List.appendNewBy xs xs (n => n % 10) = xs :=
  List.appendNewBySelf xs (n => n % 10)

test "List.differenceBy" := [1, 12, 5].differenceBy [22] (n => n % 10) == [1, 5]
test "List.differenceBy keeps repeats" := [1, 1, 2].differenceBy [2] (n => n) == [1, 1]
test "List.differenceBy of nothing" := [1, 2].differenceBy Nil (n => n) == [1, 2] ∧ (Nil: List Nat).differenceBy [1] (n => n) == Nil
test "List.appendNewBy" := [1, 12].appendNewBy [21, 3, 32] (n => n % 10) == [1, 12, 3]
test "List.appendNewBy keeps repeats within a list" := [1, 1].appendNewBy [2, 2, 1] (n => n) == [1, 1, 2, 2]
test "List.appendNewBy keeps the first list's item for a shared key" :=
  [("a", 1), ("b", 2)].appendNewBy [("b", 20), ("c", 30)] Pair.fst == [("a", 1), ("b", 2), ("c", 30)]
test "List.appendNewBy with itself" := [3, 1, 3].appendNewBy [3, 1, 3] (n => n) == [3, 1, 3]
