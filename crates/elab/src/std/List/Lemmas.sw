-- Lemmas about the list toolkit's functions (List/Toolkit.sw): lengths,
-- sums and counts, membership, permutations, congruence, `get`, and the like,
-- with the examples and tests that use them.

theorem List.lengthAppend: (xs: List a) → (ys: List a) → List.length (List.append xs ys) = List.length xs + List.length ys
  | Nil, ys => rfl
  | Cons x xs, ys => Eq.cong Succ (List.lengthAppend xs ys)

-- Splitting a list at `n` and joining the parts gives it back.
theorem List.appendTakeDrop: (xs: List a) → (n: Nat) → List.append (List.take xs n) (List.drop xs n) = xs
  | xs, Zero => rfl
  | Nil, Succ n => rfl
  | Cons x xs, Succ n => Eq.cong (Cons x) (List.appendTakeDrop xs n)

theorem List.scanLeftNil: List.scanLeft Nil 5 (acc x => acc + x) = [5] := rfl

theorem List.scanLeftSums: List.scanLeft [1, 2, 3] 0 (acc x => acc + x) = [0, 1, 3, 6] := rfl

theorem List.foldLeftReverseOnto: (xs: List a) → (acc: List a) → (z: b) → (f: a → b → b) →
    List.foldLeft (List.reverseOnto xs acc) z (r x => f x r)
      = List.foldLeft acc (List.foldLeft (List.reverseOnto xs Nil) z (r x => f x r)) (r x => f x r)
  | Nil, acc, z, f => rfl
  | Cons x xs, acc, z, f =>
    Eq.trans (List.foldLeftReverseOnto xs (Cons x acc) z f)
      (Eq.sym (Eq.cong (r => List.foldLeft acc r (r2 y => f y r2)) (List.foldLeftReverseOnto xs (Cons x Nil) z f)))

-- The step of the right fold, which the loop form hides.
theorem List.foldRightCons (xs: List a) (x: a) (z: b) (f: a → b → b): List.foldRight (Cons x xs) z f = f x (List.foldRight xs z f) :=
  List.foldLeftReverseOnto xs (Cons x Nil) z f

theorem List.sumByDoubles: List.sumBy [1, 2, 3] (x => x * 2) = 12 := rfl

theorem List.sumInts: List.sum [(3: Int), -5, 1] = -1 := rfl

theorem List.sumByInts: List.sumBy [(1: Int), 2, 3] (x => Int.sub 1 x) = -3 := rfl

-- A sum is a `sumBy` of each element itself.
theorem List.sumIsSumBy [auto add: Add a] (xs: List a): List.sum xs = List.sumBy xs (x => x) := rfl

theorem List.zipWithNextExample: List.zipWithNext [1, 2, 3] = [MkPair 1 2, MkPair 2 3] := rfl

-- One pair fewer than there are elements.
theorem List.lengthZipWithNext: (xs: List a) → List.length (List.zipWithNext xs) = List.length xs - 1
  | Nil => rfl
  | Cons x Nil => rfl
  | Cons x (Cons next rest) => rewrite List.lengthZipWithNext (Cons next rest)

-- The list zipped with its own tail.
theorem List.zipWithNextZip: (xs: List a) → List.zipWithNext xs = List.zip xs (List.tailOf xs)
  | Nil => rfl
  | Cons x Nil => rfl
  | Cons x (Cons next rest) => rewrite List.zipWithNextZip (Cons next rest)

theorem List.chainEmpty (holds: a → a → Bool): List.chain Nil holds = True := rfl

theorem List.chainSingle (x: a) (holds: a → a → Bool): List.chain [x] holds = True := rfl

theorem List.chainCons (x: a) (next: a) (rest: List a) (holds: a → a → Bool):
    List.chain (Cons x (Cons next rest)) holds = (holds x next ∧ List.chain (Cons next rest) holds) := rfl

-- `holds` is true of every pair `zipWithNext` gives.
theorem List.chainZipWithNext: (xs: List a) → (holds: a → a → Bool) →
    List.chain xs holds = (List.zipWithNext xs |> .all (pair => holds pair.fst pair.snd))
  | Nil, holds => rfl
  | Cons x Nil, holds => rfl
  | Cons x (Cons next rest), holds => rewrite List.chainZipWithNext (Cons next rest) holds in rfl

-- Without the first element, it still holds.
theorem List.chainTail: (xs: List a) → (holds: a → a → Bool) → List.chain xs holds = True → List.chain (List.tailOf xs) holds = True
  | Nil, holds, chained => rfl
  | Cons x Nil, holds, chained => rfl
  | Cons x (Cons next rest), holds, chained => Bool.andRight _ _ chained

-- Without the last element (`List.init`), it still holds.
theorem List.chainInit: (xs: List a) → (holds: a → a → Bool) → List.chain xs holds = True → List.chain (List.init xs) holds = True
  | Nil, holds, chained => rfl
  | Cons x rest, holds, chained => List.chainInitCons x rest holds chained

theorem List.chainInitCons: (x: a) → (rest: List a) → (holds: a → a → Bool) →
    List.chain (Cons x rest) holds = True → List.chain (List.init (Cons x rest)) holds = True
  | x, Nil, holds, chained => rfl
  | x, Cons next Nil, holds, chained => rfl
  | x, Cons next (Cons after more), holds, chained =>
    let first := Bool.andLeft _ _ chained
    let kept := List.chainInitCons next (Cons after more) holds (Bool.andRight _ _ chained)
    Bool.andIntro _ _ first kept

-- Both tests hold of every pair when each one does.
theorem List.chainAnd: (xs: List a) → (holds1: a → a → Bool) → (holds2: a → a → Bool) →
    List.chain xs (x y => holds1 x y ∧ holds2 x y) = (List.chain xs holds1 ∧ List.chain xs holds2)
  | Nil, holds1, holds2 => rfl
  | Cons x Nil, holds1, holds2 => rfl
  | Cons x (Cons next rest), holds1, holds2 =>
    rewrite List.chainAnd (Cons next rest) holds1 holds2 in cases

-- `all` and `any` over a cons: the head's answer, then the rest's.
theorem List.allCons (p: a → Bool) (x: a) (xs: List a): List.all (Cons x xs) p = (p x ∧ List.all xs p) := rfl

theorem List.anyCons (p: a → Bool) (x: a) (xs: List a): List.any (Cons x xs) p = (p x ∨ List.any xs p) := rfl

-- A run of `a + b` numbers is a run of `a` followed by a run of `b`.
theorem List.rangeFromAppend: (a: Nat) → (b: Nat) → (s: Nat) → List.rangeFrom (a + b) s = List.append (List.rangeFrom a s) (List.rangeFrom b (s + a))
  | Zero, b, s => Eq.cong (t => List.rangeFrom b t) (Eq.sym (Nat.addZero s))
  | Succ a, b, s =>
    Eq.cong (Cons s) (Eq.trans (List.rangeFromAppend a b (Succ s)) (Eq.cong (t => List.append (List.rangeFrom a (Succ s)) (List.rangeFrom b t)) (Eq.sym (Nat.addSucc s a))))

-- `between` is a `rangeFrom` of the right length.
theorem List.betweenRangeFrom (lo: Nat) (hi: Nat): List.between lo hi = List.rangeFrom (hi + 1 - lo) lo := rfl

-- It has `hi + 1 - lo` elements: none when `lo > hi`, one when `lo = hi`.
theorem List.lengthBetween (lo: Nat) (hi: Nat): List.length (List.between lo hi) = hi + 1 - lo := List.lengthRangeFrom (hi + 1 - lo) lo

test "List.lengthBetween" := List.length (List.between 3 3) == 1 ∧ List.length (List.between 5 2) == 0 ∧ List.length (List.between 2 6) == 5

theorem List.headExample: List.head [3, 4] = Some 3 := rfl

theorem List.headEmpty: List.head (Nil: List Nat) = None := rfl

theorem List.initExample: List.init [1, 2, 3] = [1, 2] := rfl

theorem List.initEmpty: List.init (Nil: List Nat) = Nil := rfl

-- The loop's sides are the two `filter`s, each after what it had sorted.
theorem List.partitionOntoFilters (p: a → Bool): (xs: List a) → (kept: List a) → (dropped: List a) →
    List.partitionOnto p xs (MkPair kept dropped)
      = MkPair (List.reverseOnto kept (List.filter xs p)) (List.reverseOnto dropped (List.filter xs (x => ¬(p x))))
  | Nil, kept, dropped => rfl
  | Cons x xs, kept, dropped =>
    match p x with
      | True => List.partitionOntoFilters p xs (Cons x kept) dropped
      | False => List.partitionOntoFilters p xs kept (Cons x dropped)

-- `partition` is the two `filter`s (its definition before it became one pass).
theorem List.partitionFilters (xs: List a) (p: a → Bool): List.partition xs p = MkPair (List.filter xs p) (List.filter xs (x => ¬(p x))) :=
  List.partitionOntoFilters p xs Nil Nil

theorem List.partitionExample: List.partition [1, 5, 2, 7] (x => x > 4) = MkPair [5, 7] [1, 2] := rfl

theorem List.lengthReplicate (x: a): (n: Nat) → List.length (List.replicate n x) = n
  | Zero => rfl
  | Succ n => Eq.cong Succ (List.lengthReplicate x n)

-- Padding makes a list exactly n long, when it was no longer than that.
theorem List.padRightLength (xs: List a) (n: Nat) (x: a) (h: List.length xs ≤ n):
    List.length (List.padRight xs n x) = n :=
  Eq.trans (List.lengthAppend xs (List.replicate (n - List.length xs) x))
    (Eq.trans (Eq.cong (t => List.length xs + t) (List.lengthReplicate x (n - List.length xs)))
      (Nat.addSubCancel (List.length xs) n h))

theorem List.padRightExample: List.padRight [1, 2] 4 0 = [1, 2, 0, 0] := rfl

theorem List.padRightLongEnough: List.padRight [1, 2] 1 0 = [1, 2] := rfl

-- Lemmas about `List.transpose`: it has as many columns as the first row is
-- long, and for a rectangular list, doing it twice gives back the list.
theorem List.lengthMap: (xs: List a) → (f: a → b) → List.length (List.map xs f) = List.length xs
  | Nil, f => rfl
  | Cons x xs, f => Eq.cong Succ (List.lengthMap xs f)

theorem List.transposeExample: List.transpose [[1, 2, 3], [4, 5, 6]] = [[1, 4], [2, 5], [3, 6]] := rfl

theorem List.transposeNone: List.transpose (Nil: List (List Nat)) = Nil := rfl

theorem List.transposeShortRow: List.transpose [[1, 2], [3], [4, 5]] = [[1, 3, 4], [2, 5]] := rfl

theorem List.transposeNLength: (n: Nat) → (rows: List (List a)) → List.length (List.transposeN n rows) = n
  | Zero, rows => rfl
  | Succ n, rows => Eq.cong Succ (List.transposeNLength n (List.map rows (.drop 1)))

theorem List.allAppend (p: a → Prop): (xs: List a) → (ys: List a) → List.All p xs → List.All p ys → List.All p (List.append xs ys)
  | Nil, ys, hx, hy => hy
  | Cons x xs, ys, Both hx hxs, hy => Both hx (List.allAppend p xs ys hxs hy)

theorem List.allAppendLeft (p: a → Prop): (xs: List a) → (ys: List a) → List.All p (List.append xs ys) → List.All p xs
  | Nil, ys, h => Trivial
  | Cons x xs, ys, Both h hxs => Both h (List.allAppendLeft p xs ys hxs)

theorem List.allAppendRight (p: a → Prop): (xs: List a) → (ys: List a) → List.All p (List.append xs ys) → List.All p ys
  | Nil, ys, h => h
  | Cons x xs, ys, Both h hxs => List.allAppendRight p xs ys hxs

theorem List.allMap: (xs: List a) → (p: b → Prop) → (f: a → b) → List.All (x => p (f x)) xs → List.All p (List.map xs f)
  | Nil, p, f, h => Trivial
  | Cons x xs, p, f, Both h hxs => Both h (List.allMap xs p f hxs)

theorem List.allImplies (p: a → Prop) (q: a → Prop) (h: (x: a) → p x → q x): (xs: List a) → List.All p xs → List.All q xs
  | Nil, hp => Trivial
  | Cons x xs, Both hpx hpxs => Both (h x hpx) (List.allImplies p q h xs hpxs)

theorem List.anyAppendLeft (p: a → Prop): (xs: List a) → (ys: List a) → List.Any p xs → List.Any p (List.append xs ys)
  | Nil, ys, h => Void.exfalso h
  | Cons x xs, ys, Inl h => Inl h
  | Cons x xs, ys, Inr h => Inr (List.anyAppendLeft p xs ys h)

theorem List.anyAppendRight (p: a → Prop): (xs: List a) → (ys: List a) → List.Any p ys → List.Any p (List.append xs ys)
  | Nil, ys, h => h
  | Cons x xs, ys, h => Inr (List.anyAppendRight p xs ys h)

-- `List.any` of two lists joined: either list has one.
theorem List.anyAppend: (xs: List a) → (ys: List a) → (p: a → Bool) → List.any (List.append xs ys) p = (List.any xs p ∨ List.any ys p)
  | Nil, ys, p => rfl
  | Cons x xs, ys, p =>
    match e: p x with
      | True => rfl
      | False => List.anyAppend xs ys p

theorem List.anyAppendExample: List.any (List.append [1, 2] [3]) (x => x == 3) = (False ∨ True) := rfl

theorem List.lengthZero: (xs: List a) → List.length xs = 0 → xs = Nil
  | Nil, h => rfl
  | Cons y ys, h => Void.exfalso (Nat.succNotZero (List.length ys) h)

theorem List.transposeNNil: (n: Nat) → List.transposeN n (Nil: List (List a)) = List.replicate n Nil
  | Zero => rfl
  | Succ n => Eq.cong (Cons Nil) (List.transposeNNil n)

theorem List.allLengthZero: (rows: List (List a)) → (n: Nat) → List.length rows = n → List.AllLength 0 rows →
    rows = List.replicate n Nil
  | Nil, n, hl, hr => J (y q => (Nil: List (List a)) = List.replicate y (Nil: List a)) rfl hl
  | Cons r rs, Zero, hl, hr => Void.exfalso (Nat.succNotZero (List.length rs) hl)
  | Cons r rs, Succ m, hl, Both hr hrs =>
    Eq.trans (Eq.cong (t => Cons t rs) (List.lengthZero r hr))
      (Eq.cong (Cons Nil) (List.allLengthZero rs m (Nat.succInjective (List.length rs) m hl) hrs))

theorem List.tailsAllLength: (rows: List (List a)) → (k: Nat) → List.AllLength (Succ k) rows →
    List.AllLength k (List.map rows (.drop 1))
  | Nil, k, hr => Trivial
  | Cons Nil rs, k, Both hr hrs => Void.exfalso (Nat.zeroNotSucc k hr)
  | Cons (Cons y ys) rs, k, Both hr hrs => Both (Nat.succInjective (List.length ys) k hr) (List.tailsAllLength rs k hrs)

theorem List.headsLength: (rows: List (List a)) → (k: Nat) → List.AllLength (Succ k) rows →
    List.length (List.filterMap rows (.get 0)) = List.length rows
  | Nil, k, hr => rfl
  | Cons Nil rs, k, Both hr hrs => Void.exfalso (Nat.zeroNotSucc k hr)
  | Cons (Cons y ys) rs, k, Both hr hrs => Eq.cong Succ (List.headsLength rs k hrs)

theorem List.rowsAreHeadsAndTails: (rows: List (List a)) → (k: Nat) → List.AllLength (Succ k) rows →
    rows = List.zipWith (List.filterMap rows (.get 0)) (List.map rows (.drop 1)) Cons
  | Nil, k, hr => rfl
  | Cons Nil rs, k, Both hr hrs => Void.exfalso (Nat.zeroNotSucc k hr)
  | Cons (Cons y ys) rs, k, Both hr hrs => Eq.cong (Cons (Cons y ys)) (List.rowsAreHeadsAndTails rs k hrs)

theorem List.columnsAllLength: (w: Nat) → (rows: List (List a)) → (h: Nat) → List.length rows = h → List.AllLength w rows →
    List.AllLength h (List.transposeN w rows)
  | Zero, rows, h, hl, hr => Trivial
  | Succ k, rows, h, hl, hr =>
    Both (Eq.trans (List.headsLength rows k hr) hl)
      (List.columnsAllLength k (List.map rows (.drop 1)) h (Eq.trans (List.lengthMap rows (.drop 1)) hl) (List.tailsAllLength rows k hr))

theorem List.transposeNCons: (heads: List a) → (h: Nat) → (cols: List (List a)) → List.length heads = h → List.AllLength h cols →
    List.transposeN h (Cons heads cols) = List.zipWith heads (List.transposeN h cols) Cons
  | Nil, Zero, cols, hl, hc => rfl
  | Cons x xs, Zero, cols, hl, hc => Void.exfalso (Nat.succNotZero (List.length xs) hl)
  | Nil, Succ m, cols, hl, hc => Void.exfalso (Nat.zeroNotSucc m hl)
  | Cons x xs, Succ m, cols, hl, hc =>
    Eq.cong (Cons (Cons x (List.filterMap cols (.get 0))))
      (List.transposeNCons xs m (List.map cols (.drop 1)) (Nat.succInjective (List.length xs) m hl) (List.tailsAllLength cols m hc))

theorem List.transposeNTwice: (w: Nat) → (h: Nat) → (rows: List (List a)) → List.length rows = h → List.AllLength w rows →
    List.transposeN h (List.transposeN w rows) = rows
  | Zero, h, rows, hl, hr => Eq.trans (List.transposeNNil h) (Eq.sym (List.allLengthZero rows h hl hr))
  | Succ k, h, rows, hl, hr =>
    Eq.trans
      (List.transposeNCons (List.filterMap rows (.get 0)) h (List.transposeN k (List.map rows (.drop 1)))
        (Eq.trans (List.headsLength rows k hr) hl)
        (List.columnsAllLength k (List.map rows (.drop 1)) h (Eq.trans (List.lengthMap rows (.drop 1)) hl) (List.tailsAllLength rows k hr)))
      (Eq.trans
        (Eq.cong (tails => List.zipWith (List.filterMap rows (.get 0)) tails Cons)
          (List.transposeNTwice k h (List.map rows (.drop 1)) (Eq.trans (List.lengthMap rows (.drop 1)) hl) (List.tailsAllLength rows k hr)))
        (Eq.sym (List.rowsAreHeadsAndTails rows k hr)))

-- There are as many columns as the first row is long.
theorem List.transposeLength (rows: List (List a)): List.length (List.transpose rows) = List.length (List.headOr rows Nil) :=
  List.transposeNLength (List.length (List.headOr rows Nil)) rows

-- Transposing a rectangular list (every row the same non-zero length) twice
-- gives the list back. (With rows of length 0, the first transpose is empty
-- and the rows are lost.)
theorem List.transposeTwice (k: Nat): (rows: List (List a)) → List.AllLength (Succ k) rows →
    List.transpose (List.transpose rows) = rows
  | Nil, hr => rfl
  | Cons r rs, Both hr hrs =>
    J (y q => List.transposeN (List.length (List.headOr (List.transposeN y (Cons r rs)) Nil)) (List.transposeN y (Cons r rs)) = Cons r rs)
      (List.transposeNTwice (Succ k) (List.length (List.headOr (List.transposeN (Succ k) (Cons r rs)) Nil)) (Cons r rs)
        (Eq.sym (List.headsLength (Cons r rs) k (Both hr hrs))) (Both hr hrs))
      (Eq.sym hr)

-- The step of `List.splitGroups`, which the loop form hides.
theorem List.splitGroupsCons (xs: List a) (x: a) (p: a → Bool):
    List.splitGroups (Cons x xs) p = List.splitStep x (p x) (List.splitGroups xs p) :=
  List.foldRightCons xs x (MkPair Nil Nil) (y st => List.splitStep y (p y) st)

theorem List.closeGroupSum: (cur: List a) → (done: List (List a)) →
    List.sumBy (List.closeGroup cur done) List.length = List.length cur + List.sumBy done List.length
  | Nil, done => rfl
  | Cons y ys, done => List.sumByCons done (Cons y ys) List.length

theorem List.splitStepTotal (x: a): (b: Bool) → (st: Pair (List a) (List (List a))) →
    List.splitTotal (List.splitStep x b st) + Bool.toNat b = Succ (List.splitTotal st)
  | True, MkPair cur done =>
    Eq.trans (Nat.addOne (List.sumBy (List.closeGroup cur done) List.length)) (Eq.cong Succ (List.closeGroupSum cur done))
  | False, MkPair cur done => Nat.addZero (Succ (List.length cur + List.sumBy done List.length))

theorem List.splitGroupsTotal: (xs: List a) → (p: a → Bool) →
    List.splitTotal (List.splitGroups xs p) + List.occurrences xs p = List.length xs
  | Nil, p => rfl
  | Cons x xs, p =>
    rewrite List.splitGroupsCons xs x p in
      Eq.trans (Eq.sym (Nat.addAssoc (List.splitTotal (List.splitStep x (p x) (List.splitGroups xs p))) (Bool.toNat (p x)) (List.occurrences xs p)))
        (Eq.trans (Eq.cong (t => t + List.occurrences xs p) (List.splitStepTotal x (p x) (List.splitGroups xs p)))
          (Eq.cong Succ (List.splitGroupsTotal xs p)))

theorem List.finishGroupsSum: (st: Pair (List a) (List (List a))) →
    List.sumBy (List.finishGroups st) List.length = List.splitTotal st
  | MkPair cur done => List.closeGroupSum cur done

-- The groups hold every element that isn't a separator, and nothing else.
theorem List.splitByExample: List.splitBy [1, 2, 0, 0, 3] (x => x == 0) = [[1, 2], [3]] := rfl

theorem List.splitByEdges: List.splitBy [0, 4, 0] (x => x == 0) = [[4]] := rfl

-- Splitting loses only the separators: the groups' lengths plus the number of separators is the length.
theorem List.splitByLength (xs: List a) (p: a → Bool):
    List.sumBy (List.splitBy xs p) List.length + List.occurrences xs p = List.length xs :=
  Eq.trans (Eq.cong (t => t + List.occurrences xs p) (List.finishGroupsSum (List.splitGroups xs p))) (List.splitGroupsTotal xs p)

theorem List.closeGroupGroups (p: a → Bool): (cur: List a) → (done: List (List a)) → List.NonSep p cur → List.Groups p done →
    List.Groups p (List.closeGroup cur done)
  | Nil, done, hc, hd => hd
  | Cons y ys, done, hc, hd => Both (Both (Nat.zeroLe (List.length ys)) hc) hd

theorem List.nonSepCons (p: a → Bool) (x: a) (cur: List a) (h: p x = False) (hc: List.NonSep p cur): List.NonSep p (Cons x cur) :=
  rewrite h in hc

theorem List.splitStepOk (p: a → Bool) (x: a): (b: Bool) → p x = b → (st: Pair (List a) (List (List a))) → List.SplitOk p st →
    List.SplitOk p (List.splitStep x b st)
  | True, e, MkPair cur done, Both hc hd => Both rfl (List.closeGroupGroups p cur done hc hd)
  | False, e, MkPair cur done, Both hc hd => Both (List.nonSepCons p x cur e hc) hd

theorem List.splitGroupsOk: (xs: List a) → (p: a → Bool) → List.SplitOk p (List.splitGroups xs p)
  | Nil, p => Both rfl Trivial
  | Cons x xs, p =>
    rewrite List.splitGroupsCons xs x p in List.splitStepOk p x (p x) rfl (List.splitGroups xs p) (List.splitGroupsOk xs p)

theorem List.finishGroupsOk (p: a → Bool): (st: Pair (List a) (List (List a))) → List.SplitOk p st → List.Groups p (List.finishGroups st)
  | MkPair cur done, Both hc hd => List.closeGroupGroups p cur done hc hd

-- No group is empty, and none has a separator in it.
theorem List.splitByGroups (xs: List a) (p: a → Bool): List.Groups p (List.splitBy xs p) :=
  List.finishGroupsOk p (List.splitGroups xs p) (List.splitGroupsOk xs p)

theorem List.closeGroupConcat: (cur: List a) → (done: List (List a)) →
    List.concat (List.closeGroup cur done) = List.append cur (List.concat done)
  | Nil, done => rfl
  | Cons y ys, done => rfl

theorem List.splitStepKeeps (p: a → Bool) (x: a) (xs: List a): (b: Bool) → p x = b → (st: Pair (List a) (List (List a))) →
    List.SplitKeeps p xs st → List.SplitKeeps p (Cons x xs) (List.splitStep x b st)
  | True, e, MkPair cur done, h =>
    Eq.trans (List.closeGroupConcat cur done)
      (Eq.trans h (Eq.sym (List.filterSkip xs (z => ¬(p z)) x (Eq.cong Bool.not e))))
  | False, e, MkPair cur done, h =>
    Eq.trans (Eq.cong (Cons x) h) (Eq.sym (List.filterKeep xs (z => ¬(p z)) x (Eq.cong Bool.not e)))

theorem List.splitGroupsKeeps: (xs: List a) → (p: a → Bool) → List.SplitKeeps p xs (List.splitGroups xs p)
  | Nil, p => rfl
  | Cons x xs, p =>
    rewrite List.splitGroupsCons xs x p in List.splitStepKeeps p x xs (p x) rfl (List.splitGroups xs p) (List.splitGroupsKeeps xs p)

theorem List.finishGroupsConcat: (st: Pair (List a) (List (List a))) →
    List.concat (List.finishGroups st) = List.append (Pair.fst st) (List.concat (Pair.snd st))
  | MkPair cur done => List.closeGroupConcat cur done

-- Joining the groups gives back the elements that aren't separators, in order.
theorem List.splitByConcat (xs: List a) (p: a → Bool):
    List.concat (List.splitBy xs p) = List.filter xs (x => ¬(p x)) :=
  Eq.trans (List.finishGroupsConcat (List.splitGroups xs p)) (List.splitGroupsKeeps xs p)

-- Only separators: no group, open or finished.
theorem List.splitGroupsSeparators: (ys: List a) → (p: a → Bool) → List.all ys p = True → List.splitGroups ys p = MkPair Nil Nil
  | Nil, p, h => rfl
  | Cons y ys, p, h =>
    match e: p y with
      | True => rewrite List.splitGroupsCons ys y p, e, List.splitGroupsSeparators ys p h
      | False => Void.exfalso (Bool.falseNotTrue h)

theorem List.splitGroupsAppendSeparators (ys: List a) (p: a → Bool) (h: List.all ys p = True): (xs: List a) →
    List.splitGroups (List.append xs ys) p = List.splitGroups xs p
  | Nil => List.splitGroupsSeparators ys p h
  | Cons x xs => rewrite List.splitGroupsCons (List.append xs ys) x p, List.splitGroupsCons xs x p, List.splitGroupsAppendSeparators ys p h xs

-- Separators on the end change no group: `[1, 0, 0]` splits as `[1]` does.
theorem List.splitByAppendSeparators (xs: List a) (p: a → Bool) (ys: List a) (h: List.all ys p = True):
    List.splitBy (List.append xs ys) p = List.splitBy xs p :=
  Eq.cong List.finishGroups (List.splitGroupsAppendSeparators ys p h xs)

-- Sums from a starting total, and one element at a time, for any `Add`:
-- the laws `zeroAdd`, `assoc` and `comm` (docs/proposals/interfaces.md §7.7).
theorem Add.addZero [auto add: Add a] (x: a): x + Add.zero = x :=
  Eq.trans (add.comm x Add.zero) (add.zeroAdd x)

theorem Add.addSwap [auto add: Add a] (w: a) (x: a) (y: a) (z: a): (w + x) + (y + z) = (w + y) + (x + z) :=
  calc (w + x) + (y + z)
    _ = w + (x + (y + z)) := add.assoc w x (y + z)
    _ = w + ((x + y) + z) := Eq.cong (t => w + t) (Eq.sym (add.assoc x y z))
    _ = w + ((y + x) + z) := Eq.cong (t => w + (t + z)) (add.comm x y)
    _ = w + (y + (x + z)) := Eq.cong (t => w + t) (add.assoc y x z)
    _ = (w + y) + (x + z) := Eq.sym (add.assoc w y (x + z))

theorem Add.addLeftComm [auto add: Add a] (x: a) (y: a) (z: a): x + (y + z) = y + (x + z) :=
  calc x + (y + z)
    _ = (x + y) + z := Eq.sym (add.assoc x y z)
    _ = (y + x) + z := Eq.cong (t => t + z) (add.comm x y)
    _ = y + (x + z) := add.assoc y x z

theorem List.sumByFrom [auto add: Add b]: (xs: List a) → (z: b) → (f: a → b) → List.foldLeft xs z (acc x => acc + f x) = z + List.sumBy xs f
  | Nil, z, f => Eq.sym (Add.addZero z)
  | Cons x xs, z, f =>
    calc List.foldLeft xs (z + f x) (acc x => acc + f x)
      _ = (z + f x) + List.sumBy xs f := List.sumByFrom xs (z + f x) f
      _ = z + (f x + List.sumBy xs f) := add.assoc z (f x) (List.sumBy xs f)
      _ = z + List.foldLeft xs (f x) (acc x => acc + f x) := Eq.cong (t => z + t) (Eq.sym (List.sumByFrom xs (f x) f))
      _ = z + List.sumBy (Cons x xs) f := Eq.cong (t => z + List.foldLeft xs t (acc x => acc + f x)) (Eq.sym (add.zeroAdd (f x)))

theorem List.sumByCons [auto add: Add b] (xs: List a) (x: a) (f: a → b): List.sumBy (Cons x xs) f = f x + List.sumBy xs f :=
  Eq.trans (Eq.cong (t => List.foldLeft xs t (acc x => acc + f x)) (add.zeroAdd (f x))) (List.sumByFrom xs (f x) f)

theorem List.sumByAppend [auto add: Add b] (xs: List a) (ys: List a) (f: a → b): List.sumBy (List.append xs ys) f = List.sumBy xs f + List.sumBy ys f :=
  Eq.trans (List.foldLeftAppend xs Add.zero ys (acc x => acc + f x)) (List.sumByFrom ys (List.sumBy xs f) f)

theorem List.filterKeep (xs: List a) (p: a → Bool) (x: a) (h: p x = True): List.filter (Cons x xs) p = Cons x (List.filter xs p) :=
  J (c q => List.filterStep x (List.filter xs p) c = Cons x (List.filter xs p)) rfl (Eq.sym h)

theorem List.filterSkip (xs: List a) (p: a → Bool) (x: a) (h: p x = False): List.filter (Cons x xs) p = List.filter xs p :=
  J (c q => List.filterStep x (List.filter xs p) c = List.filter xs p) rfl (Eq.sym h)

theorem List.foldLeftAppend: (xs: List a) → (z: b) → (ys: List a) → (f: b → a → b) →
    List.foldLeft (List.append xs ys) z f = List.foldLeft ys (List.foldLeft xs z f) f
  | Nil, z, ys, f => rfl
  | Cons x xs, z, ys, f => List.foldLeftAppend xs (f z x) ys f

-- Appending and taking; sums of `Nat.keepIf` terms, which pick out some
-- elements; swapping two sums; sums and `any` over a run `s .. s + c` that
-- pick nothing or exactly one element.
theorem List.appendNil: (xs: List a) → List.append xs Nil = xs
  | Nil => rfl
  | Cons x xs => Eq.cong (Cons x) (List.appendNil xs)

theorem List.appendAssoc: (xs: List a) → (ys: List a) → (zs: List a) → List.append (List.append xs ys) zs = List.append xs (List.append ys zs)
  | Nil, ys, zs => rfl
  | Cons x xs, ys, zs => Eq.cong (Cons x) (List.appendAssoc xs ys zs)

-- `List.count` is a fold with an accumulator; `List.occurrences` recurses on
-- the list, which suits proofs. They agree, so the lemmas below are stated
-- for `List.count` (the program's) and proved through `List.occurrences`.
-- Also here: counting and `List.scanLeft` over `++`, and permutations.

-- Rearranging sums, for the counting lemmas below.
theorem Nat.addRotate (a: Nat) (b: Nat) (c: Nat): (a + b) + c = b + (a + c) := Eq.trans (Eq.cong (t => t + c) (Nat.addComm a b)) (Nat.addAssoc b a c)

theorem Nat.addLeftComm (a: Nat) (b: Nat) (c: Nat): a + (b + c) = b + (a + c) := Eq.trans (Eq.sym (Nat.addAssoc a b c)) (Nat.addRotate a b c)

theorem List.countStep: (b: Bool) → (k: Nat) → (o: Nat) → Nat.succIf k b + o = k + (Bool.toNat b + o)
  | True, k, o => Eq.sym (Nat.addSucc k o)
  | False, k, o => rfl

theorem List.countFold: (xs: List a) → (k: Nat) → (p: a → Bool) →
    List.foldLeft xs k (n x => Nat.succIf n (p x)) = k + List.occurrences xs p
  | Nil, k, p => Eq.sym (Nat.addZero k)
  | Cons x xs, k, p => Eq.trans (List.countFold xs (Nat.succIf k (p x)) p) (List.countStep (p x) k (List.occurrences xs p))

theorem List.countOccurrences (xs: List a) (p: a → Bool): List.count xs p = List.occurrences xs p := List.countFold xs 0 p

theorem List.occurrencesSumBy: (xs: List a) → (p: a → Bool) → List.occurrences xs p = List.sumBy xs (x => Bool.toNat (p x))
  | Nil, p => rfl
  | Cons x xs, p => rewrite List.sumByCons xs x (x => Bool.toNat (p x)), List.occurrencesSumBy xs p

-- A count is a sum of 1s and 0s, so the sum lemmas apply to it.
theorem List.countSumBy (xs: List a) (p: a → Bool): List.count xs p = List.sumBy xs (x => Bool.toNat (p x)) :=
  Eq.trans (List.countOccurrences xs p) (List.occurrencesSumBy xs p)

theorem List.occurrencesAppend: (xs: List a) → (ys: List a) → (p: a → Bool) →
    List.occurrences (List.append xs ys) p = List.occurrences xs p + List.occurrences ys p
  | Nil, ys, p => rfl
  | Cons x xs, ys, p =>
    Eq.trans (Eq.cong (t => Bool.toNat (p x) + t) (List.occurrencesAppend xs ys p))
      (Eq.sym (Nat.addAssoc (Bool.toNat (p x)) (List.occurrences xs p) (List.occurrences ys p)))

theorem List.countNil (p: a → Bool): List.count Nil p = 0 := rfl

theorem List.countCons (xs: List a) (x: a) (p: a → Bool): List.count (Cons x xs) p = Bool.toNat (p x) + List.count xs p :=
  Eq.trans (List.countOccurrences (Cons x xs) p) (Eq.cong (n => Bool.toNat (p x) + n) (Eq.sym (List.countOccurrences xs p)))

theorem List.countAppend (xs: List a) (ys: List a) (p: a → Bool): List.count (List.append xs ys) p = List.count xs p + List.count ys p :=
  Eq.trans (List.countOccurrences (List.append xs ys) p)
    (Eq.trans (List.occurrencesAppend xs ys p)
      (Eq.trans (Eq.cong (n => n + List.occurrences ys p) (Eq.sym (List.countOccurrences xs p)))
        (Eq.cong (n => List.count xs p + n) (Eq.sym (List.countOccurrences ys p)))))

-- The length of a `filter` is the `count` with the same test.
theorem List.lengthFilter: (xs: List a) → (p: a → Bool) → List.length (List.filter xs p) = List.count xs p
  | Nil, p => rfl
  | Cons x rest, p =>
    rewrite List.countCons rest x p, <- List.lengthFilter rest p in
      match keep: p x with
        | True => rfl
        | False => rfl

theorem List.countFalse: (xs: List a) → List.count xs (x => False) = 0
  | Nil => rfl
  | Cons x rest => List.countFalse rest

-- A count where no element passes is 0.
theorem List.countNone: (xs: List a) → (p: a → Bool) → ((x: a) → x ∈ xs → p x = False) → List.count xs p = 0
  | Nil, p, none => rfl
  | Cons x rest, p, none =>
    rewrite List.countCons rest x p, none x (Inl rfl), List.countNone rest p (y member => none y (Inr member)) in rfl

theorem List.anyEmpty: (xs: List a) → (p: a → Bool) → List.length xs = 0 → List.any xs p = False
  | Nil, p, empty => rfl
  | Cons x rest, p, empty => Void.exfalso (Nat.succNotZero (List.length rest) empty)

-- The length of a `flatMap` is the sum of the lengths of the lists it joins.
theorem List.lengthFlatMap (f: a → List b): (xs: List a) → List.length (List.flatMap xs f) = List.sumBy xs (x => List.length (f x))
  | Nil => rfl
  | Cons x rest =>
    rewrite List.sumByCons rest x (x => List.length (f x)), <- List.lengthFlatMap f rest in
      List.lengthAppend (f x) (List.flatMap rest f)

theorem List.lengthFlatMapExample: List.length (List.flatMap [1, 2, 3] (n => List.replicate n n)) = 6 := rfl

-- Counting over a `flatMap` adds up the counts over each list it joins.
theorem List.countFlatMap (f: a → List b) (p: b → Bool): (xs: List a) →
    List.count (List.flatMap xs f) p = List.sumBy xs (x => List.count (f x) p)
  | Nil => rfl
  | Cons x rest =>
    rewrite List.countAppend (f x) (List.flatMap rest f) p, List.sumByCons rest x (x => List.count (f x) p), List.countFlatMap f p rest
      in rfl

-- Dropping a list's start leaves what was appended to it.
theorem List.dropAppend: (start: List a) → (rest: List a) → List.drop (List.append start rest) (List.length start) = rest
  | Nil, rest => rfl
  | Cons x xs, rest => List.dropAppend xs rest

-- A list starts with what was appended to.
theorem List.startsWithAppend [auto eq: DecEq a]: (prefix: List a) → (rest: List a) → List.startsWith (List.append prefix rest) prefix = True
  | Nil, rest => rfl
  | Cons p ps, rest => rewrite DecEq.refl p, List.startsWithAppend ps rest in rfl

-- A list that starts with `prefix` is `prefix`, then the rest of it.
theorem List.startsWithSplit [auto eq: DecEq a]: (xs: List a) → (prefix: List a) → List.startsWith xs prefix = True →
    List.append prefix (List.drop xs (List.length prefix)) = xs
  | xs, Nil, starts => rfl
  | Nil, Cons p ps, starts => Void.exfalso (Bool.falseNotTrue starts)
  | Cons x xs, Cons p ps, starts =>
    rewrite DecEq.sound x p (Bool.andLeft _ _ starts), List.startsWithSplit xs ps (Bool.andRight _ _ starts) in rfl

-- A prefix is no longer than the list.
theorem List.startsWithLength [auto eq: DecEq a]: (xs: List a) → (prefix: List a) → List.startsWith xs prefix = True →
    List.length prefix ≤ List.length xs
  | xs, Nil, starts => rfl
  | Nil, Cons p ps, starts => Void.exfalso (Bool.falseNotTrue starts)
  | Cons x xs, Cons p ps, starts => List.startsWithLength xs ps (Bool.andRight _ _ starts)

-- Appending to `prefix` gives `xs` exactly when the appended list is the
-- rest of `xs`, once `xs` starts with `prefix`.
theorem List.appendEqDrop [auto eq: DecEq a] (xs: List a) (prefix: List a) (starts: List.startsWith xs prefix = True) (rest: List a):
    (List.append prefix rest == xs) = (rest == List.drop xs (List.length prefix)) :=
  match same: rest == List.drop xs (List.length prefix) with
    | True => rewrite DecEq.sound rest (List.drop xs (List.length prefix)) same, List.startsWithSplit xs prefix starts in DecEq.refl xs
    | False =>
      match made: List.append prefix rest == xs with
        | True =>
          let dropped := Eq.trans (Eq.sym (List.dropAppend prefix rest)) (Eq.cong (ys => List.drop ys (List.length prefix)) (DecEq.sound _ _ made))
          Void.exfalso (DecEq.soundFalse rest (List.drop xs (List.length prefix)) same dropped)
        | False => rfl

-- Nothing appended to `prefix` gives a list that doesn't start with it.
theorem List.appendNotEq [auto eq: DecEq a] (xs: List a) (prefix: List a) (starts: List.startsWith xs prefix = False) (rest: List a):
    (List.append prefix rest == xs) = False :=
  match made: List.append prefix rest == xs with
    | True =>
      let startsAfter: List.startsWith xs prefix = True := rewrite <- DecEq.sound _ _ made in List.startsWithAppend prefix rest
      Void.exfalso (Bool.falseNotTrue (Eq.trans (Eq.sym starts) startsAfter))
    | False => rfl

-- Stripping what was appended to gives the rest.
theorem List.stripPrefixAppend [auto eq: DecEq a]: (prefix: List a) → (rest: List a) → List.stripPrefix (List.append prefix rest) prefix = Some rest
  | Nil, rest => rfl
  | Cons p ps, rest => rewrite DecEq.refl p in List.stripPrefixAppend ps rest

-- `stripPrefix` is `startsWith`, then `drop`.
theorem List.stripPrefixStartsWith [auto eq: DecEq a]: (xs: List a) → (prefix: List a) →
    List.stripPrefix xs prefix = (if List.startsWith xs prefix then Some (List.drop xs (List.length prefix)) else None)
  | xs, Nil => rfl
  | Nil, Cons p ps => rfl
  | Cons x xs, Cons p ps =>
    match same: x == p with
      | True => List.stripPrefixStartsWith xs ps
      | False => rfl

-- `isEmpty` is `== []`.
theorem List.isEmptyEqNil [auto eq: DecEq a]: (xs: List a) → List.isEmpty xs = (xs == Nil)
  | Nil => rfl
  | Cons x xs => rfl

-- What passes a test after a `flatMap`: what passes in each list it joins,
-- added up.
theorem List.occurrencesFlatMap (f: a → List b) (p: b → Bool): (xs: List a) →
    List.occurrences (List.flatMap xs f) p = List.sumBy xs (x => List.occurrences (f x) p)
  | Nil => rfl
  | Cons x rest =>
    rewrite List.occurrencesAppend (f x) (List.flatMap rest f) p, List.occurrencesFlatMap f p rest,
      List.sumByCons rest x (x => List.occurrences (f x) p)
      in rfl

-- Summing 1 for each element counts them.
theorem List.sumByOne: (xs: List a) → List.sumBy xs (x => 1) = List.length xs
  | Nil => rfl
  | Cons x rest => rewrite List.sumByCons rest x (x => 1) in Eq.cong Succ (List.sumByOne rest)

-- Sums agree when their terms agree on the list's elements.
theorem List.sumByCongMem [auto add: Add b]: (xs: List a) → (f: a → b) → (g: a → b) → ((x: a) → x ∈ xs → f x = g x) →
    List.sumBy xs f = List.sumBy xs g
  | Nil, f, g, agree => rfl
  | Cons x rest, f, g, agree =>
    rewrite List.sumByCons rest x f, List.sumByCons rest x g, agree x (Inl rfl), List.sumByCongMem rest f g (y member => agree y (Inr member))
      in rfl

-- An element's term is at most the sum.
theorem List.memLeSumBy (f: a → Nat): (xs: List a) → (x: a) → x ∈ xs → f x ≤ List.sumBy xs f
  | Nil, x, none => Void.exfalso none
  | Cons first rest, x, Inl same => rewrite List.sumByCons rest first f, same in Nat.leAddRight (f x) (List.sumBy rest f)
  | Cons first rest, x, Inr later =>
    rewrite List.sumByCons rest first f in
      Nat.leTrans _ _ _ (List.memLeSumBy f rest x later) (Nat.leAddLeft (f first) (List.sumBy rest f))

test "List.sumByOne" := List.sumBy ["a", "b", "c"] (x => 1) == 3

theorem List.scanLeftCons: (xs: List a) → (z: b) → (f: b → a → b) → List.scanLeft xs z f = Cons z (List.drop (List.scanLeft xs z f) 1)
  | Nil, z, f => rfl
  | Cons x xs, z, f => rfl

theorem List.scanLeftAppend: (xs: List a) → (z: b) → (ys: List a) → (f: b → a → b) →
    List.drop (List.scanLeft (List.append xs ys) z f) 1 = List.append (List.drop (List.scanLeft xs z f) 1) (List.drop (List.scanLeft ys (List.foldLeft xs z f) f) 1)
  | Nil, z, ys, f => rfl
  | Cons x xs, z, ys, f =>
    Eq.trans (List.scanLeftCons (List.append xs ys) (f z x) f)
      (Eq.trans (Eq.cong (Cons (f z x)) (List.scanLeftAppend xs (f z x) ys f))
        (Eq.cong (l => List.append l (List.drop (List.scanLeft ys (List.foldLeft xs (f z x) f) f) 1)) (Eq.sym (List.scanLeftCons xs (f z x) f))))

theorem List.permRefl (xs: List a): List.Perm xs xs := p => rfl

theorem List.permSym (xs: List a) (ys: List a) (h: List.Perm xs ys): List.Perm ys xs := p => Eq.sym (h p)

theorem List.permTrans (xs: List a) (ys: List a) (zs: List a) (h1: List.Perm xs ys) (h2: List.Perm ys zs): List.Perm xs zs := p => Eq.trans (h1 p) (h2 p)

theorem List.occurrencesTrue: (xs: List a) → List.occurrences xs (x => True) = List.length xs
  | Nil => rfl
  | Cons x xs => Eq.cong Succ (List.occurrencesTrue xs)

theorem List.permLength (xs: List a) (ys: List a) (h: List.Perm xs ys): List.length xs = List.length ys := Eq.trans (Eq.sym (List.occurrencesTrue xs)) (Eq.trans (h (x => True)) (List.occurrencesTrue ys))

-- Some element passes `p` exactly when at least one does, so permutations
-- agree on `any`.
theorem List.anyOccurrences: (xs: List a) → (p: a → Bool) → List.any xs p = Nat.leq 1 (List.occurrences xs p)
  | Nil, p => rfl
  | Cons x xs, p =>
    Bool.inspect (p x) (c => Bool.ifThenElse c (u => True) (u => List.any xs p) = Nat.leq 1 (Bool.toNat c + List.occurrences xs p))
      (t => rfl) (f => List.anyOccurrences xs p)

theorem List.anyPerm (xs: List a) (ys: List a) (h: List.Perm xs ys) (p: a → Bool): List.any xs p = List.any ys p :=
  Eq.trans (List.anyOccurrences xs p) (Eq.trans (Eq.cong (n => Nat.leq 1 n) (h p)) (Eq.sym (List.anyOccurrences ys p)))

-- Reversing is a permutation, and keeps sums.
theorem List.occurrencesReverseOnto: (xs: List a) → (acc: List a) → (p: a → Bool) →
    List.occurrences (List.reverseOnto xs acc) p = List.occurrences xs p + List.occurrences acc p
  | Nil, acc, p => rfl
  | Cons x xs, acc, p =>
    Eq.trans (List.occurrencesReverseOnto xs (Cons x acc) p)
      (Eq.trans (Nat.addLeftComm (List.occurrences xs p) (Bool.toNat (p x)) (List.occurrences acc p))
        (Eq.sym (Nat.addAssoc (Bool.toNat (p x)) (List.occurrences xs p) (List.occurrences acc p))))

theorem List.reversePerm (xs: List a): List.Perm (List.reverse xs) xs := p =>
  Eq.trans (List.occurrencesReverseOnto xs Nil p) (Nat.addZero (List.occurrences xs p))

theorem List.sumByReverseOnto: (xs: List a) → (acc: List a) → (f: a → Nat) →
    List.sumBy (List.reverseOnto xs acc) f = List.sumBy xs f + List.sumBy acc f
  | Nil, acc, f => rfl
  | Cons x xs, acc, f =>
    Eq.trans (List.sumByReverseOnto xs (Cons x acc) f)
      (Eq.trans (Eq.cong (t => List.sumBy xs f + t) (List.sumByCons acc x f))
        (Eq.trans (Nat.addLeftComm (List.sumBy xs f) (f x) (List.sumBy acc f))
          (Eq.trans (Eq.sym (Nat.addAssoc (f x) (List.sumBy xs f) (List.sumBy acc f)))
            (Eq.cong (t => t + List.sumBy acc f) (Eq.sym (List.sumByCons xs x f))))))

theorem List.sumByReverse (xs: List a) (f: a → Nat): List.sumBy (List.reverse xs) f = List.sumBy xs f :=
  Eq.trans (List.sumByReverseOnto xs Nil f) (Nat.addZero (List.sumBy xs f))

-- Counting with a test nothing passes, and with either of two tests.
theorem List.occurrencesNone: (xs: List a) → (p: a → Bool) → (h: (x: a) → p x = False) → List.occurrences xs p = 0
  | Nil, p, h => rfl
  | Cons x xs, p, h => Eq.trans (Eq.cong (b => Bool.toNat b + List.occurrences xs p) (h x)) (List.occurrencesNone xs p h)

-- When nothing passes both `p` and `q`, the elements passing either are those
-- passing `p` plus those passing `q`.
theorem List.occurrencesOr: (xs: List a) → (p: a → Bool) → (q: a → Bool) → (h: (x: a) → p x = True → q x = False) →
    List.occurrences xs (x => p x ∨ q x) = List.occurrences xs p + List.occurrences xs q
  | Nil, p, q, h => rfl
  | Cons x xs, p, q, h =>
    Bool.inspect (p x)
      (c => Bool.toNat (c ∨ q x) + List.occurrences xs (x => p x ∨ q x)
        = (Bool.toNat c + List.occurrences xs p) + (Bool.toNat (q x) + List.occurrences xs q))
      (t => Eq.trans (Eq.cong (n => 1 + n) (List.occurrencesOr xs p q h))
        (Eq.cong (b => (1 + List.occurrences xs p) + (Bool.toNat b + List.occurrences xs q)) (Eq.sym (h x t))))
      (f => Eq.trans (Eq.cong (n => Bool.toNat (q x) + n) (List.occurrencesOr xs p q h))
        (Nat.addLeftComm (Bool.toNat (q x)) (List.occurrences xs p) (List.occurrences xs q)))

-- Lemmas for proofs about grids: runs' lengths, `map` and `filterMap` fused,
-- `init`, `last` and `reverse` of a `map`, and transposing a grid given cell
-- by cell.
theorem List.lengthRangeFrom: (n: Nat) → (s: Nat) → List.length (List.rangeFrom n s) = n
  | Zero, s => rfl
  | Succ n, s => rewrite List.lengthRangeFrom n (Succ s)

theorem List.mapMap: (xs: List a) → (f: b → c) → (g: a → b) → List.map (List.map xs g) f = List.map xs (x => f (g x))
  | Nil, f, g => rfl
  | Cons x xs, f, g => rewrite List.mapMap xs f g

theorem List.filterMapMap: (xs: List a) → (f: b → Option c) → (g: a → b) → List.filterMap (List.map xs g) f = List.filterMap xs (x => f (g x))
  | Nil, f, g => rfl
  | Cons x xs, f, g => rewrite List.filterMapMap xs f g

theorem List.filterMapSome: (xs: List a) → (f: a → b) → List.filterMap xs (x => Some (f x)) = List.map xs f
  | Nil, f => rfl
  | Cons x xs, f => rewrite List.filterMapSome xs f

theorem List.filterMapAppend: (xs: List a) → (ys: List a) → (f: a → Option b) →
    List.filterMap (List.append xs ys) f = List.append (List.filterMap xs f) (List.filterMap ys f)
  | Nil, ys, f => rfl
  | Cons x xs, ys, f =>
    match f x with
      | None => List.filterMapAppend xs ys f
      | Some y => rewrite List.filterMapAppend xs ys f

theorem List.initMap: (xs: List a) → (f: a → b) → List.init (List.map xs f) = List.map (List.init xs) f
  | Nil, f => rfl
  | Cons x Nil, f => rfl
  | Cons x (Cons y ys), f => rewrite List.initMap (Cons y ys) f

theorem List.lastMap: (xs: List a) → (f: a → b) → List.last (List.map xs f) = Option.map (List.last xs) f
  | Nil, f => rfl
  | Cons x Nil, f => rfl
  | Cons x (Cons y ys), f => List.lastMap (Cons y ys) f
theorem List.mapRangeShift (f: Nat → b): (n: Nat) → (s: Nat) →
    List.map (List.rangeFrom n (Succ s)) f = List.map (List.rangeFrom n s) (i => f (Succ i))
  | Zero, s => rfl
  | Succ n, s => rewrite List.mapRangeShift f n (Succ s)

-- Transposing a grid given cell by cell: row x, column y becomes row y, column x.
theorem List.transposeNGrid (rows: List a): (cols: List b) → (cell: a → b → c) →
    List.transposeN (List.length cols) (List.map rows (x => List.map cols (cell x))) = List.map cols (y => List.map rows (x => cell x y))
  | Nil, cell => rfl
  | Cons y cols, cell =>
    calc List.transposeN (Succ (List.length cols)) (List.map rows (x => List.map (Cons y cols) (cell x)))
      _ = Cons (List.filterMap (List.map rows (x => List.map (Cons y cols) (cell x))) (.get 0))
        (List.transposeN (List.length cols) (List.map (List.map rows (x => List.map (Cons y cols) (cell x))) (.drop 1)))
      _ = Cons (List.filterMap rows (x => Some (cell x y))) (List.transposeN (List.length cols) (List.map rows (x => List.map cols (cell x))))
        := rewrite List.filterMapMap rows (.get 0) (x => List.map (Cons y cols) (cell x)),
          List.mapMap rows (.drop 1) (x => List.map (Cons y cols) (cell x))
      _ = Cons (List.map rows (x => cell x y)) (List.map cols (z => List.map rows (x => cell x z)))
        := rewrite List.filterMapSome rows (x => cell x y), List.transposeNGrid rows cols cell

theorem List.transposeGrid (rows: List a) (r: a) (cols: List b) (cell: a → b → c):
    List.transpose (List.map (Cons r rows) (x => List.map cols (cell x))) = List.map cols (y => List.map (Cons r rows) (x => cell x y)) :=
  calc List.transpose (List.map (Cons r rows) (x => List.map cols (cell x)))
    _ = List.transposeN (List.length (List.map cols (cell r))) (List.map (Cons r rows) (x => List.map cols (cell x)))
    _ = List.transposeN (List.length cols) (List.map (Cons r rows) (x => List.map cols (cell x))) := rewrite List.lengthMap cols (cell r)
    _ = List.map cols (y => List.map (Cons r rows) (x => cell x y)) := List.transposeNGrid (Cons r rows) cols cell

theorem List.mapReverseOnto: (xs: List a) → (acc: List a) → (f: a → b) →
    List.map (List.reverseOnto xs acc) f = List.reverseOnto (List.map xs f) (List.map acc f)
  | Nil, acc, f => rfl
  | Cons x xs, acc, f => List.mapReverseOnto xs (Cons x acc) f

theorem List.mapReverse (xs: List a) (f: a → b): List.map (List.reverse xs) f = List.reverse (List.map xs f) := List.mapReverseOnto xs Nil f

-- Reversing onto `acc`, then reversing that, is `acc` reversed onto the list.
theorem List.reverseOntoTwice: (xs: List a) → (acc: List a) → List.reverseOnto (List.reverseOnto xs acc) Nil = List.reverseOnto acc xs
  | Nil, acc => rfl
  | Cons x xs, acc => List.reverseOntoTwice xs (Cons x acc)

-- Reversing twice gives the list back.
theorem List.reverseReverse (xs: List a): List.reverse (List.reverse xs) = xs := List.reverseOntoTwice xs Nil

-- Reversing onto `acc` is reversing, then appending `acc`.
theorem List.reverseOntoAppend: (xs: List a) → (acc: List a) → List.reverseOnto xs acc = List.append (List.reverseOnto xs Nil) acc
  | Nil, acc => rfl
  | Cons x xs, acc =>
    rewrite List.reverseOntoAppend xs (Cons x acc), List.reverseOntoAppend xs [x]
      in Eq.sym (List.appendAssoc (List.reverseOnto xs Nil) [x] acc)

-- Reversing a list puts its first element last.
theorem List.reverseCons (x: a) (xs: List a): List.reverse (Cons x xs) = List.append (List.reverse xs) [x] := List.reverseOntoAppend xs [x]

-- Reversing a list puts its last element first.
theorem List.reverseSnoc: (xs: List a) → (x: a) → List.reverse (List.append xs [x]) = Cons x (List.reverse xs)
  | Nil, x => rfl
  | Cons y rest, x =>
    rewrite List.reverseCons y (List.append rest [x]), List.reverseSnoc rest x, List.reverseCons y rest in rfl

theorem List.lengthReverseOnto: (xs: List a) → (acc: List a) → List.length (List.reverseOnto xs acc) = List.length xs + List.length acc
  | Nil, acc => rfl
  | Cons x rest, acc => Eq.trans (List.lengthReverseOnto rest (Cons x acc)) (Nat.addSucc (List.length rest) (List.length acc))

theorem List.lengthReverse (xs: List a): List.length (List.reverse xs) = List.length xs :=
  Eq.trans (List.lengthReverseOnto xs Nil) (Nat.addZero (List.length xs))

theorem List.lengthSnoc: (xs: List a) → (x: a) → List.length (List.append xs [x]) = Succ (List.length xs)
  | Nil, x => rfl
  | Cons y rest, x => Eq.cong Succ (List.lengthSnoc rest x)

-- Counting in a `flatMap` over a list reversed onto `acc`.
theorem List.occurrencesFlatMapReverseOnto (f: a → List b) (p: b → Bool): (xs: List a) → (acc: List a) →
    List.occurrences (List.flatMap (List.reverseOnto xs acc) f) p =
      List.occurrences (List.flatMap xs f) p + List.occurrences (List.flatMap acc f) p
  | Nil, acc => rfl
  | Cons x rest, acc =>
    let here := List.occurrences (f x) p
    let before := List.occurrences (List.flatMap rest f) p
    let after := List.occurrences (List.flatMap acc f) p
    rewrite List.occurrencesFlatMapReverseOnto f p rest (Cons x acc), List.occurrencesAppend (f x) (List.flatMap acc f) p,
      List.occurrencesAppend (f x) (List.flatMap rest f) p
      in Eq.trans (Eq.sym (Nat.addAssoc before here after)) (Eq.cong (t => t + after) (Nat.addComm before here))

-- A `flatMap` over the list reversed has the same elements.
theorem List.permFlatMapReverse (f: a → List b) (xs: List a): List.Perm (List.flatMap (List.reverse xs) f) (List.flatMap xs f) :=
  p => Eq.trans (List.occurrencesFlatMapReverseOnto f p xs Nil) (Nat.addZero (List.occurrences (List.flatMap xs f) p))

-- Adding up the values there are is adding up every value, with 0 for none.
theorem List.sumFilterMap (f: a → Option Nat): (xs: List a) →
    List.sum (List.filterMap xs f) = List.sumBy xs (x => Option.getOrElse (f x) 0)
  | Nil => rfl
  | Cons x rest =>
    rewrite List.sumByCons rest x (y => Option.getOrElse (f y) 0), <- List.sumFilterMap f rest in
      match value: f x with
        | Some v => List.sumByCons (List.filterMap rest f) v (y => y)
        | None => rfl

theorem List.reverseReverseExample: List.reverse (List.reverse [1, 2, 3]) = [1, 2, 3] := List.reverseReverse [1, 2, 3]

-- A test every element passes holds for all of them.
theorem List.allTrue: (xs: List a) → (p: a → Bool) → ((x: a) → p x = True) → List.all xs p = True
  | Nil, p, h => rfl
  | Cons x xs, p, h => rewrite h x in List.allTrue xs p h

-- A test no element passes holds for none of them.
theorem List.anyFalse: (xs: List a) → (p: a → Bool) → ((x: a) → p x = False) → List.any xs p = False
  | Nil, p, h => rfl
  | Cons x xs, p, h => rewrite h x in List.anyFalse xs p h

-- Every element passes both tests when every element passes each.
theorem List.allAnd: (xs: List a) → (p: a → Bool) → (q: a → Bool) → List.all xs (x => p x ∧ q x) = (List.all xs p ∧ List.all xs q)
  | Nil, p, q => rfl
  | Cons x xs, p, q =>
    match px: p x, qx: q x with
      | True, True => List.allAnd xs p q
      | True, False => cases
      | False, qx => rfl

theorem Option.flatMapMap: (m: Option a) → (g: b → Option c) → (f: a → b) → Option.flatMap (Option.map m f) g = Option.flatMap m (x => g (f x))
  | None, g, f => rfl
  | Some x, g, f => rfl

theorem List.lengthZipWith3 (f: a → b → c → e): (xs: List a) → (ys: List b) → (zs: List c) →
    List.length ys = List.length xs → List.length zs = List.length xs → List.length (List.zipWith3 xs ys zs f) = List.length xs
  | Nil, ys, zs, h1, h2 => rfl
  | Cons x xs, Nil, zs, h1, h2 => Void.exfalso (Nat.zeroNotSucc (List.length xs) h1)
  | Cons x xs, Cons y ys, Nil, h1, h2 => Void.exfalso (Nat.zeroNotSucc (List.length xs) h2)
  | Cons x xs, Cons y ys, Cons z zs, h1, h2 =>
    rewrite List.lengthZipWith3 f xs ys zs (Nat.succInjective (List.length ys) (List.length xs) h1) (Nat.succInjective (List.length zs) (List.length xs) h2)

-- Lists zipped in step are no longer than the first.
theorem List.lengthZipWithLe (f: a → b → c): (xs: List a) → (ys: List b) → List.length (List.zipWith xs ys f) ≤ List.length xs
  | Nil, ys => rfl
  | Cons x xs, Nil => rfl
  | Cons x xs, Cons y ys => List.lengthZipWithLe f xs ys

theorem List.lengthZipWith3Le (f: a → b → c → d): (xs: List a) → (ys: List b) → (zs: List c) → List.length (List.zipWith3 xs ys zs f) ≤ List.length xs
  | Nil, ys, zs => rfl
  | Cons x xs, Nil, zs => rfl
  | Cons x xs, Cons y ys, Nil => rfl
  | Cons x xs, Cons y ys, Cons z zs => List.lengthZipWith3Le f xs ys zs

theorem List.lengthZipWith4Le (f: a → b → c → d → e): (xs: List a) → (ys: List b) → (zs: List c) → (ws: List d) →
    List.length (List.zipWith4 xs ys zs ws f) ≤ List.length xs
  | Nil, ys, zs, ws => rfl
  | Cons x xs, Nil, zs, ws => rfl
  | Cons x xs, Cons y ys, Nil, ws => rfl
  | Cons x xs, Cons y ys, Cons z zs, Nil => rfl
  | Cons x xs, Cons y ys, Cons z zs, Cons w ws => List.lengthZipWith4Le f xs ys zs ws

-- Zipping with an empty list in a later place gives nothing.
theorem List.zipWith3NilSecond (zs: List c) (f: a → b → c → d): (xs: List a) → List.zipWith3 xs Nil zs f = Nil
  | Nil => rfl
  | Cons x xs => rfl

theorem List.zipWith3NilThird (f: a → b → c → d): (xs: List a) → (ys: List b) → List.zipWith3 xs ys Nil f = Nil
  | Nil, ys => rfl
  | Cons x xs, Nil => rfl
  | Cons x xs, Cons y ys => rfl

theorem List.zipWith4NilSecond (zs: List c) (ws: List d) (f: a → b → c → d → e): (xs: List a) → List.zipWith4 xs Nil zs ws f = Nil
  | Nil => rfl
  | Cons x xs => rfl

theorem List.zipWith4NilThird (ws: List d) (f: a → b → c → d → e): (xs: List a) → (ys: List b) → List.zipWith4 xs ys Nil ws f = Nil
  | Nil, ys => rfl
  | Cons x xs, Nil => rfl
  | Cons x xs, Cons y ys => rfl

theorem List.zipWith4NilFourth (f: a → b → c → d → e): (xs: List a) → (ys: List b) → (zs: List c) → List.zipWith4 xs ys zs Nil f = Nil
  | Nil, ys, zs => rfl
  | Cons x xs, Nil, zs => rfl
  | Cons x xs, Cons y ys, Nil => rfl
  | Cons x xs, Cons y ys, Cons z zs => rfl

theorem List.distinctNil: List.Distinct (Nil: List a) := Trivial

theorem List.distinctCons (x: a) (xs: List a) (h: x ∉ xs) (d: List.Distinct xs): List.Distinct (Cons x xs) := Both h d

-- An element of two lists joined is in one of them.
theorem List.memAppend (x: a): (xs: List a) → (ys: List a) → x ∈ List.append xs ys → Or (x ∈ xs) (x ∈ ys)
  | Nil, ys, h => Inr h
  | Cons z zs, ys, Inl h => Inl (Inl h)
  | Cons z zs, ys, Inr h =>
    match List.memAppend x zs ys h with
      | Inl m => Inl (Inr m)
      | Inr m => Inr m

-- And back: an element of either list is in the two joined.
theorem List.memAppendLeft (x: a): (xs: List a) → (ys: List a) → x ∈ xs → x ∈ List.append xs ys
  | Nil, ys, m => Void.exfalso m
  | Cons z zs, ys, Inl e => Inl e
  | Cons z zs, ys, Inr m => Inr (List.memAppendLeft x zs ys m)

theorem List.memAppendRight (x: a): (xs: List a) → (ys: List a) → x ∈ ys → x ∈ List.append xs ys
  | Nil, ys, m => m
  | Cons z zs, ys, m => Inr (List.memAppendRight x zs ys m)

theorem List.memAppendExample: 3 ∈ List.append [1, 2] [3] := List.memAppendRight 3 [1, 2] [3] (Inl rfl)

-- `f x` is in `List.map xs f` only if `x` is in `xs`, for an injective `f`.
theorem List.memMapInjective (f: a → b) (inj: (x: a) → (y: a) → f x = f y → x = y) (x: a): (xs: List a) → f x ∈ List.map xs f → x ∈ xs
  | Nil, h => h
  | Cons z zs, Inl h => Inl (inj z x h)
  | Cons z zs, Inr h => Inr (List.memMapInjective f inj x zs h)

-- If `x` is in `xs`, `f x` is in `List.map xs f`.
theorem List.memMap: (xs: List a) → (x: a) → x ∈ xs → (f: a → b) → f x ∈ List.map xs f
  | Nil, x, h, f => h
  | Cons z zs, x, Inl h, f => Inl (Eq.cong f h)
  | Cons z zs, x, Inr h, f => Inr (List.memMap zs x h f)

-- Use "some element satisfies `p`": take that element, know it is in the
-- list, and carry on to the goal. (The library has no `Exists`.)
theorem List.anyElim (p: a → Prop) (goal: Prop): (xs: List a) → List.Any p xs → ((x: a) → x ∈ xs → p x → goal) → goal
  | Nil, h, k => Void.exfalso h
  | Cons z zs, Inl h, k => k z (Inl rfl) h
  | Cons z zs, Inr h, k => List.anyElim p goal zs h (x inZs px => k x (Inr inZs) px)

-- And to prove it: an element of the list that satisfies `p`. (For the
-- `Bool` `List.any`, `List.anyOfMem`.)
theorem List.anyIntro (p: a → Prop) (x: a): (xs: List a) → x ∈ xs → p x → List.Any p xs
  | Nil, m, px => Void.exfalso m
  | Cons z zs, Inl e, px => Inl (rewrite e in px)
  | Cons z zs, Inr m, px => Inr (List.anyIntro p x zs m px)

theorem List.anyIntroExample: List.Any (n => n > 2) [1, 2, 3] := List.anyIntro (n => n > 2) 3 [1, 2, 3] (Inr (Inr (Inl rfl))) rfl

-- What is in `List.map xs f` is `f x` for some `x` in `xs` (said with
-- `List.Any`, which also says where `x` is: `Exists` wouldn't).
theorem List.memMapAny: (xs: List a) → (f: a → b) → (y: b) → y ∈ List.map xs f → List.Any (x => f x = y) xs
  | Nil, f, y, h => h
  | Cons z zs, f, y, Inl h => Inl h
  | Cons z zs, f, y, Inr h => Inr (List.memMapAny zs f y h)

-- `List.Any` gives a member that satisfies `p`.
theorem List.anyMember (p: a → Prop): (xs: List a) → List.Any p xs → Exists a (x => And (x ∈ xs) (p x))
  | Nil, none => Void.exfalso none
  | Cons x rest, Inl here => Witness x (Both (Inl rfl) here)
  | Cons x rest, Inr later => Exists.elim (List.anyMember p rest later) (found both => Witness found (Both (Inr (And.left both)) (And.right both)))

-- A member of a mapped list is the image of a member.
theorem List.memMapElim (f: a → b) (y: b) (xs: List a) (member: y ∈ List.map xs f): Exists a (x => And (x ∈ xs) (f x = y)) :=
  List.anyMember (x => f x = y) xs (List.memMapAny xs f y member)

-- What `(.filter p)` keeps was in the list, and passes `p`.
theorem List.memFilter: (xs: List a) → (p: a → Bool) → (x: a) → x ∈ List.filter xs p → And (x ∈ xs) (p x = True)
  | Nil, p, x, h => Void.exfalso h
  | Cons y ys, p, x, h =>
    match e: p y with
      | True =>
        match h with
          | Inl q => Both (Inl q) (rewrite q at e)
          | Inr m =>
            match List.memFilter ys p x m with
              | Both inYs px => Both (Inr inYs) px
      | False =>
        match List.memFilter ys p x h with
          | Both inYs px => Both (Inr inYs) px

-- A `filter` that keeps nothing of the list is empty.
theorem List.filterNone (p: a → Bool): (xs: List a) → ((x: a) → x ∈ xs → p x = False) → List.filter xs p = Nil
  | Nil, h => rfl
  | Cons x xs, h => rewrite h x (Inl rfl) in List.filterNone p xs (y m => h y (Inr m))

-- A `filter` that keeps all of the list is the list.
theorem List.filterAll (p: a → Bool): (xs: List a) → ((x: a) → x ∈ xs → p x = True) → List.filter xs p = xs
  | Nil, h => rfl
  | Cons x xs, h => rewrite h x (Inl rfl) in Eq.cong (Cons x) (List.filterAll p xs (y m => h y (Inr m)))

-- No successor is zero, and every one is at least 1.
theorem List.filterNoneExample (xs: List Nat): List.filter (List.map xs Succ) (n => n == 0) = Nil :=
  List.filterNone (n => n == 0) (List.map xs Succ) (n m =>
    List.anyElim (x => Succ x = n) ((n == 0) = False) xs (List.memMapAny xs Succ n m) (x inXs e => rewrite <- e in rfl))

theorem List.filterAllExample (xs: List Nat): List.filter (List.map xs Succ) (n => Nat.leq 1 n) = List.map xs Succ :=
  List.filterAll (n => Nat.leq 1 n) (List.map xs Succ) (n m =>
    List.anyElim (x => Succ x = n) (Nat.leq 1 n = True) xs (List.memMapAny xs Succ n m) (x inXs e => rewrite <- e in rfl))

-- `List.between lo hi` holds the numbers from `lo` to `hi`, both included.
-- The numbers are implicit, for use on a `List.Member`'s `isIn`.
theorem List.memBetween [x lo hi: Nat] (h: x ∈ List.between lo hi): And (lo ≤ x) (x ≤ hi) :=
  match List.memRangeFrom x (hi + 1 - lo) lo h with
    | Both above below => Both above (Nat.ltCongRight x (hi + 1) (Succ hi) (Nat.addOne hi) (Nat.ltOfRunSub lo x (hi + 1) above below))

-- The other way: every number from `s` up to, not including, `s + c` is in
-- the run `List.rangeFrom c s`.
theorem List.memRangeFromIntro (x: Nat): (c: Nat) → (s: Nat) → s ≤ x → x < s + c → x ∈ List.rangeFrom c s
  | Zero, s, lo, hi => Void.exfalso (Nat.lessIrrefl x (Nat.leTrans (Succ x) s x (Nat.ltCongRight x (s + 0) s (Nat.addZero s) hi) lo))
  | Succ c, s, lo, hi =>
    match e: Nat.leq (Succ s) x with
      | True => Inr (List.memRangeFromIntro x c (Succ s) e (Nat.ltSuccAdd s c x hi))
      | False => Inl (Nat.leAntisym s x lo (Nat.leqFalse (Succ s) x e))

-- And for `List.between lo hi`: every number from `lo` to `hi`, both included.
theorem List.memBetweenIntro (x: Nat) (lo: Nat) (hi: Nat) (above: lo ≤ x) (below: x ≤ hi): x ∈ List.between lo hi :=
  List.memRangeFromIntro x (hi + 1 - lo) lo above
    (Nat.ltCongRight x (hi + 1) (lo + (hi + 1 - lo))
      (Eq.sym (Nat.addSubCancel lo (hi + 1) (Nat.leTrans lo x (hi + 1) above (Nat.leTrans x hi (hi + 1) below (Nat.leCongRight hi (Succ hi) (hi + 1) (Eq.sym (Nat.addOne hi)) (Nat.leSucc hi))))))
      (Nat.ltCongRight x (Succ hi) (hi + 1) (Eq.sym (Nat.addOne hi)) (Nat.leLessSucc x hi below)))

-- A list's `flatMap`: an element of `f x` for an `x` of the list is in it.
theorem List.memFlatMapIntro (f: a → List b) (x: a) (y: b): (xs: List a) → x ∈ xs → y ∈ f x → y ∈ List.flatMap xs f
  | Nil, h, m => Void.exfalso h
  | Cons z zs, Inl h, m => List.anyAppendLeft (w => w = y) (f z) (List.concat (List.map zs f)) (rewrite h in m)
  | Cons z zs, Inr h, m => List.anyAppendRight (w => w = y) (f z) (List.concat (List.map zs f)) (List.memFlatMapIntro f x y zs h m)

-- And back: what is in a `flatMap` is in `f x` for some `x` of the list.
theorem List.memFlatMapElim (f: a → List b) (y: b): (xs: List a) → y ∈ List.flatMap xs f → List.Any (x => y ∈ f x) xs
  | Nil, h => h
  | Cons z zs, h =>
    match List.memAppend y (f z) (List.concat (List.map zs f)) h with
      | Inl m => Inl m
      | Inr m => Inr (List.memFlatMapElim f y zs m)

-- Mapping an injective function keeps a list distinct.
theorem List.distinctMap: (xs: List a) → List.Distinct xs → (f: a → b) → (inj: (x: a) → (y: a) → f x = f y → x = y) → List.Distinct (List.map xs f)
  | Nil, d, f, inj => Trivial
  | Cons x xs, Both h d, f, inj => Both (m => h (List.memMapInjective f inj x xs m)) (List.distinctMap xs d f inj)

-- Two distinct lists with no element in common, joined, are distinct.
theorem List.distinctAppend: (xs: List a) → (ys: List a) → List.Distinct xs → List.Distinct ys → List.Disjoint xs ys → List.Distinct (List.append xs ys)
  | Nil, ys, dx, dy, dj => dy
  | Cons x xs, ys, Both hx dx, dy, Both hj dj =>
    Both
      (m => match List.memAppend x xs ys m with
        | Inl inXs => hx inXs
        | Inr inYs => hj inYs)
      (List.distinctAppend xs ys dx dy dj)

-- The same head in front of two lists gives the same list only if the tails
-- were the same.
theorem List.consInjective (x: a) (ys: List a) (zs: List a) (p: Cons x ys = Cons x zs): ys = zs := Eq.cong (.drop 1) p

-- A list starting with x isn't among lists that all start with y, a
-- different element.
theorem List.notMemMapCons (x: a) (y: a) (ne: Not (x = y)) (xs: List a): (ys: List (List a)) → Cons x xs ∉ List.map ys (Cons y)
  | Nil, m => m
  | Cons z zs, Inl p => ne (Eq.sym (Eq.cong (.headOr x) p))
  | Cons z zs, Inr q => List.notMemMapCons x y ne xs zs q

-- Lists that all start with x and lists that all start with a different y
-- have none in common.
theorem List.disjointMapCons (ys: List (List a)) (x: a) (y: a) (ne: Not (x = y)): (xs: List (List a)) →
    List.Disjoint (List.map xs (Cons x)) (List.map ys (Cons y))
  | Nil => Trivial
  | Cons z zs => Both (List.notMemMapCons x y ne z ys) (List.disjointMapCons ys x y ne zs)

-- A run of numbers has no repeats.
theorem List.distinctRangeFrom: (c: Nat) → (s: Nat) → List.Distinct (List.rangeFrom c s)
  | Zero, s => Trivial
  | Succ c, s =>
    Both (m => match List.memRangeFrom s c (Succ s) m with
        | Both above _ => Nat.lessIrrefl s above)
      (List.distinctRangeFrom c (Succ s))

theorem List.distinctBetween (lo: Nat) (hi: Nat): List.Distinct (List.between lo hi) := List.distinctRangeFrom (hi + 1 - lo) lo

-- Every element of the list passes, given that each element that is in it does.
theorem List.allOfMem (p: a → Prop): (xs: List a) → ((x: a) → x ∈ xs → p x) → List.All p xs
  | Nil, h => Trivial
  | Cons z zs, h => Both (h z (Inl rfl)) (List.allOfMem p zs (x inZs => h x (Inr inZs)))

-- A `flatMap` of distinct lists has no repeats if the list mapped over has none
-- and the lists apart: `key` says which element of `xs` each result came from.
theorem List.distinctFlatMap (f: a → List b) (key: b → a): (xs: List a) → List.Distinct xs →
    ((x: a) → x ∈ xs → List.Distinct (f x)) →
    ((x: a) → x ∈ xs → (y: b) → y ∈ f x → key y = x) →
    List.Distinct (List.flatMap xs f)
  | Nil, d, distinctEach, keyed => Trivial
  | Cons x xs, Both notLater later, distinctEach, keyed =>
    List.distinctAppend (f x) (List.flatMap xs f)
      (distinctEach x (Inl rfl))
      (List.distinctFlatMap f key xs later (z inXs => distinctEach z (Inr inXs)) (z inXs => keyed z (Inr inXs)))
      -- Nothing in `f x` is in a later `f z`: it would have key `x` and key `z`.
      (List.allOfMem (y => y ∉ List.flatMap xs f) (f x) (y fromX inLater =>
        List.anyElim (z => y ∈ f z) Void xs (List.memFlatMapElim f y xs inLater)
          (z inXs fromZ =>
            notLater (rewrite Eq.trans (Eq.sym (keyed x (Inl rfl) y fromX)) (keyed z (Inr inXs) y fromZ) in inXs))))

theorem List.distinctExample: List.Distinct [1, 2] :=
  Both (m => match m with
      | Inl p => Nat.succNotZero 0 (Nat.succInjective 1 0 p)
      | Inr v => v)
    (Both (m => m) Trivial)

theorem List.distinctMapExample: List.Distinct (List.map [1, 2] Succ) :=
  List.distinctMap [1, 2] List.distinctExample Succ (x y p => Nat.succInjective x y p)

theorem List.consInjectiveExample (ys: List Nat) (zs: List Nat) (p: Cons 1 ys = Cons 1 zs): ys = zs := List.consInjective 1 ys zs p

theorem List.disjointMapConsExample: List.Disjoint (List.map [[1], [2]] (Cons 0)) (List.map [[1], Nil] (Cons 1)) :=
  List.disjointMapCons [[1], Nil] 0 1 (p => Nat.succNotZero 0 (Eq.sym p)) [[1], [2]]

theorem List.distinctMapConsExample: List.Distinct (List.append (List.map [Nil] (Cons 0)) (List.map [Nil] (Cons 1))) :=
  List.distinctAppend (List.map [Nil] (Cons 0)) (List.map [Nil] (Cons 1))
    (List.distinctMap [Nil] (Both (m => m) Trivial) (Cons 0) (List.consInjective 0))
    (List.distinctMap [Nil] (Both (m => m) Trivial) (Cons 1) (List.consInjective 1))
    (List.disjointMapCons [Nil] 0 1 (p => Nat.succNotZero 0 (Eq.sym p)) [Nil])

theorem List.memBetweenIntroExample: 3 ∈ List.between 1 5 := List.memBetweenIntro 3 1 5 rfl rfl

theorem List.memFlatMapExample: 20 ∈ List.flatMap [1, 2] (x => [x, x * 10]) :=
  List.memFlatMapIntro (x => [x, x * 10]) 2 20 [1, 2] (Inr (Inl rfl)) (Inr (Inl rfl))

theorem List.distinctAppendExample: List.Distinct (List.append [1] [2]) :=
  List.distinctAppend [1] [2]
    (Both (m => m) Trivial)
    (Both (m => m) Trivial)
    (Both (m => match m with
      | Inl p => Nat.succNotZero 0 (Nat.succInjective 1 0 p)
      | Inr v => v) Trivial)

-- What `List.All` says of an element of the list.
theorem List.allMem (p: a → Prop) (x: a): (xs: List a) → List.All p xs → x ∈ xs → p x
  | Nil, h, m => Void.exfalso m
  | Cons z zs, Both pz h, Inl e => rewrite <- e in pz
  | Cons z zs, Both pz h, Inr m => List.allMem p x zs h m

-- `List.find` and `List.any`, and keys that are distinct (SW-363): lemmas
-- for code that finds records by an id.

-- What `List.find` finds passes the test and is in the list.
theorem List.findSome: (xs: List a) → (p: a → Bool) → (y: a) → List.find xs p = Some y → And (p y = True) (y ∈ xs)
  | Nil, p, y, h => Void.exfalso (Option.noneNotSome y h)
  | Cons x xs, p, y, h =>
    match e: p x with
      | True => Both (Eq.trans (Eq.cong p (Eq.sym (Option.someInjective x y h))) e) (Inl (Option.someInjective x y h))
      | False =>
        match List.findSome xs p y h with
          | Both py m => Both py (Inr m)

-- `List.find` finds nothing only when no element passes.
theorem List.findNoneNotMem: (xs: List a) → (p: a → Bool) → (x: a) → (px: p x = True) → x ∈ xs → List.find xs p = None → Void
  | Nil, p, x, px, m, h => m
  | Cons z zs, p, x, px, Inl e, h => Option.someNotNone x (rewrite e, px at h)
  | Cons z zs, p, x, px, Inr m, h =>
    match c: p z with
      | True => Option.someNotNone z h
      | False => List.findNoneNotMem zs p x px m h

-- `List.find` over `List.range`: what it finds is the least number that
-- passes, and when it finds nothing, no number in the range passes.

-- No number from `start` up to the one found passes.
theorem List.findRangeFirst (passes: Nat → Bool): (count: Nat) → (start: Nat) → (found: Nat) →
    (List.rangeFrom count start).find passes = Some found → (earlier: Nat) → start ≤ earlier → earlier < found → passes earlier = False
  | Zero, start, found, h, earlier, low, high => Void.exfalso (Option.noneNotSome found h)
  | Succ count, start, found, h, earlier, low, high =>
    match c: passes start with
      | True =>
        let same: start = found := Option.someInjective start found h
        Void.exfalso (Nat.lessIrrefl earlier (Nat.leTrans (Succ earlier) found earlier high (rewrite <- same in low)))
      | False =>
        match e: earlier == start with
          | True => rewrite DecEq.sound earlier start e in c
          | False =>
            let later: Succ start ≤ earlier := Nat.leNeSucc start earlier low (p => DecEq.soundFalse earlier start e (Eq.sym p))
            List.findRangeFirst passes count (Succ start) found h earlier later high

-- What is found passes, is in the range, and no smaller number passes.
theorem List.findRangeSome (passes: Nat → Bool) (count: Nat) (found: Nat) (h: (List.range count).find passes = Some found):
    And (passes found = True) (And (found < count) ((earlier: Nat) → earlier < found → passes earlier = False)) :=
  match List.findSome (List.range count) passes found h with
    | Both foundPasses member =>
      Both foundPasses
        (Both (And.right (List.memRangeFrom found count 0 member))
          (earlier before => List.findRangeFirst passes count 0 found h earlier (Nat.zeroLe earlier) before))

-- Finding nothing means no number in the range passes.
theorem List.findRangeNone (passes: Nat → Bool) (count: Nat) (h: (List.range count).find passes = None) (n: Nat) (below: n < count):
    passes n = False :=
  match c: passes n with
    | True => Void.exfalso (List.findNoneNotMem (List.range count) passes n c (List.memRangeFromIntro n count 0 (Nat.zeroLe n) below) h)
    | False => rfl

test "List.findRangeSome" := List.range 10 |> .find (n => n * n > 20) == Some 5

-- `List.minimum`: the least of a list that holds `least` and nothing else
-- is `least`, an empty list has none, and what it finds is in the list and
-- at most each element.

-- Folding `Ord.min` from `least` over elements that are all `least`.
theorem List.foldMinAll [auto ord: Ord a] (least: a): (xs: List a) → ((x: a) → x ∈ xs → x = least) → List.foldLeft xs least Ord.min = least
  | Nil, all => rfl
  | Cons x rest, all =>
    rewrite all x (Inl rfl), Ord.minSelf least in List.foldMinAll least rest (y member => all y (Inr member))

theorem List.minimumAllEqual [auto ord: Ord a] (least: a): (xs: List a) → least ∈ xs → ((x: a) → x ∈ xs → x = least) → List.minimum xs = Some least
  | Nil, member, all => Void.exfalso member
  | Cons x rest, member, all =>
    rewrite all x (Inl rfl) in Eq.cong Some (List.foldMinAll least rest (y member => all y (Inr member)))

theorem List.minimumEmpty [auto ord: Ord a]: (xs: List a) → ((x: a) → x ∈ xs → Void) → List.minimum xs = None
  | Nil, none => rfl
  | Cons x rest, none => Void.exfalso (none x (Inl rfl))

-- Folding with `Ord.min` gives at most the start and each element, and
-- gives the start or an element.
theorem List.foldMinLeStart [auto ord: Ord a]: (xs: List a) → (start: a) → List.foldLeft xs start Ord.min <= start
  | Nil, start => Ord.leRefl start
  | Cons y ys, start =>
    Ord.leTrans (List.foldLeft ys (Ord.min start y) Ord.min) (Ord.min start y) start (List.foldMinLeStart ys (Ord.min start y)) (Ord.minLeLeft start y)

theorem List.foldMinLeMember [auto ord: Ord a]: (xs: List a) → (start: a) → (x: a) → x ∈ xs → List.foldLeft xs start Ord.min <= x
  | Nil, start, x, member => Void.exfalso member
  | Cons y ys, start, x, Inl same =>
    rewrite Eq.sym same in
      Ord.leTrans (List.foldLeft ys (Ord.min start y) Ord.min) (Ord.min start y) y (List.foldMinLeStart ys (Ord.min start y)) (Ord.minLeRight start y)
  | Cons y ys, start, x, Inr member => List.foldMinLeMember ys (Ord.min start y) x member

theorem List.foldMinMember [auto ord: Ord a]: (xs: List a) → (start: a) → Or (List.foldLeft xs start Ord.min = start) (List.foldLeft xs start Ord.min ∈ xs)
  | Nil, start => Inl rfl
  | Cons y ys, start =>
    match List.foldMinMember ys (Ord.min start y) with
      | Inr member => Inr (Inr member)
      | Inl same =>
        match Ord.minEither start y with
          | Inl isStart => Inl (Eq.trans same isStart)
          | Inr isY => Inr (Inl (Eq.sym (Eq.trans same isY)))

-- The least element is in the list and at most every element.
theorem List.minimumSome [auto ord: Ord a] (xs: List a) (least: a) (found: List.minimum xs = Some least): And (least ∈ xs) ((x: a) → x ∈ xs → least <= x) :=
  match xs with
    | Nil => Void.exfalso (Option.noneNotSome least found)
    | Cons y ys =>
      let same := Option.someInjective (List.foldLeft ys y Ord.min) least found
      Both
        (match List.foldMinMember ys y with
          | Inl isY => Inl (Eq.sym (Eq.trans (Eq.sym same) isY))
          | Inr member => Inr (rewrite same at member))
        (x member =>
          rewrite Eq.sym same in
            match member with
              | Inl isY => rewrite Eq.sym isY in List.foldMinLeStart ys y
              | Inr inRest => List.foldMinLeMember ys y x inRest)

-- A list with an element has a least one.
theorem List.minimumExists [auto ord: Ord a]: (xs: List a) → (x: a) → x ∈ xs → ∃ (least: a) => List.minimum xs = Some least
  | Nil, x, member => Void.exfalso member
  | Cons y ys, x, member => Witness (List.foldLeft ys y Ord.min) rfl

-- An element that passes makes `List.any` true.
theorem List.anyOfMem: (xs: List a) → (q: a → Bool) → (y: a) → (qy: q y = True) → y ∈ xs → List.any xs q = True
  | Nil, q, y, qy, m => Void.exfalso m
  | Cons x xs, q, y, qy, Inl e => rewrite e, qy in rfl
  | Cons x xs, q, y, qy, Inr m =>
    match c: q x with
      | True => rfl
      | False => List.anyOfMem xs q y qy m

-- And back: when `List.any` is true, some element of the list passes.
theorem List.anyTrueElim: (xs: List a) → (p: a → Bool) → (goal: Prop) → List.any xs p = True → ((x: a) → x ∈ xs → p x = True → goal) → goal
  | Nil, p, goal, h, k => Void.exfalso (Bool.falseNotTrue h)
  | Cons z zs, p, goal, h, k =>
    match c: p z with
      | True => k z (Inl rfl) c
      | False => List.anyTrueElim zs p goal h (x inZs px => k x (Inr inZs) px)

-- `List.contains` is membership.
theorem List.memContains [auto eq: DecEq a] (xs: List a) (x: a): Iff (List.contains xs x = True) (x ∈ xs) := {
  forward = found =>
    List.anyTrueElim xs (member => member == x) (x ∈ xs) found (member isIn same => rewrite <- DecEq.sound member x same in isIn),
  backward = isIn => List.anyOfMem xs (member => member == x) x (DecEq.refl x) isIn
}

-- What `(.find p)` finds passes any other test some element passes.
theorem List.findAny (xs: List a) (p: a → Bool) (q: a → Bool) (y: a) (qy: q y = True) (h: List.find xs p = Some y): List.any xs q = True :=
  match List.findSome xs p y h with
    | Both py m => List.anyOfMem xs q y qy m

-- With distinct keys, finding by an element's key finds that element (and
-- `List.findKey`, std/List/SortLemmas.sw, says what is found has the key).
theorem List.findKeyDistinct [auto eq: DecEq k] (key: a → k): (xs: List a) → List.Distinct (List.map xs key) → (x: a) → x ∈ xs →
    List.find xs (y => key y == key x) = Some x
  | Nil, d, x, m => Void.exfalso m
  | Cons z zs, Both notMem d, x, Inl e => rewrite e, DecEq.refl (key x) in rfl
  | Cons z zs, Both notMem d, x, Inr m =>
    match c: key z == key x with
      | True => Void.exfalso (notMem (rewrite DecEq.sound (key z) (key x) c in List.memMap zs x m key))
      | False => List.findKeyDistinct key zs d x m

theorem List.findKeyDistinctExample: List.find [(1, "a"), (2, "b")] (y => y.fst == 2) = Some (2, "b") :=
  List.findKeyDistinct Pair.fst [(1, "a"), (2, "b")]
    (Both (m => match m with
        | Inl p => Nat.succNotZero 0 (Nat.succInjective 1 0 p)
        | Inr v => v)
      (Both (m => m) Trivial))
    (2, "b") (Inr (Inl rfl))

-- A key of part of the list is a key of the list.
theorem List.memMapOfSub (key: a → k) (s: List a) (xs: List a) (sub: (y: a) → y ∈ s → y ∈ xs) (z: k)
    (m: z ∈ List.map s key): z ∈ List.map xs key :=
  List.anyElim (y => key y = z) (z ∈ List.map xs key) s (List.memMapAny s key z m)
    (y inS e => rewrite <- e in List.memMap xs y (sub y inS) key)

-- Keeping some elements keeps their keys distinct.
theorem List.distinctMapFilter: (xs: List a) → (key: a → k) → (p: a → Bool) → List.Distinct (List.map xs key) →
    List.Distinct (List.map (List.filter xs p) key)
  | Nil, key, p, d => Trivial
  | Cons x xs, key, p, Both notMem d =>
    match e: p x with
      | True =>
        Both
          (m => notMem (List.memMapOfSub key (List.filter xs p) xs (y inFiltered => match List.memFilter xs p y inFiltered with
            | Both inXs py => inXs) (key x) m))
          (List.distinctMapFilter xs key p d)
      | False => List.distinctMapFilter xs key p d

-- Keeping some elements keeps them distinct.
theorem List.distinctFilter: (xs: List a) → (p: a → Bool) → List.Distinct xs → List.Distinct (List.filter xs p)
  | Nil, p, d => Trivial
  | Cons x xs, p, Both notMem d =>
    match e: p x with
      | True => Both (m => notMem (And.left (List.memFilter xs p x m))) (List.distinctFilter xs p d)
      | False => List.distinctFilter xs p d

-- A key of a `filterMap`'s result is the key of an element it came from,
-- when each result has the key of its element.
theorem List.memMapFilterMap (f: a → Option b) (ka: a → k) (kb: b → k) (hk: (x: a) → (y: b) → f x = Some y → kb y = ka x) (z: k):
    (xs: List a) → z ∈ List.map (List.filterMap xs f) kb → z ∈ List.map xs ka
  | Nil, m => m
  | Cons x xs, m =>
    match e: f x with
      | None => Inr (List.memMapFilterMap f ka kb hk z xs m)
      | Some y =>
        match m with
          | Inl q => Inl (Eq.trans (Eq.sym (hk x y e)) q)
          | Inr r => Inr (List.memMapFilterMap f ka kb hk z xs r)

-- So `filterMap` keeps keys distinct.
theorem List.distinctMapFilterMap (f: a → Option b) (ka: a → k) (kb: b → k) (hk: (x: a) → (y: b) → f x = Some y → kb y = ka x):
    (xs: List a) → List.Distinct (List.map xs ka) → List.Distinct (List.map (List.filterMap xs f) kb)
  | Nil, d => Trivial
  | Cons x xs, Both notMem d =>
    match e: f x with
      | None => List.distinctMapFilterMap f ka kb hk xs d
      | Some y =>
        Both (m => notMem (rewrite <- hk x y e in List.memMapFilterMap f ka kb hk (kb y) xs m))
          (List.distinctMapFilterMap f ka kb hk xs d)

-- Two lists with distinct keys and no key in common, joined, have distinct keys.
theorem List.distinctMapAppend (key: a → k) (xs: List a) (ys: List a) (dx: List.Distinct (List.map xs key)) (dy: List.Distinct (List.map ys key))
    (dj: List.Disjoint (List.map xs key) (List.map ys key)): List.Distinct (List.map (List.append xs ys) key) :=
  rewrite List.mapAppend xs ys key in List.distinctAppend (List.map xs key) (List.map ys key) dx dy dj

theorem List.distinctMapFilterExample: List.Distinct (List.map (List.filter [1, 2] (x => Nat.leq 2 x)) Succ) :=
  List.distinctMapFilter [1, 2] Succ (x => Nat.leq 2 x) List.distinctMapExample

-- `findMap` is the first of the `filterMap` results, found without building
-- the rest.
theorem List.findMapIsHeadFilterMap: (xs: List a) → (f: a → Option b) → List.findMap xs f = List.head (List.filterMap xs f)
  | Nil, f => rfl
  | Cons x xs, f =>
    match f x with
      | None => List.findMapIsHeadFilterMap xs f
      | Some y => rfl

theorem List.lengthTails: (xs: List a) → List.length (List.tails xs) = Succ (List.length xs)
  | Nil => rfl
  | Cons x xs => Eq.cong Succ (List.lengthTails xs)

theorem List.splitAtFst (xs: List a) (n: Nat): Pair.fst (List.splitAt xs n) = List.take xs n := rfl

-- The loop's prefix is `takeWhile`'s, after what it had taken.
theorem List.spanOntoTakeDrop (p: a → Bool): (taken: List a) → (xs: List a) →
    List.spanOnto taken p xs = MkPair (List.reverseOnto taken (List.takeWhile xs p)) (List.dropWhile xs p)
  | taken, Nil => rfl
  | taken, Cons x xs =>
    match p x with
      | True => List.spanOntoTakeDrop p (Cons x taken) xs
      | False => rfl

-- `span` is `takeWhile` and `dropWhile` (its definition before it became one
-- pass).
theorem List.spanTakeDrop (xs: List a) (p: a → Bool): List.span xs p = MkPair (List.takeWhile xs p) (List.dropWhile xs p) :=
  List.spanOntoTakeDrop p Nil xs

theorem List.spanExample: List.span [1, 2, 3, 1] (x => Nat.leq x 2) = MkPair [1, 2] [3, 1] := rfl

-- `takeWhile` over a prefix that passes: the prefix, then what passes after.
theorem List.takeWhileAppend (p: a → Bool) (rest: List a): (prefix: List a) → List.all prefix p = True →
    List.takeWhile (List.append prefix rest) p = List.append prefix (List.takeWhile rest p)
  | Nil, all => rfl
  | Cons x xs, all =>
    match p x with
      | True => Eq.cong (Cons x) (List.takeWhileAppend p rest xs all)
      | False => Void.exfalso (Bool.falseNotTrue all)

-- `dropWhile` over a prefix that passes drops it.
theorem List.dropWhileAppend (p: a → Bool) (rest: List a): (prefix: List a) → List.all prefix p = True →
    List.dropWhile (List.append prefix rest) p = List.dropWhile rest p
  | Nil, all => rfl
  | Cons x xs, all =>
    match p x with
      | True => List.dropWhileAppend p rest xs all
      | False => Void.exfalso (Bool.falseNotTrue all)

-- Where `takeWhile` takes nothing, `dropWhile` drops nothing.
theorem List.dropWhileStops (p: a → Bool): (xs: List a) → List.takeWhile xs p = Nil → List.dropWhile xs p = xs
  | Nil, stops => rfl
  | Cons x xs, stops =>
    match p x with
      | True => Void.exfalso (List.consNotNil x (List.takeWhile xs p) stops)
      | False => rfl

-- `span` of a prefix that passes, then a rest that starts with an element
-- that doesn't (or is empty), splits between the two.
theorem List.spanAppend (p: a → Bool) (taken: List a) (rest: List a) (all: List.all taken p = True)
    (stops: List.takeWhile rest p = Nil):
    List.span (List.append taken rest) p = MkPair taken rest :=
  rewrite List.spanTakeDrop (List.append taken rest) p, List.takeWhileAppend p rest taken all, stops, List.appendNil taken,
    List.dropWhileAppend p rest taken all, List.dropWhileStops p rest stops in
    rfl

-- `map` through the other list functions (SW-198, day 8).

theorem List.mapAppend: (xs: List a) → (ys: List a) → (f: a → b) → List.map (List.append xs ys) f = List.append (List.map xs f) (List.map ys f)
  | Nil, ys, f => rfl
  | Cons x xs, ys, f => rewrite List.mapAppend xs ys f

theorem List.takeMap: (xs: List a) → (k: Nat) → (f: a → b) → List.take (List.map xs f) k = List.map (List.take xs k) f
  | xs, Zero, f => rfl
  | Nil, Succ k, f => rfl
  | Cons x xs, Succ k, f => rewrite List.takeMap xs k f

-- The first `k` of two lists combined are the first `k` of each combined.
theorem List.takeZipWith (f: a → b → c): (xs: List a) → (ys: List b) → (k: Nat) →
    List.take (List.zipWith xs ys f) k = List.zipWith (List.take xs k) (List.take ys k) f
  | xs, ys, Zero => rfl
  | Nil, ys, Succ k => rfl
  | Cons x xs, Nil, Succ k => rfl
  | Cons x xs, Cons y ys, Succ k => Eq.cong (Cons (f x y)) (List.takeZipWith f xs ys k)

theorem List.takeZipWithExample: List.take (List.zipWith [1, 2, 3] [10, 20, 30] Nat.add) 2 = List.zipWith [1, 2] [10, 20] Nat.add :=
  List.takeZipWith Nat.add [1, 2, 3] [10, 20, 30] 2

theorem List.foldLeftMap: (xs: List a) → (z: c) → (f: c → b → c) → (g: a → b) →
    List.foldLeft (List.map xs g) z f = List.foldLeft xs z (acc x => f acc (g x))
  | Nil, z, f, g => rfl
  | Cons x xs, z, f, g => List.foldLeftMap xs (f z (g x)) f g

-- A fold over `zipWith` folds over the pairs, combining each as it goes.
theorem List.foldLeftZipWith (g: a → b → c) (f: d → c → d): (xs: List a) → (ys: List b) → (z: d) →
    List.foldLeft (List.zipWith xs ys g) z f = List.foldLeft (List.zip xs ys) z (acc p => f acc (g p.fst p.snd))
  | Nil, ys, z => rfl
  | Cons x xs, Nil, z => rfl
  | Cons x xs, Cons y ys, z => List.foldLeftZipWith g f xs ys (f z (g x y))

-- A fold over `zip xs ys` whose step uses only each pair's first element is
-- the fold over `xs`, when `ys` is at least as long.
theorem List.foldLeftZipLeft (step: c → Pair a b → c) (f: c → a → c) (same: (acc: c) → (x: a) → (y: b) → step acc (MkPair x y) = f acc x):
    (xs: List a) → (ys: List b) → (z: c) → List.length xs ≤ List.length ys → List.foldLeft (List.zip xs ys) z step = List.foldLeft xs z f
  | Nil, ys, z, le => rfl
  | Cons x xs, Nil, z, le => Void.exfalso (Bool.falseNotTrue le)
  | Cons x xs, Cons y ys, z, le => rewrite same z x y in List.foldLeftZipLeft step f same xs ys (f z x) le

theorem List.foldRightZipLeft (step: Pair a b → c → c) (f: a → c → c) (same: (x: a) → (y: b) → (acc: c) → step (MkPair x y) acc = f x acc):
    (xs: List a) → (ys: List b) → (z: c) → List.length xs ≤ List.length ys → List.foldRight (List.zip xs ys) z step = List.foldRight xs z f
  | Nil, ys, z, le => rfl
  | Cons x xs, Nil, z, le => Void.exfalso (Bool.falseNotTrue le)
  | Cons x xs, Cons y ys, z, le =>
    calc List.foldRight (Cons (MkPair x y) (List.zip xs ys)) z step
      _ = step (MkPair x y) (List.foldRight (List.zip xs ys) z step) := List.foldRightCons (List.zip xs ys) (MkPair x y) z step
      _ = f x (List.foldRight (List.zip xs ys) z step) := same x y (List.foldRight (List.zip xs ys) z step)
      _ = f x (List.foldRight xs z f) := rewrite List.foldRightZipLeft step f same xs ys z le
      _ = List.foldRight (Cons x xs) z f := Eq.sym (List.foldRightCons xs x z f)

test "List.foldLeftZipLeft" := List.foldLeft (List.zip [1, 2, 3] ["a", "b", "c", "d"]) 0 (acc pair => acc + pair.fst) == 6

theorem List.anyMap: (xs: List a) → (p: b → Bool) → (f: a → b) → List.any (List.map xs f) p = List.any xs (x => p (f x))
  | Nil, p, f => rfl
  | Cons x xs, p, f => rewrite List.anyMap xs p f

-- Some element of a `flatMap` passes exactly when some list it is made of
-- has one.
theorem List.anyFlatMap (f: a → List b) (p: b → Bool): (xs: List a) → List.any (List.flatMap xs f) p = List.any xs (x => List.any (f x) p)
  | Nil => rfl
  | Cons x xs =>
    Eq.trans (List.anyAppend (f x) (List.flatMap xs f) p) (Eq.cong (later => List.any (f x) p ∨ later) (List.anyFlatMap f p xs))

-- `List.any` of an `∨` is the `∨` of the `List.any`s.
theorem List.anyOr (p: a → Bool) (q: a → Bool): (xs: List a) → List.any xs (x => p x ∨ q x) = (List.any xs p ∨ List.any xs q)
  | Nil => rfl
  | Cons x xs => rewrite List.anyOr p q xs in cases

-- Two `List.any`s, in either order.
theorem List.anyComm (related: a → b → Bool) (ys: List b): (xs: List a) →
    List.any xs (x => List.any ys (y => related x y)) = List.any ys (y => List.any xs (x => related x y))
  | Nil => Eq.sym (List.anyFalse ys (y => False) (y => rfl))
  | Cons x xs =>
    rewrite List.anyComm related ys xs in
      Eq.sym (List.anyOr (y => related x y) (y => List.any xs (other => related other y)) ys)

theorem List.anyFlatMapExample: List.any (List.flatMap [1, 2] (x => [x, x * 10])) (== 20) = List.any [1, 2] (x => List.any [x, x * 10] (== 20)) :=
  List.anyFlatMap (x => [x, x * 10]) (== 20) [1, 2]

theorem List.countMap (xs: List a) (p: b → Bool) (f: a → b): List.count (List.map xs f) p = List.count xs (x => p (f x)) :=
  List.foldLeftMap xs 0 (n x => Nat.succIf n (p x)) f

theorem List.occurrencesMap: (xs: List a) → (f: a → b) → (p: b → Bool) → List.occurrences (List.map xs f) p = List.occurrences xs (x => p (f x))
  | Nil, f, p => rfl
  | Cons x xs, f, p => rewrite List.occurrencesMap xs f p in rfl

-- Mapping both lists of a permutation keeps it one.
theorem List.permMap (xs: List a) (ys: List a) (h: List.Perm xs ys) (f: a → b): List.Perm (List.map xs f) (List.map ys f) :=
  p => rewrite List.occurrencesMap xs f p, List.occurrencesMap ys f p in h (x => p (f x))

-- Counting what `(.filter keep)` kept is counting what passes both tests.
theorem List.occurrencesFilter: (xs: List a) → (keep: a → Bool) → (p: a → Bool) →
    List.occurrences (List.filter xs keep) p = List.occurrences xs (x => p x ∧ keep x)
  | Nil, keep, p => rfl
  | Cons x xs, keep, p =>
    match e: keep x with
      | True =>
        rewrite List.occurrencesFilter xs keep p in
          match p x with
            | True => rfl
            | False => rfl
      | False =>
        rewrite List.occurrencesFilter xs keep p in
          match p x with
            | True => rfl
            | False => rfl

-- The first k numbers of a longer run.
theorem List.takeRangeFrom: (k: Nat) → (n: Nat) → (s: Nat) → k ≤ n → List.take (List.rangeFrom n s) k = List.rangeFrom k s
  | Zero, n, s, h => rfl
  | Succ k, Zero, s, h => Void.exfalso (Bool.falseNotTrue h)
  | Succ k, Succ n, s, h => rewrite List.takeRangeFrom k n (Succ s) h

-- The pairs of a mapped list are the list's pairs, mapped.
theorem List.pairsMap: (xs: List a) → (f: a → b) → List.pairs (List.map xs f) = List.map (List.pairs xs) (p => MkPair (f (Pair.fst p)) (f (Pair.snd p)))
  | Nil, f => rfl
  | Cons x xs, f =>
    rewrite List.mapAppend (List.map xs (y => MkPair x y)) (List.pairs xs) (p => MkPair (f (Pair.fst p)) (f (Pair.snd p))),
      List.mapMap xs (y => MkPair (f x) y) f, List.mapMap xs (p => MkPair (f (Pair.fst p)) (f (Pair.snd p))) (y => MkPair x y),
      List.pairsMap xs f

-- A `filterMap` that keeps every element, changed by `g`, is a `map`.
theorem List.filterMapSomeMem (xs: List a) (f: a → Option b) (g: a → b) (h: (x: a) → x ∈ xs → f x = Some (g x)):
    List.filterMap xs f = List.map xs g :=
  Eq.trans (List.filterMapCongMem xs f (x => Some (g x)) h) (List.filterMapSome xs g)

-- A `filterMap` that keeps every element as it is gives the list back.
theorem List.filterMapAll (f: a → Option a): (xs: List a) → ((x: a) → x ∈ xs → f x = Some x) → List.filterMap xs f = xs
  | Nil, h => rfl
  | Cons x xs, h => rewrite h x (Inl rfl) in Eq.cong (Cons x) (List.filterMapAll f xs (y m => h y (Inr m)))

test "List.pairsMap" := (List.map [1, 2, 3] Succ).pairs == List.map [1, 2, 3].pairs (p => MkPair (Succ p.fst) (Succ p.snd))

-- the largest by folding Nat.max --------------------------------------------

-- The fold starts at `start` and never goes down.
theorem List.foldMaxGe: (xs: List Nat) → (start: Nat) → start ≤ List.foldLeft xs start Nat.max
  | Nil, start => Nat.leRefl start
  | Cons x xs, start => Nat.leTrans start (Nat.max start x) (List.foldLeft xs (Nat.max start x) Nat.max) (Nat.leMaxLeft start x) (List.foldMaxGe xs (Nat.max start x))

-- Every element is at most the largest.
theorem List.leFoldMax: (xs: List Nat) → (x: Nat) → (start: Nat) → x ∈ xs → x ≤ List.foldLeft xs start Nat.max
  | Nil, x, start, m => Void.exfalso m
  | Cons y ys, x, start, Inl e => rewrite <- e in Nat.leTrans y (Nat.max start y) (List.foldLeft ys (Nat.max start y) Nat.max) (Nat.leMaxRight start y) (List.foldMaxGe ys (Nat.max start y))
  | Cons y ys, x, start, Inr m => List.leFoldMax ys x (Nat.max start y) m

-- The largest is the start or one of the elements.
theorem List.foldMaxMem: (xs: List Nat) → (start: Nat) → Or (List.foldLeft xs start Nat.max = start) (List.foldLeft xs start Nat.max ∈ xs)
  | Nil, start => Inl rfl
  | Cons y ys, start =>
    match List.foldMaxMem ys (Nat.max start y) with
      | Inr m => Inr (Inr m)
      | Inl e =>
        match h: Nat.leq start y with
          | True => Inr (Inl (Eq.sym e))
          | False => Inl e

-- lengths, and sums over ranges ---------------------------------------------

-- Zipping two lists of at least n elements gives at least n.
theorem List.lengthZipWithAtLeast: (u: List a) → (n: Nat) → (v: List b) → n ≤ List.length u → n ≤ List.length v → (f: a → b → c) →
    n ≤ List.length (List.zipWith u v f)
  | u, Zero, v, hu, hv, f => rfl
  | Nil, Succ n, v, hu, hv, f => hu
  | Cons x xs, Succ n, Nil, hu, hv, f => hv
  | Cons x xs, Succ n, Cons y ys, hu, hv, f => List.lengthZipWithAtLeast xs n ys hu hv f

-- Running results: one more than the elements, the start first.
theorem List.lengthScanLeft: (xs: List a) → (start: b) → (f: b → a → b) → List.length (List.scanLeft xs start f) = Succ (List.length xs)
  | Nil, start, f => rfl
  | Cons x xs, start, f => Eq.cong Succ (List.lengthScanLeft xs (f start x) f)

-- A sum over the numbers below b is the sum below t and the sum from t up to b.
theorem List.sumByRangeSplit (f: Nat → Nat) (t: Nat) (b: Nat) (tb: t ≤ b):
    List.sumBy (List.rangeFrom b 0) f = List.sumBy (List.rangeFrom t 0) f + List.sumBy (List.rangeFrom (b - t) t) f :=
  calc List.sumBy (List.rangeFrom b 0) f
    _ = List.sumBy (List.rangeFrom (t + (b - t)) 0) f := Eq.cong (n => List.sumBy (List.rangeFrom n 0) f) (Eq.sym (Nat.addSubCancel t b tb))
    _ = List.sumBy (List.append (List.rangeFrom t 0) (List.rangeFrom (b - t) (0 + t))) f := Eq.cong (.sumBy f) (List.rangeFromAppend t (b - t) 0)
    _ = List.sumBy (List.rangeFrom t 0) f + List.sumBy (List.rangeFrom (b - t) t) f := List.sumByAppend (List.rangeFrom t 0) (List.rangeFrom (b - t) t) f

-- sums of zero -----------------------------------------------------------------

-- A sum of numbers is 0 only if each is.
theorem List.sumByZeroElim: (xs: List a) → (f: a → Nat) → List.sumBy xs f = 0 → (x: a) → x ∈ xs → f x = 0
  | Nil, f, h, x, m => Void.exfalso m
  | Cons y ys, f, h, x, Inl e => rewrite <- e in (Nat.addEqZero (f y) (List.sumBy ys f) (Eq.trans (Eq.sym (List.sumByCons ys y f)) h)).left
  | Cons y ys, f, h, x, Inr m => List.sumByZeroElim ys f (Nat.addEqZero (f y) (List.sumBy ys f) (Eq.trans (Eq.sym (List.sumByCons ys y f)) h)).right x m

theorem List.sumByZeroIntro: (xs: List a) → (f: a → Nat) → ((x: a) → x ∈ xs → f x = 0) → List.sumBy xs f = 0
  | Nil, f, h => rfl
  | Cons y ys, f, h => rewrite List.sumByCons ys y f, h y (Inl rfl), List.sumByZeroIntro ys f (x m => h x (Inr m)) in rfl

-- filtering what can't pass anyway ------------------------------------------

-- Dropping elements that fail `q`, when only elements that pass `q` can pass
-- `p`, changes neither `any p` nor `count p`.
theorem List.anyFilter: (xs: List a) → (p: a → Bool) → (q: a → Bool) → (h: (x: a) → p x = True → q x = True) → List.any (List.filter xs q) p = List.any xs p
  | Nil, p, q, h => rfl
  | Cons x xs, p, q, h =>
    match e: q x with
      | True => rewrite List.anyFilter xs p q h in rfl
      | False =>
        match f: p x with
          | True => Void.exfalso (Bool.falseNotTrue (Eq.trans (Eq.sym e) (h x f)))
          | False => List.anyFilter xs p q h

theorem List.countFromFilter: (xs: List a) → (n: Nat) → (p: a → Bool) → (q: a → Bool) → (h: (x: a) → p x = True → q x = True) →
    List.foldLeft (List.filter xs q) n (k x => Nat.succIf k (p x)) = List.foldLeft xs n (k x => Nat.succIf k (p x))
  | Nil, n, p, q, h => rfl
  | Cons x xs, n, p, q, h =>
    match e: q x with
      | True => List.countFromFilter xs (Nat.succIf n (p x)) p q h
      | False =>
        match f: p x with
          | True => Void.exfalso (Bool.falseNotTrue (Eq.trans (Eq.sym e) (h x f)))
          | False => List.countFromFilter xs n p q h

theorem List.countFilter (xs: List a) (p: a → Bool) (q: a → Bool) (h: (x: a) → p x = True → q x = True): List.count (List.filter xs q) p = List.count xs p :=
  List.countFromFilter xs 0 p q h

-- membership through zip, take, drop and filter ------------------------------

-- Each pair of `List.zip xs ys` is an element of `xs` with one of `ys`.
theorem List.memZip (p: (a, b)): (xs: List a) → (ys: List b) → p ∈ List.zip xs ys → And (p.fst ∈ xs) (p.snd ∈ ys)
  | Nil, ys, m => Void.exfalso m
  | Cons x xs, Nil, m => Void.exfalso m
  | Cons x xs, Cons y ys, Inl e => rewrite <- e in Both (Inl rfl) (Inl rfl)
  | Cons x xs, Cons y ys, Inr m =>
    match List.memZip p xs ys m with
      | Both inXs inYs => Both (Inr inXs) (Inr inYs)

theorem List.memTake: (xs: List a) → (v: a) → (n: Nat) → v ∈ List.take xs n → v ∈ xs
  | xs, v, Zero, m => Void.exfalso m
  | Nil, v, Succ n, m => m
  | Cons x xs, v, Succ n, Inl e => Inl e
  | Cons x xs, v, Succ n, Inr m => Inr (List.memTake xs v n m)

theorem List.memDrop: (xs: List a) → (v: a) → (n: Nat) → v ∈ List.drop xs n → v ∈ xs
  | xs, v, Zero, m => m
  | Nil, v, Succ n, m => m
  | Cons x xs, v, Succ n, m => Inr (List.memDrop xs v n m)

-- What passes the test is kept.
theorem List.memFilterIntro: (xs: List a) → (p: a → Bool) → (v: a) → v ∈ xs → p v = True → v ∈ List.filter xs p
  | Nil, p, v, m, h => m
  | Cons x xs, p, v, Inl e, h => rewrite <- e at h in (rewrite h in Inl e)
  | Cons x xs, p, v, Inr m, h =>
    match e: p x with
      | True => Inr (List.memFilterIntro xs p v m h)
      | False => List.memFilterIntro xs p v m h

-- Filtering a mapped list is mapping the filtered list.
theorem List.filterOfMap: (xs: List a) → (q: b → Bool) → (g: a → b) → List.filter (List.map xs g) q = List.map (List.filter xs (x => q (g x))) g
  | Nil, q, g => rfl
  | Cons x xs, q, g =>
    match e: q (g x) with
      | True => rewrite List.filterOfMap xs q g in rfl
      | False => List.filterOfMap xs q g

-- Each pair of `List.pairs xs` is two elements of `xs`.
theorem List.memPairs (p: (a, a)): (xs: List a) → p ∈ List.pairs xs → And (p.fst ∈ xs) (p.snd ∈ xs)
  | Nil, m => Void.exfalso m
  | Cons x xs, m =>
    match List.memAppend p (List.map xs (y => (x, y))) (List.pairs xs) m with
      | Inl first =>
        List.anyElim (y => (x, y) = p) (And (p.fst ∈ Cons x xs) (p.snd ∈ Cons x xs)) xs (List.memMapAny xs (y => (x, y)) p first)
          (y inXs e => rewrite <- e in Both (Inl rfl) (Inr inXs))
      | Inr later =>
        match List.memPairs p xs later with
          | Both one other => Both (Inr one) (Inr other)

-- The last element, if there is one, is an element.
theorem List.lastMem: (xs: List a) → (x: a) → List.last xs = Some x → x ∈ xs
  | Nil, x, h => Void.exfalso (Option.noneNotSome x h)
  | Cons y Nil, x, h => Inl (Option.someInjective y x h)
  | Cons y (Cons z zs), x, h => Inr (List.lastMem (Cons z zs) x h)

theorem List.lastMemExample: 3 ∈ [1, 2, 3] := List.lastMem [1, 2, 3] 3 rfl

-- The last element of a list with `x` added at the end is `x`.
theorem List.lastSnoc (x: a): (xs: List a) → List.last (List.append xs [x]) = Some x
  | Nil => rfl
  | Cons y Nil => rfl
  | Cons y (Cons z zs) => List.lastSnoc x (Cons z zs)

-- `filterMap` keeps `y` when an element maps to `Some y` ...
theorem List.memFilterMapIntro (f: a → Option b) (x: a) (y: b): (xs: List a) → x ∈ xs → f x = Some y → y ∈ List.filterMap xs f
  | Nil, m, e => Void.exfalso m
  | Cons z zs, Inl q, e => rewrite q, e in Inl rfl
  | Cons z zs, Inr m, e =>
    match c: f z with
      | None => List.memFilterMapIntro f x y zs m e
      | Some w => Inr (List.memFilterMapIntro f x y zs m e)

-- ... and keeps nothing else.
theorem List.memFilterMapElim (f: a → Option b) (y: b): (xs: List a) → y ∈ List.filterMap xs f → List.Any (x => f x = Some y) xs
  | Nil, m => m
  | Cons z zs, m =>
    match c: f z with
      | None => Inr (List.memFilterMapElim f y zs m)
      | Some w =>
        match m with
          | Inl q => Inl (Eq.cong Some q)
          | Inr r => Inr (List.memFilterMapElim f y zs r)

-- Everything `filterMap` keeps has `q` when every element's `Some` result
-- would; and back.
theorem List.allFilterMap (q: b → Prop) (f: a → Option b): (xs: List a) → List.All (x => (y: b) → f x = Some y → q y) xs → List.All q (List.filterMap xs f)
  | Nil, h => Trivial
  | Cons z zs, Both hz h =>
    match c: f z with
      | None => List.allFilterMap q f zs h
      | Some w => Both (hz w rfl) (List.allFilterMap q f zs h)

theorem List.allFilterMapElim (q: b → Prop) (f: a → Option b): (xs: List a) → List.All q (List.filterMap xs f) → List.All (x => (y: b) → f x = Some y → q y) xs
  | Nil, h => Trivial
  | Cons z zs, h =>
    match c: f z with
      | None => Both (y e => Void.exfalso (Option.noneNotSome y e)) (List.allFilterMapElim q f zs h)
      | Some w =>
        match h with
          | Both hw rest => Both (y e => rewrite <- Option.someInjective w y e in hw) (List.allFilterMapElim q f zs rest)

theorem List.memFilterMapExample: 4 ∈ List.filterMap [1, 2, 3] (x => if x == 2 then Some (x * 2) else None) :=
  List.memFilterMapIntro (x => if x == 2 then Some (x * 2) else None) 2 4 [1, 2, 3] (Inr (Inl rfl)) rfl

-- `List.all` and `List.any` (the `Bool`s a program computes) are `List.All`
-- and `List.Any` (the propositions proofs use), so a lemma needs only one
-- form.
theorem List.allToAll (p: a → Bool): (xs: List a) → List.all xs p = True → List.All (x => p x = True) xs
  | Nil, h => Trivial
  | Cons x xs, h =>
    match c: p x with
      | True => Both rfl (List.allToAll p xs h)
      | False => Void.exfalso (Bool.falseNotTrue h)

theorem List.allOfAll (p: a → Bool): (xs: List a) → List.All (x => p x = True) xs → List.all xs p = True
  | Nil, h => rfl
  | Cons x xs, Both px h => rewrite px in List.allOfAll p xs h

theorem List.allIff (xs: List a) (p: a → Bool): List.all xs p = True ↔ List.All (x => p x = True) xs :=
  { forward = List.allToAll p xs, backward = List.allOfAll p xs }

theorem List.anyToAny (p: a → Bool): (xs: List a) → List.any xs p = True → List.Any (x => p x = True) xs
  | Nil, h => Void.exfalso (Bool.falseNotTrue h)
  | Cons x xs, h =>
    match c: p x with
      | True => Inl rfl
      | False => Inr (List.anyToAny p xs h)

theorem List.anyOfAny (p: a → Bool): (xs: List a) → List.Any (x => p x = True) xs → List.any xs p = True
  | Nil, h => Void.exfalso h
  | Cons x xs, Inl px => rewrite px in rfl
  | Cons x xs, Inr h =>
    match c: p x with
      | True => rfl
      | False => List.anyOfAny p xs h

theorem List.anyIff (xs: List a) (p: a → Bool): List.any xs p = True ↔ List.Any (x => p x = True) xs :=
  { forward = List.anyToAny p xs, backward = List.anyOfAny p xs }

-- Membership written with `any` and `==` is `x ∈ xs`. (`x ∈ xs` as a
-- `Bool` is `List.decMem`'s decision: `Decidable.toBoolSound` and
-- `Decidable.toBoolOf` take it to the proposition and back.)
theorem List.anyEqIff [auto eq: DecEq a] (x: a) (xs: List a): List.any xs (== x) = True ↔ x ∈ xs := {
  forward = h => List.anyTrueElim xs (== x) (x ∈ xs) h (y m e => rewrite <- DecEq.sound y x e in m),
  backward = m => List.anyOfMem xs (== x) x (DecEq.refl x) m
}

theorem List.allIffExample: List.All (x => Nat.leq 1 x = True) [1, 2, 3] := (List.allIff [1, 2, 3] (x => Nat.leq 1 x)).forward rfl

-- `any` is whether `find` finds something.
theorem List.anyFind (p: a → Bool): (xs: List a) → List.any xs p = Option.isSome (List.find xs p)
  | Nil => rfl
  | Cons x xs =>
    match c: p x with
      | True => rfl
      | False => List.anyFind p xs

-- Running accumulations beside the elements: `List.zipWith xs
-- (List.scanLeft xs z f) g` is `g` of each element and the fold of the
-- elements before it (`List.getOrZipWithScanLeft`, std/List/Index.sw). It
-- lays items end to end from `z`, say, with `f` adding an item's size and
-- `g` placing it. Its first step, for induction, is by computation:
theorem List.zipWithScanLeftCons (x: a) (xs: List a) (z: b) (f: b → a → b) (g: a → b → c):
    List.zipWith (Cons x xs) (List.scanLeft (Cons x xs) z f) g = Cons (g x z) (List.zipWith xs (List.scanLeft xs (f z x) f) g) := rfl

theorem List.zipWithScanLeftExample:
    List.zipWith [2, 3, 4] (List.scanLeft [2, 3, 4] 10 (offset width => offset + width)) (width offset => (offset, width)) = [(10, 2), (12, 3), (15, 4)] := rfl

-- It has an element for each element.
theorem List.lengthZipWithScanLeft (f: b → a → b) (g: a → b → c): (xs: List a) → (z: b) →
    List.length (List.zipWith xs (List.scanLeft xs z f) g) = List.length xs
  | Nil, z => rfl
  | Cons x xs, z => Eq.cong Succ (List.lengthZipWithScanLeft f g xs (f z x))

-- What `g` keeps of an element (`h`, an id say) doesn't depend on the other
-- list, so mapping it over the zip is mapping over the first list.
theorem List.mapZipWithLeft (h: c → d) (k: a → d) (g: a → b → c) (same: (x: a) → (y: b) → h (g x y) = k x):
    (xs: List a) → (ys: List b) → List.length xs ≤ List.length ys → List.map (List.zipWith xs ys g) h = List.map xs k
  | Nil, ys, le => rfl
  | Cons x xs, Nil, le => Void.exfalso (Bool.falseNotTrue le)
  | Cons x xs, Cons y ys, le => rewrite same x y, List.mapZipWithLeft h k g same xs ys le in rfl

theorem List.mapZipWithScanLeft (h: c → d) (k: a → d) (g: a → b → c) (same: (x: a) → (y: b) → h (g x y) = k x)
    (xs: List a) (z: b) (f: b → a → b): List.map (List.zipWith xs (List.scanLeft xs z f) g) h = List.map xs k :=
  List.mapZipWithLeft h k g same xs (List.scanLeft xs z f) (rewrite List.lengthScanLeft xs z f in Nat.leSucc (List.length xs))

-- `mapAccumLeft` is a fold for its final state, and for its list the zip of
-- the elements with the running states.
theorem List.mapAccumLeftGoSpec (f: s → a → Pair s b): (xs: List a) → (state: s) → (done: List b) →
    List.mapAccumLeftGo f state done xs
      = MkPair (List.foldLeft xs state (st x => Pair.fst (f st x)))
        (List.reverseOnto done (List.zipWith xs (List.scanLeft xs state (st x => Pair.fst (f st x))) (x st => Pair.snd (f st x))))
  | Nil, state, done => rfl
  | Cons x xs, state, done => List.mapAccumLeftGoSpec f xs (Pair.fst (f state x)) (Cons (Pair.snd (f state x)) done)

theorem List.mapAccumLeftState (xs: List a) (initial: s) (f: s → a → Pair s b):
    Pair.fst (List.mapAccumLeft xs initial f) = List.foldLeft xs initial (st x => Pair.fst (f st x)) :=
  Eq.cong Pair.fst (List.mapAccumLeftGoSpec f xs initial Nil)

theorem List.mapAccumLeftList (xs: List a) (initial: s) (f: s → a → Pair s b):
    Pair.snd (List.mapAccumLeft xs initial f) = List.zipWith xs (List.scanLeft xs initial (st x => Pair.fst (f st x))) (x st => Pair.snd (f st x)) :=
  Eq.cong Pair.snd (List.mapAccumLeftGoSpec f xs initial Nil)

theorem List.lengthMapAccumLeft (xs: List a) (initial: s) (f: s → a → Pair s b):
    List.length (Pair.snd (List.mapAccumLeft xs initial f)) = List.length xs :=
  rewrite List.mapAccumLeftList xs initial f in List.lengthZipWithScanLeft (st x => Pair.fst (f st x)) (x st => Pair.snd (f st x)) xs initial

theorem List.mapAccumLeftExample: List.mapAccumLeft [1, 2, 3] 0 (sum x => MkPair (sum + x) sum) = MkPair 6 [0, 1, 3] := rfl

-- `List.get`, the element at an index if there is one: it is `Some` exactly
-- within the list, what it finds is an element, and it goes through `map`,
-- `zipWith`, `append` and `take`. (`List.getOrGet`, std/List/Index.sw, is
-- `List.getOr` from it.)

-- `get` finds something exactly when the index is within the list.
theorem List.isSomeGet: (xs: List a) → (k: Nat) → Option.isSome (List.get xs k) = Nat.leq (Succ k) (List.length xs)
  | Nil, k => rfl
  | Cons x xs, Zero => rfl
  | Cons x xs, Succ k => List.isSomeGet xs k

theorem List.getInRange (xs: List a) (k: Nat): k < List.length xs ↔ Option.isSome (List.get xs k) = True := {
  forward = h => Eq.trans (List.isSomeGet xs k) h,
  backward = h => Eq.trans (Eq.sym (List.isSomeGet xs k)) h
}

-- Past the end, `get` finds nothing.
theorem List.getPast: (xs: List a) → (k: Nat) → List.length xs ≤ k → List.get xs k = None
  | Nil, k, h => rfl
  | Cons x xs, Zero, h => Void.exfalso (Bool.falseNotTrue h)
  | Cons x xs, Succ k, h => List.getPast xs k h

-- What `get` finds is an element of the list.
theorem List.memOfGet: (xs: List a) → (k: Nat) → (v: a) → List.get xs k = Some v → v ∈ xs
  | Nil, k, v, h => Void.exfalso (Option.noneNotSome v h)
  | Cons x xs, Zero, v, h => Inl (Option.someInjective x v h)
  | Cons x xs, Succ k, v, h => Inr (List.memOfGet xs k v h)

theorem List.getMap: (xs: List a) → (f: a → b) → (k: Nat) → List.get (List.map xs f) k = Option.map (List.get xs k) f
  | Nil, f, k => rfl
  | Cons x xs, f, Zero => rfl
  | Cons x xs, f, Succ k => List.getMap xs f k

-- Each element with its index: as long as the list, and element k is the
-- list's element k with k (counted from `start`).
theorem List.lengthWithIndexFrom: (start: Nat) → (xs: List a) → List.length (List.withIndexFrom start xs) = List.length xs
  | start, Nil => rfl
  | start, Cons x xs => Eq.cong Succ (List.lengthWithIndexFrom (Succ start) xs)

theorem List.lengthWithIndex (xs: List a): List.length (List.withIndex xs) = List.length xs := List.lengthWithIndexFrom 0 xs

theorem List.getWithIndexFrom: (start: Nat) → (xs: List a) → (k: Nat) →
    List.get (List.withIndexFrom start xs) k = Option.map (List.get xs k) (x => MkPair (start + k) x)
  | start, Nil, k => rfl
  | start, Cons x xs, Zero => rewrite Nat.addZero start in rfl
  | start, Cons x xs, Succ k => rewrite Nat.addSucc start k in List.getWithIndexFrom (Succ start) xs k

theorem List.getWithIndex (xs: List a) (k: Nat): List.get (List.withIndex xs) k = Option.map (List.get xs k) (x => MkPair k x) :=
  List.getWithIndexFrom 0 xs k

-- `mapWithIndex` keeps the length, and element k is `f k` of the list's
-- element k.
theorem List.lengthMapWithIndex (xs: List a) (f: Nat → a → b): List.length (List.mapWithIndex xs f) = List.length xs :=
  Eq.trans (List.lengthMap (List.withIndex xs) (pair => f pair.fst pair.snd)) (List.lengthWithIndex xs)

theorem List.getMapWithIndex (xs: List a) (f: Nat → a → b) (k: Nat): List.get (List.mapWithIndex xs f) k = Option.map (List.get xs k) (f k) :=
  let mapped: List.get (List.mapWithIndex xs f) k = Option.map (Option.map (List.get xs k) (x => MkPair k x)) (pair => f pair.fst pair.snd) :=
    rewrite <- List.getWithIndex xs k in List.getMap (List.withIndex xs) (pair => f pair.fst pair.snd) k
  rewrite mapped in
    match List.get xs k with
      | None => rfl
      | Some x => rfl

-- `zipWith` has `f x y` where both lists have an element, `x` and `y`.
theorem List.getZipWith (f: a → b → c): (xs: List a) → (ys: List b) → (k: Nat) →
    List.get (List.zipWith xs ys f) k = Option.flatMap (List.get xs k) (x => Option.map (List.get ys k) (f x))
  | Nil, ys, k => rfl
  | Cons x xs, Nil, Zero => rfl
  | Cons x xs, Nil, Succ k =>
    match c: List.get xs k with
      | None => rfl
      | Some u => rfl
  | Cons x xs, Cons y ys, Zero => rfl
  | Cons x xs, Cons y ys, Succ k => List.getZipWith f xs ys k

-- `zip`, `zipWith3` and `zipWith4` have the combined elements where every
-- list has one.
theorem List.getZip: (xs: List a) → (ys: List b) → (k: Nat) → List.get (List.zip xs ys) k = Option.map2 MkPair (List.get xs k) (List.get ys k)
  | Nil, ys, k => rfl
  | Cons x xs, Nil, k => Eq.sym (Option.map2None MkPair _)
  | Cons x xs, Cons y ys, Zero => rfl
  | Cons x xs, Cons y ys, Succ k => List.getZip xs ys k

theorem List.getZipWith3 (f: a → b → c → d): (xs: List a) → (ys: List b) → (zs: List c) → (k: Nat) →
    List.get (List.zipWith3 xs ys zs f) k = Option.map3 f (List.get xs k) (List.get ys k) (List.get zs k)
  | Nil, ys, zs, k => rfl
  | Cons x xs, Nil, zs, k => Eq.sym (Option.map3None2 f _ _)
  | Cons x xs, Cons y ys, Nil, k => Eq.sym (Option.map3None3 f _ _)
  | Cons x xs, Cons y ys, Cons z zs, Zero => rfl
  | Cons x xs, Cons y ys, Cons z zs, Succ k => List.getZipWith3 f xs ys zs k

theorem List.getZipWith4 (f: a → b → c → d → e): (xs: List a) → (ys: List b) → (zs: List c) → (ws: List d) → (k: Nat) →
    List.get (List.zipWith4 xs ys zs ws f) k = Option.map4 f (List.get xs k) (List.get ys k) (List.get zs k) (List.get ws k)
  | Nil, ys, zs, ws, k => rfl
  | Cons x xs, Nil, zs, ws, k => Eq.sym (Option.map4None2 f _ _ _)
  | Cons x xs, Cons y ys, Nil, ws, k => Eq.sym (Option.map4None3 f _ _ _)
  | Cons x xs, Cons y ys, Cons z zs, Nil, k => Eq.sym (Option.map4None4 f _ _ _)
  | Cons x xs, Cons y ys, Cons z zs, Cons w ws, Zero => rfl
  | Cons x xs, Cons y ys, Cons z zs, Cons w ws, Succ k => List.getZipWith4 f xs ys zs ws k

theorem List.getZipWith3Example: List.get (List.zipWith3 [1, 2] [10, 20, 30] [100, 200] (x y z => x + y + z)) 1 = Some 222 := rfl

-- `append`: the first list's element, else the second's, counting on from
-- the end of the first.
theorem List.getAppend: (xs: List a) → (ys: List a) → (k: Nat) →
    List.get (List.append xs ys) k = Option.orElse (List.get xs k) (List.get ys (k - List.length xs))
  | Nil, ys, k => rfl
  | Cons x xs, ys, Zero => rfl
  | Cons x xs, ys, Succ k => List.getAppend xs ys k

theorem List.getAppendLeft: (xs: List a) → (ys: List a) → (k: Nat) → k < List.length xs → List.get (List.append xs ys) k = List.get xs k
  | Nil, ys, k, h => Void.exfalso (Bool.falseNotTrue h)
  | Cons x xs, ys, Zero, h => rfl
  | Cons x xs, ys, Succ k, h => List.getAppendLeft xs ys k h

theorem List.getAppendRight: (xs: List a) → (ys: List a) → (k: Nat) → List.length xs ≤ k →
    List.get (List.append xs ys) k = List.get ys (k - List.length xs)
  | Nil, ys, k, h => rfl
  | Cons x xs, ys, Zero, h => Void.exfalso (Bool.falseNotTrue h)
  | Cons x xs, ys, Succ k, h => List.getAppendRight xs ys k h

-- `take n` keeps the elements before `n`, and nothing from `n` on.
theorem List.getTake: (xs: List a) → (n: Nat) → (k: Nat) → k < n → List.get (List.take xs n) k = List.get xs k
  | xs, Zero, k, h => Void.exfalso (Bool.falseNotTrue h)
  | Nil, Succ n, k, h => rfl
  | Cons x xs, Succ n, Zero, h => rfl
  | Cons x xs, Succ n, Succ k, h => List.getTake xs n k h

theorem List.getTakePast: (xs: List a) → (n: Nat) → (k: Nat) → n ≤ k → List.get (List.take xs n) k = None
  | xs, Zero, k, h => rfl
  | Nil, Succ n, k, h => rfl
  | Cons x xs, Succ n, Zero, h => Void.exfalso (Bool.falseNotTrue h)
  | Cons x xs, Succ n, Succ k, h => List.getTakePast xs n k h

-- Index j after dropping k is index k + j before.
theorem List.getDrop: (xs: List a) → (k: Nat) → (j: Nat) → List.get (List.drop xs k) j = List.get xs (k + j)
  | xs, Zero, j => rfl
  | Nil, Succ k, j => rfl
  | Cons x xs, Succ k, j => List.getDrop xs k j

-- Entry k of the running accumulations is the fold of the first k
-- elements (`List.getOrScanLeft`, std/List/Index.sw, with a fallback).
theorem List.getScanLeft (f: b → a → b): (xs: List a) → (z: b) → (k: Nat) → k ≤ List.length xs →
    List.get (List.scanLeft xs z f) k = Some (List.foldLeft (List.take xs k) z f)
  | Nil, z, Zero, h => rfl
  | Nil, z, Succ k, h => Void.exfalso (Bool.falseNotTrue h)
  | Cons x xs, z, Zero, h => rfl
  | Cons x xs, z, Succ k, h => List.getScanLeft f xs (f z x) k h

-- Element k of each element beside the running accumulations is `g` of
-- element k and the fold of the elements before it, and nothing past the end.
theorem List.getZipWithScanLeft (f: b → a → b) (g: a → b → c): (xs: List a) → (z: b) → (k: Nat) →
    List.get (List.zipWith xs (List.scanLeft xs z f) g) k = Option.map (List.get xs k) (x => g x (List.foldLeft (List.take xs k) z f))
  | Nil, z, k => rfl
  | Cons x xs, z, Zero => rfl
  | Cons x xs, z, Succ k => List.getZipWithScanLeft f g xs (f z x) k

theorem List.getExample: List.get (List.append [1, 2] (List.map [3, 4] Succ)) 3 = Some 5 := rfl

-- For any list of successors, what `get` finds is not zero.
theorem List.getMapExample (xs: List Nat) (k: Nat) (v: Nat) (h: List.get (List.map xs Succ) k = Some v): Not (v = 0) :=
  Option.mapEqSome (List.get xs k) Succ v (Eq.trans (Eq.sym (List.getMap xs Succ k)) h) (u found e => rewrite <- e in Nat.succNotZero u)
