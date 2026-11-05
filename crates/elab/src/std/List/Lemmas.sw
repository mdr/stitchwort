--| Lemmas about the list toolkit's functions (List/Toolkit.sw): lengths, sums
--| and counts, membership, permutations, congruence, `get`, and the like, with
--| the examples and tests that use them.

theorem List.lengthAppend: (xs: List a) → (ys: List a) → List.length (List.append xs ys) = List.length xs + List.length ys
  | [], ys => rfl
  | [x, ..xs], ys => Eq.cong Succ (List.lengthAppend xs ys)

--| The loop the runtimes run for `List.length` counts the same.
theorem List.lengthOntoEq: (xs: List a) → (n: Nat) → List.lengthOnto xs n = n + List.length xs
  | [], n => Eq.sym (Nat.addZero n)
  | [x, ..xs], n => Eq.trans (List.lengthOntoEq xs (Succ n)) (Eq.sym (Nat.addSucc n (List.length xs)))

--| Splitting a list at `n` and joining the parts gives it back.
theorem List.appendTakeDrop: (xs: List a) → (n: Nat) → List.append (List.take xs n) (List.drop xs n) = xs
  | xs, Zero => rfl
  | [], Succ n => rfl
  | [x, ..xs], Succ n => Eq.cong (Cons x) (List.appendTakeDrop xs n)

theorem List.scanLeftNil: List.scanLeft [] 5 (acc x => acc + x) = [5] := rfl

theorem List.scanLeftSums: List.scanLeft [1, 2, 3] 0 (acc x => acc + x) = [0, 1, 3, 6] := rfl

theorem List.foldLeftReverseOnto: (xs: List a) → (acc: List a) → (z: b) → (f: a → b → b) →
    List.foldLeft (List.reverseOnto xs acc) z (r x => f x r)
      = List.foldLeft acc (List.foldLeft (List.reverseOnto xs []) z (r x => f x r)) (r x => f x r)
  | [], acc, z, f => rfl
  | [x, ..xs], acc, z, f =>
    Eq.trans (List.foldLeftReverseOnto xs [x, ..acc] z f)
      (Eq.sym (Eq.cong (r => List.foldLeft acc r (r2 y => f y r2)) (List.foldLeftReverseOnto xs [x] z f)))

--| The step of the right fold, which the loop form hides.
theorem List.foldRightCons (xs: List a) (x: a) (z: b) (f: a → b → b): List.foldRight [x, ..xs] z f = f x (List.foldRight xs z f) :=
  List.foldLeftReverseOnto xs [x] z f

theorem List.sumByDoubles: List.sumBy [1, 2, 3] (x => x * 2) = 12 := rfl

theorem List.sumInts: List.sum [(3: Int), -5, 1] = -1 := rfl

theorem List.sumByInts: List.sumBy [(1: Int), 2, 3] (x => Int.sub 1 x) = -3 := rfl

--| A sum is a `sumBy` of each element itself.
theorem List.sumIsSumBy [auto add: Add a] (xs: List a): List.sum xs = List.sumBy xs (x => x) := rfl

theorem List.zipWithNextExample: List.zipWithNext [1, 2, 3] = [MkPair 1 2, MkPair 2 3] := rfl

--| One pair fewer than there are elements.
theorem List.lengthZipWithNext: (xs: List a) → List.length (List.zipWithNext xs) = List.length xs - 1
  | [] => rfl
  | [x] => rfl
  | [x, next, ..rest] => rewrite List.lengthZipWithNext [next, ..rest]

--| The list zipped with its own tail.
theorem List.zipWithNextZip: (xs: List a) → List.zipWithNext xs = List.zip xs (List.tailOf xs)
  | [] => rfl
  | [x] => rfl
  | [x, next, ..rest] => rewrite List.zipWithNextZip [next, ..rest]

theorem List.chainEmpty (holds: a → a → Bool): List.chain [] holds = True := rfl

theorem List.chainSingle (x: a) (holds: a → a → Bool): List.chain [x] holds = True := rfl

theorem List.chainCons (x: a) (next: a) (rest: List a) (holds: a → a → Bool):
    List.chain [x, next, ..rest] holds = (holds x next ∧ List.chain [next, ..rest] holds) := rfl

--| `holds` is true of every pair `zipWithNext` gives.
theorem List.chainZipWithNext: (xs: List a) → (holds: a → a → Bool) →
    List.chain xs holds = (List.zipWithNext xs |> .all (pair => holds pair.fst pair.snd))
  | [], holds => rfl
  | [x], holds => rfl
  | [x, next, ..rest], holds => rewrite List.chainZipWithNext [next, ..rest] holds in rfl

--| Without the first element, it still holds.
theorem List.chainTail: (xs: List a) → (holds: a → a → Bool) → List.chain xs holds = True → List.chain (List.tailOf xs) holds = True
  | [], holds, chained => rfl
  | [x], holds, chained => rfl
  | [x, next, ..rest], holds, chained => Bool.andRight _ _ chained

--| Without the last element (`List.init`), it still holds.
theorem List.chainInit: (xs: List a) → (holds: a → a → Bool) → List.chain xs holds = True → List.chain (List.init xs) holds = True
  | [], holds, chained => rfl
  | [x, ..rest], holds, chained => List.chainInitCons x rest holds chained

theorem List.chainInitCons: (x: a) → (rest: List a) → (holds: a → a → Bool) →
    List.chain [x, ..rest] holds = True → List.chain (List.init [x, ..rest]) holds = True
  | x, [], holds, chained => rfl
  | x, [next], holds, chained => rfl
  | x, [next, after, ..more], holds, chained =>
    let first := Bool.andLeft _ _ chained
    let kept := List.chainInitCons next [after, ..more] holds (Bool.andRight _ _ chained)
    Bool.andIntro _ _ first kept

--| A `chain` of two tests together holds when the chain of each one does.
theorem List.chainAnd: (xs: List a) → (holds1: a → a → Bool) → (holds2: a → a → Bool) →
    List.chain xs (x y => holds1 x y ∧ holds2 x y) = (List.chain xs holds1 ∧ List.chain xs holds2)
  | [], holds1, holds2 => rfl
  | [x], holds1, holds2 => rfl
  | [x, next, ..rest], holds1, holds2 =>
    rewrite List.chainAnd [next, ..rest] holds1 holds2 in cases

--| `all` over a cons: the head's answer, then the rest's.
theorem List.allCons (p: a → Bool) (x: a) (xs: List a): List.all [x, ..xs] p = (p x ∧ List.all xs p) := rfl

--| `any` over a cons: the head's answer, then the rest's.
theorem List.anyCons (p: a → Bool) (x: a) (xs: List a): List.any [x, ..xs] p = (p x ∨ List.any xs p) := rfl

--| A run of `a + b` numbers is a run of `a` followed by a run of `b`.
theorem List.rangeFromAppend: (a: Nat) → (b: Nat) → (s: Nat) → List.rangeFrom (a + b) s = List.append (List.rangeFrom a s) (List.rangeFrom b (s + a))
  | Zero, b, s => Eq.cong (t => List.rangeFrom b t) (Eq.sym (Nat.addZero s))
  | Succ a, b, s =>
    Eq.cong (Cons s) (Eq.trans (List.rangeFromAppend a b (Succ s)) (Eq.cong (t => List.append (List.rangeFrom a (Succ s)) (List.rangeFrom b t)) (Eq.sym (Nat.addSucc s a))))

--| `List.range a b` has `b - a` elements: none when `b ≤ a`.
theorem List.lengthRange (a: Nat) (b: Nat): List.length (List.range a b) = b - a := List.lengthRangeFrom (b - a) a

test "List.lengthRange" := List.length (List.range 3 4) == 1 ∧ List.length (List.range 5 3) == 0 ∧ List.length (List.range 2 7) == 5

--| A range whose end is not past its start is empty.
theorem List.rangeEmpty (a: Nat) (b: Nat) (h: b ≤ a): List.range a b = [] :=
  Eq.cong (t => List.rangeFrom t a) (omega: b - a = 0)

--| A non-empty range is its first number and the range from the next one.
theorem List.rangeCons (a: Nat) (b: Nat) (h: a < b): List.range a b = [a, ..List.range (a + 1) b] :=
  Eq.cong (t => List.rangeFrom t a) (omega: b - a = Succ (b - (a + 1)))

--| Ranges that meet end to end join into one.
theorem List.rangeAppend (a: Nat) (b: Nat) (c: Nat) (ab: a ≤ b) (bc: b ≤ c): List.range a b ++ List.range b c = List.range a c :=
  Eq.trans (Eq.cong (t => List.append (List.rangeFrom (b - a) a) (List.rangeFrom (c - b) t)) (Eq.sym (omega: a + (b - a) = b)))
    (Eq.trans (Eq.sym (List.rangeFromAppend (b - a) (c - b) a)) (Eq.cong (t => List.rangeFrom t a) (omega: (b - a) + (c - b) = c - a)))

--| A range that includes its end is the range before the end, then the end.
theorem List.rangeSnoc (a: Nat) (b: Nat) (h: a ≤ b): List.range a (b + 1) = [..List.range a b, b] :=
  Eq.trans (Eq.sym (List.rangeAppend a b (b + 1) h (omega)))
    (Eq.cong (t => List.append (List.range a b) t) (Eq.cong (t => List.rangeFrom t b) (omega: b + 1 - b = 1)))

theorem List.headExample: List.head [3, 4] = Some 3 := rfl

theorem List.headEmpty: List.head ([]: List Nat) = None := rfl

theorem List.initExample: List.init [1, 2, 3] = [1, 2] := rfl

theorem List.initEmpty: List.init ([]: List Nat) = [] := rfl

--| The loop's sides are the two `filter`s, each after what it had sorted.
theorem List.partitionOntoFilters (p: a → Bool): (xs: List a) → (kept: List a) → (dropped: List a) →
    List.partitionOnto p xs (MkPair kept dropped)
      = MkPair (List.reverseOnto kept (List.filter xs p)) (List.reverseOnto dropped (List.filter xs (x => ¬(p x))))
  | [], kept, dropped => rfl
  | [x, ..xs], kept, dropped =>
    match p x with
      | True => List.partitionOntoFilters p xs [x, ..kept] dropped
      | False => List.partitionOntoFilters p xs kept [x, ..dropped]

--| `partition` is the two `filter`s.
-- (its definition before it became one pass)
theorem List.partitionFilters (xs: List a) (p: a → Bool): List.partition xs p = MkPair (List.filter xs p) (List.filter xs (x => ¬(p x))) :=
  List.partitionOntoFilters p xs [] []

theorem List.partitionExample: List.partition [1, 5, 2, 7] (x => x > 4) = MkPair [5, 7] [1, 2] := rfl

theorem List.lengthReplicate (x: a): (n: Nat) → List.length (List.replicate n x) = n
  | Zero => rfl
  | Succ n => Eq.cong Succ (List.lengthReplicate x n)

--| Padding makes a list exactly n long, when it was no longer than that.
theorem List.padRightLength (xs: List a) (n: Nat) (x: a) (h: List.length xs ≤ n):
    List.length (List.padRight xs n x) = n :=
  Eq.trans (List.lengthAppend xs (List.replicate (n - List.length xs) x))
    (Eq.trans (Eq.cong (t => List.length xs + t) (List.lengthReplicate x (n - List.length xs)))
      (Nat.addSubCancel (List.length xs) n h))

theorem List.padRightExample: List.padRight [1, 2] 4 0 = [1, 2, 0, 0] := rfl

theorem List.padRightLongEnough: List.padRight [1, 2] 1 0 = [1, 2] := rfl

-- Lemmas about `List.transpose`: it has as many columns as the first row is
-- long, and for a rectangular list, doing it twice gives back the list.

--| `map` keeps the length.
theorem List.lengthMap: (xs: List a) → (f: a → b) → List.length (List.map xs f) = List.length xs
  | [], f => rfl
  | [x, ..xs], f => Eq.cong Succ (List.lengthMap xs f)

theorem List.transposeExample: List.transpose [[1, 2, 3], [4, 5, 6]] = [[1, 4], [2, 5], [3, 6]] := rfl

theorem List.transposeNone: List.transpose ([]: List (List Nat)) = [] := rfl

theorem List.transposeShortRow: List.transpose [[1, 2], [3], [4, 5]] = [[1, 3, 4], [2, 5]] := rfl

theorem List.transposeNLength: (n: Nat) → (rows: List (List a)) → List.length (List.transposeN n rows) = n
  | Zero, rows => rfl
  | Succ n, rows => Eq.cong Succ (List.transposeNLength n (List.map rows (.drop 1)))

theorem List.allAppend (p: a → Prop): (xs: List a) → (ys: List a) → List.All p xs → List.All p ys → List.All p (List.append xs ys)
  | [], ys, hx, hy => hy
  | [x, ..xs], ys, Both hx hxs, hy => Both hx (List.allAppend p xs ys hxs hy)

theorem List.allAppendLeft (p: a → Prop): (xs: List a) → (ys: List a) → List.All p (List.append xs ys) → List.All p xs
  | [], ys, h => Trivial
  | [x, ..xs], ys, Both h hxs => Both h (List.allAppendLeft p xs ys hxs)

theorem List.allAppendRight (p: a → Prop): (xs: List a) → (ys: List a) → List.All p (List.append xs ys) → List.All p ys
  | [], ys, h => h
  | [x, ..xs], ys, Both h hxs => List.allAppendRight p xs ys hxs

theorem List.allMap: (xs: List a) → (p: b → Prop) → (f: a → b) → List.All (x => p (f x)) xs → List.All p (List.map xs f)
  | [], p, f, h => Trivial
  | [x, ..xs], p, f, Both h hxs => Both h (List.allMap xs p f hxs)

theorem List.allImplies (p: a → Prop) (q: a → Prop) (h: (x: a) → p x → q x): (xs: List a) → List.All p xs → List.All q xs
  | [], hp => Trivial
  | [x, ..xs], Both hpx hpxs => Both (h x hpx) (List.allImplies p q h xs hpxs)

theorem List.anyAppendLeft (p: a → Prop): (xs: List a) → (ys: List a) → List.Any p xs → List.Any p (List.append xs ys)
  | [], ys, h => Void.exfalso h
  | [x, ..xs], ys, Inl h => Inl h
  | [x, ..xs], ys, Inr h => Inr (List.anyAppendLeft p xs ys h)

theorem List.anyAppendRight (p: a → Prop): (xs: List a) → (ys: List a) → List.Any p ys → List.Any p (List.append xs ys)
  | [], ys, h => h
  | [x, ..xs], ys, h => Inr (List.anyAppendRight p xs ys h)

--| `List.any` of two lists joined: either list has one.
theorem List.anyAppend: (xs: List a) → (ys: List a) → (p: a → Bool) → List.any (List.append xs ys) p = (List.any xs p ∨ List.any ys p)
  | [], ys, p => rfl
  | [x, ..xs], ys, p =>
    match e: p x with
      | True => rfl
      | False => List.anyAppend xs ys p

theorem List.anyAppendExample: List.any (List.append [1, 2] [3]) (x => x == 3) = (False ∨ True) := rfl

theorem List.lengthZero: (xs: List a) → List.length xs = 0 → xs = []
  | [], h => rfl
  | [y, ..ys], h => Void.exfalso (Nat.succNotZero (List.length ys) h)

theorem List.transposeNNil: (n: Nat) → List.transposeN n ([]: List (List a)) = List.replicate n []
  | Zero => rfl
  | Succ n => Eq.cong (Cons []) (List.transposeNNil n)

theorem List.allLengthZero: (rows: List (List a)) → (n: Nat) → List.length rows = n → List.AllLength 0 rows →
    rows = List.replicate n []
  | [], n, hl, hr => J (y q => ([]: List (List a)) = List.replicate y ([]: List a)) rfl hl
  | [r, ..rs], Zero, hl, hr => Void.exfalso (Nat.succNotZero (List.length rs) hl)
  | [r, ..rs], Succ m, hl, Both hr hrs =>
    Eq.trans (Eq.cong (t => [t, ..rs]) (List.lengthZero r hr))
      (Eq.cong (Cons []) (List.allLengthZero rs m (Nat.succInjective (List.length rs) m hl) hrs))

theorem List.tailsAllLength: (rows: List (List a)) → (k: Nat) → List.AllLength (Succ k) rows →
    List.AllLength k (List.map rows (.drop 1))
  | [], k, hr => Trivial
  | [[], ..rs], k, Both hr hrs => Void.exfalso (Nat.zeroNotSucc k hr)
  | [[y, ..ys], ..rs], k, Both hr hrs => Both (Nat.succInjective (List.length ys) k hr) (List.tailsAllLength rs k hrs)

theorem List.headsLength: (rows: List (List a)) → (k: Nat) → List.AllLength (Succ k) rows →
    List.length (List.filterMap rows (.get 0)) = List.length rows
  | [], k, hr => rfl
  | [[], ..rs], k, Both hr hrs => Void.exfalso (Nat.zeroNotSucc k hr)
  | [[y, ..ys], ..rs], k, Both hr hrs => Eq.cong Succ (List.headsLength rs k hrs)

theorem List.rowsAreHeadsAndTails: (rows: List (List a)) → (k: Nat) → List.AllLength (Succ k) rows →
    rows = List.zipWith (List.filterMap rows (.get 0)) (List.map rows (.drop 1)) Cons
  | [], k, hr => rfl
  | [[], ..rs], k, Both hr hrs => Void.exfalso (Nat.zeroNotSucc k hr)
  | [[y, ..ys], ..rs], k, Both hr hrs => Eq.cong (Cons [y, ..ys]) (List.rowsAreHeadsAndTails rs k hrs)

theorem List.columnsAllLength: (w: Nat) → (rows: List (List a)) → (h: Nat) → List.length rows = h → List.AllLength w rows →
    List.AllLength h (List.transposeN w rows)
  | Zero, rows, h, hl, hr => Trivial
  | Succ k, rows, h, hl, hr =>
    Both (Eq.trans (List.headsLength rows k hr) hl)
      (List.columnsAllLength k (List.map rows (.drop 1)) h (Eq.trans (List.lengthMap rows (.drop 1)) hl) (List.tailsAllLength rows k hr))

theorem List.transposeNCons: (heads: List a) → (h: Nat) → (cols: List (List a)) → List.length heads = h → List.AllLength h cols →
    List.transposeN h [heads, ..cols] = List.zipWith heads (List.transposeN h cols) Cons
  | [], Zero, cols, hl, hc => rfl
  | [x, ..xs], Zero, cols, hl, hc => Void.exfalso (Nat.succNotZero (List.length xs) hl)
  | [], Succ m, cols, hl, hc => Void.exfalso (Nat.zeroNotSucc m hl)
  | [x, ..xs], Succ m, cols, hl, hc =>
    Eq.cong (Cons [x, ..List.filterMap cols (.get 0)])
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

--| There are as many columns as the first row is long.
theorem List.transposeLength (rows: List (List a)): List.length (List.transpose rows) = List.length (List.headOr rows []) :=
  List.transposeNLength (List.length (List.headOr rows [])) rows

--| Transposing a rectangular list (every row the same non-zero length) twice
--| gives the list back. (With rows of length 0, the first transpose is empty
--| and the rows are lost.)
theorem List.transposeTwice (k: Nat): (rows: List (List a)) → List.AllLength (Succ k) rows →
    List.transpose (List.transpose rows) = rows
  | [], hr => rfl
  | [r, ..rs], Both hr hrs =>
    J (y q => List.transposeN (List.length (List.headOr (List.transposeN y [r, ..rs]) [])) (List.transposeN y [r, ..rs]) = [r, ..rs])
      (List.transposeNTwice (Succ k) (List.length (List.headOr (List.transposeN (Succ k) [r, ..rs]) [])) [r, ..rs]
        (Eq.sym (List.headsLength [r, ..rs] k (Both hr hrs))) (Both hr hrs))
      (Eq.sym hr)

-- Sums from a starting total, and one element at a time, for any `Add`:
-- the laws `zeroAdd`, `assoc` and `comm`.
-- (docs/proposals/interfaces.md §7.7)

--| Adding zero on the right changes nothing, for any `Add`.
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
  | [], z, f => Eq.sym (Add.addZero z)
  | [x, ..xs], z, f =>
    calc List.foldLeft xs (z + f x) (acc x => acc + f x)
      _ = (z + f x) + List.sumBy xs f := List.sumByFrom xs (z + f x) f
      _ = z + (f x + List.sumBy xs f) := add.assoc z (f x) (List.sumBy xs f)
      _ = z + List.foldLeft xs (f x) (acc x => acc + f x) := Eq.cong (t => z + t) (Eq.sym (List.sumByFrom xs (f x) f))
      _ = z + List.sumBy [x, ..xs] f := Eq.cong (t => z + List.foldLeft xs t (acc x => acc + f x)) (Eq.sym (add.zeroAdd (f x)))

theorem List.sumByCons [auto add: Add b] (xs: List a) (x: a) (f: a → b): List.sumBy [x, ..xs] f = f x + List.sumBy xs f :=
  Eq.trans (Eq.cong (t => List.foldLeft xs t (acc x => acc + f x)) (add.zeroAdd (f x))) (List.sumByFrom xs (f x) f)

theorem List.sumByAppend [auto add: Add b] (xs: List a) (ys: List a) (f: a → b): List.sumBy (List.append xs ys) f = List.sumBy xs f + List.sumBy ys f :=
  Eq.trans (List.foldLeftAppend xs Add.zero ys (acc x => acc + f x)) (List.sumByFrom ys (List.sumBy xs f) f)

theorem List.filterKeep (xs: List a) (p: a → Bool) (x: a) (h: p x = True): List.filter [x, ..xs] p = [x, ..List.filter xs p] :=
  J (c q => List.filterStep x (List.filter xs p) c = [x, ..List.filter xs p]) rfl (Eq.sym h)

theorem List.filterSkip (xs: List a) (p: a → Bool) (x: a) (h: p x = False): List.filter [x, ..xs] p = List.filter xs p :=
  J (c q => List.filterStep x (List.filter xs p) c = List.filter xs p) rfl (Eq.sym h)

theorem List.foldLeftAppend: (xs: List a) → (z: b) → (ys: List a) → (f: b → a → b) →
    List.foldLeft (List.append xs ys) z f = List.foldLeft ys (List.foldLeft xs z f) f
  | [], z, ys, f => rfl
  | [x, ..xs], z, ys, f => List.foldLeftAppend xs (f z x) ys f

-- Appending and taking; sums of `Nat.keepIf` terms, which pick out some
-- elements; swapping two sums; sums and `any` over a run `s .. s + c` that
-- pick nothing or exactly one element.

--| Appending the empty list changes nothing.
theorem List.appendNil: (xs: List a) → List.append xs [] = xs
  | [] => rfl
  | [x, ..xs] => Eq.cong (Cons x) (List.appendNil xs)

--| Appending to a list that isn't empty, or appending one that isn't, gives
--| a list that isn't empty.
theorem List.appendNotNilLeft: (xs: List a) → (ys: List a) → xs ≠ [] → List.append xs ys ≠ []
  | [], ys, some, empty => some rfl
  | [x, ..rest], ys, some, empty => List.consNotNil x (List.append rest ys) empty

theorem List.appendNotNilRight: (xs: List a) → (ys: List a) → ys ≠ [] → List.append xs ys ≠ []
  | [], ys, some, empty => some empty
  | [x, ..rest], ys, some, empty => List.consNotNil x (List.append rest ys) empty

--| Appending is associative: `(xs ++ ys) ++ zs = xs ++ (ys ++ zs)`.
theorem List.appendAssoc: (xs: List a) → (ys: List a) → (zs: List a) → List.append (List.append xs ys) zs = List.append xs (List.append ys zs)
  | [], ys, zs => rfl
  | [x, ..xs], ys, zs => Eq.cong (Cons x) (List.appendAssoc xs ys zs)

-- `List.count` is a fold with an accumulator; `List.occurrences` recurses on
-- the list, which suits proofs. They agree, so the lemmas below are stated
-- for `List.count` (the program's) and proved through `List.occurrences`.
-- Also here: counting and `List.scanLeft` over `++`, and permutations.

--| Rearranging sums, for the counting lemmas below.
theorem Nat.addRotate (a: Nat) (b: Nat) (c: Nat): (a + b) + c = b + (a + c) := Eq.trans (Eq.cong (t => t + c) (Nat.addComm a b)) (Nat.addAssoc b a c)

theorem Nat.addLeftComm (a: Nat) (b: Nat) (c: Nat): a + (b + c) = b + (a + c) := Eq.trans (Eq.sym (Nat.addAssoc a b c)) (Nat.addRotate a b c)

theorem List.countStep: (b: Bool) → (k: Nat) → (o: Nat) → Nat.succIf k b + o = k + (Bool.toNat b + o)
  | True, k, o => Eq.sym (Nat.addSucc k o)
  | False, k, o => rfl

theorem List.countFold: (xs: List a) → (k: Nat) → (p: a → Bool) →
    List.foldLeft xs k (n x => Nat.succIf n (p x)) = k + List.occurrences xs p
  | [], k, p => Eq.sym (Nat.addZero k)
  | [x, ..xs], k, p => Eq.trans (List.countFold xs (Nat.succIf k (p x)) p) (List.countStep (p x) k (List.occurrences xs p))

theorem List.countOccurrences (xs: List a) (p: a → Bool): List.count xs p = List.occurrences xs p := List.countFold xs 0 p

theorem List.occurrencesSumBy: (xs: List a) → (p: a → Bool) → List.occurrences xs p = List.sumBy xs (x => Bool.toNat (p x))
  | [], p => rfl
  | [x, ..xs], p => rewrite List.sumByCons xs x (x => Bool.toNat (p x)), List.occurrencesSumBy xs p

--| A count is a sum of 1s and 0s, so the sum lemmas apply to it.
theorem List.countSumBy (xs: List a) (p: a → Bool): List.count xs p = List.sumBy xs (x => Bool.toNat (p x)) :=
  Eq.trans (List.countOccurrences xs p) (List.occurrencesSumBy xs p)

theorem List.occurrencesAppend: (xs: List a) → (ys: List a) → (p: a → Bool) →
    List.occurrences (List.append xs ys) p = List.occurrences xs p + List.occurrences ys p
  | [], ys, p => rfl
  | [x, ..xs], ys, p =>
    Eq.trans (Eq.cong (t => Bool.toNat (p x) + t) (List.occurrencesAppend xs ys p))
      (Eq.sym (Nat.addAssoc (Bool.toNat (p x)) (List.occurrences xs p) (List.occurrences ys p)))

theorem List.countNil (p: a → Bool): List.count [] p = 0 := rfl

theorem List.countCons (xs: List a) (x: a) (p: a → Bool): List.count [x, ..xs] p = Bool.toNat (p x) + List.count xs p :=
  Eq.trans (List.countOccurrences [x, ..xs] p) (Eq.cong (n => Bool.toNat (p x) + n) (Eq.sym (List.countOccurrences xs p)))

theorem List.countAppend (xs: List a) (ys: List a) (p: a → Bool): List.count (List.append xs ys) p = List.count xs p + List.count ys p :=
  Eq.trans (List.countOccurrences (List.append xs ys) p)
    (Eq.trans (List.occurrencesAppend xs ys p)
      (Eq.trans (Eq.cong (n => n + List.occurrences ys p) (Eq.sym (List.countOccurrences xs p)))
        (Eq.cong (n => List.count xs p + n) (Eq.sym (List.countOccurrences ys p)))))

--| The length of a `filter` is the `count` with the same test.
theorem List.lengthFilter: (xs: List a) → (p: a → Bool) → List.length (List.filter xs p) = List.count xs p
  | [], p => rfl
  | [x, ..rest], p =>
    rewrite List.countCons rest x p, <- List.lengthFilter rest p in
      match keep: p x with
        | True => rfl
        | False => rfl

--| A count is at most the length, and so is a `filter`'s length; filtering
--| out an element that is there makes the list shorter.
theorem List.countLeLength: (xs: List a) → (p: a → Bool) → List.count xs p ≤ List.length xs
  | [], p => Nat.leRefl 0
  | [x, ..rest], p =>
    rewrite List.countCons rest x p in omega [List.countLeLength rest p, Bool.toNatLeOne (p x)]

theorem List.lengthFilterLe (xs: List a) (p: a → Bool): List.length (List.filter xs p) ≤ List.length xs :=
  rewrite List.lengthFilter xs p in List.countLeLength xs p

theorem List.lengthFilterLt (p: a → Bool) (x: a) (dropped: p x = False): (xs: List a) → x ∈ xs → List.length (List.filter xs p) < List.length xs
  | [], member => Void.exfalso member
  | [y, ..rest], Inl same => rewrite same, dropped in omega [List.lengthFilterLe rest p]
  | [y, ..rest], Inr later =>
    match p y with
      | True => List.lengthFilterLt p x dropped rest later
      | False => omega [List.lengthFilterLt p x dropped rest later]

--| An element that passes makes the count positive, and the other way
--| round, for an element counted by `== c`.
theorem List.countPositive: (xs: List a) → (p: a → Bool) → (x: a) → x ∈ xs → p x = True → 0 < List.count xs p
  | [], p, x, member, passes => Void.exfalso member
  | [y, ..rest], p, x, Inl same, passes => rewrite List.countCons rest y p, same, passes in omega
  | [y, ..rest], p, x, Inr later, passes =>
    rewrite List.countCons rest y p in omega [List.countPositive rest p x later passes]

theorem List.memOfCountPositive [auto eq: DecEq a] (c: a): (xs: List a) → 0 < List.count xs (== c) → c ∈ xs
  | [], positive => Void.exfalso (omega: Void)
  | [x, ..rest], positive =>
    match t: x == c with
      | True => Inl (DecEq.sound x c t)
      | False => Inr (List.memOfCountPositive c rest (omega [List.countCons rest x (== c)]))

--| Filtering twice is filtering once by both tests.
theorem List.filterFilter (p: a → Bool) (q: a → Bool): (xs: List a) → List.filter (List.filter xs p) q = List.filter xs (x => p x ∧ q x)
  | [] => rfl
  | [x, ..rest] => rewrite <- List.filterFilter p q rest in cases

theorem List.countFalse: (xs: List a) → List.count xs (x => False) = 0
  | [] => rfl
  | [x, ..rest] => List.countFalse rest

--| A count where no element passes is 0.
theorem List.countNone: (xs: List a) → (p: a → Bool) → ((x: a) → x ∈ xs → p x = False) → List.count xs p = 0
  | [], p, none => rfl
  | [x, ..rest], p, none =>
    rewrite List.countCons rest x p, none x (Inl rfl), List.countNone rest p (y member => none y (Inr member)) in rfl

theorem List.anyEmpty: (xs: List a) → (p: a → Bool) → List.length xs = 0 → List.any xs p = False
  | [], p, empty => rfl
  | [x, ..rest], p, empty => Void.exfalso (Nat.succNotZero (List.length rest) empty)

--| The length of a `flatMap` is the sum of the lengths of the lists it joins.
theorem List.lengthFlatMap (f: a → List b): (xs: List a) → List.length (List.flatMap xs f) = List.sumBy xs (x => List.length (f x))
  | [] => rfl
  | [x, ..rest] =>
    rewrite List.sumByCons rest x (x => List.length (f x)), <- List.lengthFlatMap f rest in
      List.lengthAppend (f x) (List.flatMap rest f)

theorem List.lengthFlatMapExample: List.length (List.flatMap [1, 2, 3] (n => List.replicate n n)) = 6 := rfl

--| Counting over a `flatMap` adds up the counts over each list it joins.
theorem List.countFlatMap (f: a → List b) (p: b → Bool): (xs: List a) →
    List.count (List.flatMap xs f) p = List.sumBy xs (x => List.count (f x) p)
  | [] => rfl
  | [x, ..rest] =>
    rewrite List.countAppend (f x) (List.flatMap rest f) p, List.sumByCons rest x (x => List.count (f x) p), List.countFlatMap f p rest
      in rfl

--| Dropping a list's start leaves what was appended to it.
theorem List.dropAppend: (start: List a) → (rest: List a) → List.drop (List.append start rest) (List.length start) = rest
  | [], rest => rfl
  | [x, ..xs], rest => List.dropAppend xs rest

--| Nothing is left of the empty list, however much is dropped.
theorem List.dropNil: (n: Nat) → List.drop ([]: List a) n = []
  | Zero => rfl
  | Succ n => rfl

--| Dropping `n + m` is dropping `n`, then `m`.
theorem List.dropAdd: (n: Nat) → (m: Nat) → (xs: List a) → List.drop xs (n + m) = List.drop (List.drop xs n) m
  | Zero, m, xs => rfl
  | Succ n, m, [] => Eq.sym (List.dropNil m)
  | Succ n, m, [x, ..xs] => List.dropAdd n m xs

--| Dropping the whole length leaves nothing.
theorem List.dropLength: (xs: List a) → List.drop xs (List.length xs) = []
  | [] => rfl
  | [x, ..xs] => List.dropLength xs

--| A list starts with what was appended to.
theorem List.startsWithAppend [auto eq: DecEq a]: (prefix: List a) → (rest: List a) → List.startsWith (List.append prefix rest) prefix = True
  | [], rest => rfl
  | [p, ..ps], rest => rewrite DecEq.refl p, List.startsWithAppend ps rest in rfl

--| A list that starts with `prefix` is `prefix`, then the rest of it.
theorem List.startsWithSplit [auto eq: DecEq a]: (xs: List a) → (prefix: List a) → List.startsWith xs prefix = True →
    List.append prefix (List.drop xs (List.length prefix)) = xs
  | xs, [], starts => rfl
  | [], [p, ..ps], starts => Void.exfalso (Bool.falseNotTrue starts)
  | [x, ..xs], [p, ..ps], starts =>
    rewrite DecEq.sound x p (Bool.andLeft _ _ starts), List.startsWithSplit xs ps (Bool.andRight _ _ starts) in rfl

--| A prefix is no longer than the list.
theorem List.startsWithLength [auto eq: DecEq a]: (xs: List a) → (prefix: List a) → List.startsWith xs prefix = True →
    List.length prefix ≤ List.length xs
  | xs, [], starts => rfl
  | [], [p, ..ps], starts => Void.exfalso (Bool.falseNotTrue starts)
  | [x, ..xs], [p, ..ps], starts => List.startsWithLength xs ps (Bool.andRight _ _ starts)

--| Appending to `prefix` gives `xs` exactly when the appended list is the
--| rest of `xs`, once `xs` starts with `prefix`.
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

--| Nothing appended to `prefix` gives a list that doesn't start with it.
theorem List.appendNotEq [auto eq: DecEq a] (xs: List a) (prefix: List a) (starts: List.startsWith xs prefix = False) (rest: List a):
    (List.append prefix rest == xs) = False :=
  match made: List.append prefix rest == xs with
    | True =>
      let startsAfter: List.startsWith xs prefix = True := rewrite <- DecEq.sound _ _ made in List.startsWithAppend prefix rest
      Void.exfalso (Bool.falseNotTrue (Eq.trans (Eq.sym starts) startsAfter))
    | False => rfl

--| Stripping what was appended to gives the rest.
theorem List.stripPrefixAppend [auto eq: DecEq a]: (prefix: List a) → (rest: List a) → List.stripPrefix (List.append prefix rest) prefix = Some rest
  | [], rest => rfl
  | [p, ..ps], rest => rewrite DecEq.refl p in List.stripPrefixAppend ps rest

--| `stripPrefix` is `startsWith`, then `drop`.
theorem List.stripPrefixStartsWith [auto eq: DecEq a]: (xs: List a) → (prefix: List a) →
    List.stripPrefix xs prefix = (if List.startsWith xs prefix then Some (List.drop xs (List.length prefix)) else None)
  | xs, [] => rfl
  | [], [p, ..ps] => rfl
  | [x, ..xs], [p, ..ps] =>
    match same: x == p with
      | True => List.stripPrefixStartsWith xs ps
      | False => rfl

--| `isEmpty` is `== []`.
theorem List.isEmptyEqNil [auto eq: DecEq a]: (xs: List a) → List.isEmpty xs = (xs == [])
  | [] => rfl
  | [x, ..xs] => rfl

--| What passes a test after a `flatMap`: what passes in each list it joins,
--| added up.
theorem List.occurrencesFlatMap (f: a → List b) (p: b → Bool): (xs: List a) →
    List.occurrences (List.flatMap xs f) p = List.sumBy xs (x => List.occurrences (f x) p)
  | [] => rfl
  | [x, ..rest] =>
    rewrite List.occurrencesAppend (f x) (List.flatMap rest f) p, List.occurrencesFlatMap f p rest,
      List.sumByCons rest x (x => List.occurrences (f x) p)
      in rfl

--| Summing 1 for each element counts them.
theorem List.sumByOne: (xs: List a) → List.sumBy xs (x => 1) = List.length xs
  | [] => rfl
  | [x, ..rest] => rewrite List.sumByCons rest x (x => 1) in Eq.cong Succ (List.sumByOne rest)

--| An element's term is at most the sum.
theorem List.memLeSumBy (f: a → Nat): (xs: List a) → (x: a) → x ∈ xs → f x ≤ List.sumBy xs f
  | [], x, none => Void.exfalso none
  | [first, ..rest], x, Inl same => rewrite List.sumByCons rest first f, same in Nat.leAddRight (f x) (List.sumBy rest f)
  | [first, ..rest], x, Inr later =>
    rewrite List.sumByCons rest first f in
      Nat.leTrans _ _ _ (List.memLeSumBy f rest x later) (Nat.leAddLeft (f first) (List.sumBy rest f))

test "List.sumByOne" := List.sumBy ["a", "b", "c"] (x => 1) == 3

theorem List.scanLeftCons: (xs: List a) → (z: b) → (f: b → a → b) → List.scanLeft xs z f = [z, ..List.drop (List.scanLeft xs z f) 1]
  | [], z, f => rfl
  | [x, ..xs], z, f => rfl

theorem List.scanLeftAppend: (xs: List a) → (z: b) → (ys: List a) → (f: b → a → b) →
    List.drop (List.scanLeft (List.append xs ys) z f) 1 = List.append (List.drop (List.scanLeft xs z f) 1) (List.drop (List.scanLeft ys (List.foldLeft xs z f) f) 1)
  | [], z, ys, f => rfl
  | [x, ..xs], z, ys, f =>
    Eq.trans (List.scanLeftCons (List.append xs ys) (f z x) f)
      (Eq.trans (Eq.cong (Cons (f z x)) (List.scanLeftAppend xs (f z x) ys f))
        (Eq.cong (l => List.append l (List.drop (List.scanLeft ys (List.foldLeft xs (f z x) f) f) 1)) (Eq.sym (List.scanLeftCons xs (f z x) f))))

theorem List.permRefl (xs: List a): List.Perm xs xs := p => rfl

theorem List.permSym (xs: List a) (ys: List a) (h: List.Perm xs ys): List.Perm ys xs := p => Eq.sym (h p)

theorem List.permTrans (xs: List a) (ys: List a) (zs: List a) (h1: List.Perm xs ys) (h2: List.Perm ys zs): List.Perm xs zs := p => Eq.trans (h1 p) (h2 p)

theorem List.occurrencesTrue: (xs: List a) → List.occurrences xs (x => True) = List.length xs
  | [] => rfl
  | [x, ..xs] => Eq.cong Succ (List.occurrencesTrue xs)

theorem List.permLength (xs: List a) (ys: List a) (h: List.Perm xs ys): List.length xs = List.length ys := Eq.trans (Eq.sym (List.occurrencesTrue xs)) (Eq.trans (h (x => True)) (List.occurrencesTrue ys))

--| Some element passes `p` exactly when at least one does, so permutations
--| agree on `any`.
theorem List.anyOccurrences: (xs: List a) → (p: a → Bool) → List.any xs p = Nat.leq 1 (List.occurrences xs p)
  | [], p => rfl
  | [x, ..xs], p =>
    Bool.inspect (p x) (c => Bool.ifThenElse c (u => True) (u => List.any xs p) = Nat.leq 1 (Bool.toNat c + List.occurrences xs p))
      (t => rfl) (f => List.anyOccurrences xs p)

theorem List.anyPerm (xs: List a) (ys: List a) (h: List.Perm xs ys) (p: a → Bool): List.any xs p = List.any ys p :=
  Eq.trans (List.anyOccurrences xs p) (Eq.trans (Eq.cong (n => Nat.leq 1 n) (h p)) (Eq.sym (List.anyOccurrences ys p)))

-- Reversing is a permutation, and keeps sums.

--| Counting in a list reversed onto `acc` counts in the list and in `acc`.
theorem List.occurrencesReverseOnto: (xs: List a) → (acc: List a) → (p: a → Bool) →
    List.occurrences (List.reverseOnto xs acc) p = List.occurrences xs p + List.occurrences acc p
  | [], acc, p => rfl
  | [x, ..xs], acc, p =>
    Eq.trans (List.occurrencesReverseOnto xs [x, ..acc] p)
      (Eq.trans (Nat.addLeftComm (List.occurrences xs p) (Bool.toNat (p x)) (List.occurrences acc p))
        (Eq.sym (Nat.addAssoc (Bool.toNat (p x)) (List.occurrences xs p) (List.occurrences acc p))))

--| Reversing a list gives a permutation of it.
theorem List.reversePerm (xs: List a): List.Perm (List.reverse xs) xs := p =>
  Eq.trans (List.occurrencesReverseOnto xs [] p) (Nat.addZero (List.occurrences xs p))

theorem List.sumByReverseOnto: (xs: List a) → (acc: List a) → (f: a → Nat) →
    List.sumBy (List.reverseOnto xs acc) f = List.sumBy xs f + List.sumBy acc f
  | [], acc, f => rfl
  | [x, ..xs], acc, f =>
    Eq.trans (List.sumByReverseOnto xs [x, ..acc] f)
      (Eq.trans (Eq.cong (t => List.sumBy xs f + t) (List.sumByCons acc x f))
        (Eq.trans (Nat.addLeftComm (List.sumBy xs f) (f x) (List.sumBy acc f))
          (Eq.trans (Eq.sym (Nat.addAssoc (f x) (List.sumBy xs f) (List.sumBy acc f)))
            (Eq.cong (t => t + List.sumBy acc f) (Eq.sym (List.sumByCons xs x f))))))

theorem List.sumByReverse (xs: List a) (f: a → Nat): List.sumBy (List.reverse xs) f = List.sumBy xs f :=
  Eq.trans (List.sumByReverseOnto xs [] f) (Nat.addZero (List.sumBy xs f))

--| Counting with a test nothing passes finds nothing.
theorem List.occurrencesNone: (xs: List a) → (p: a → Bool) → (h: (x: a) → p x = False) → List.occurrences xs p = 0
  | [], p, h => rfl
  | [x, ..xs], p, h => Eq.trans (Eq.cong (b => Bool.toNat b + List.occurrences xs p) (h x)) (List.occurrencesNone xs p h)

--| When nothing passes both `p` and `q`, the elements passing either are those
--| passing `p` plus those passing `q`.
theorem List.occurrencesOr: (xs: List a) → (p: a → Bool) → (q: a → Bool) → (h: (x: a) → p x = True → q x = False) →
    List.occurrences xs (x => p x ∨ q x) = List.occurrences xs p + List.occurrences xs q
  | [], p, q, h => rfl
  | [x, ..xs], p, q, h =>
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

--| `List.rangeFrom n s` has `n` elements.
theorem List.lengthRangeFrom: (n: Nat) → (s: Nat) → List.length (List.rangeFrom n s) = n
  | Zero, s => rfl
  | Succ n, s => rewrite List.lengthRangeFrom n (Succ s)

--| Mapping twice is mapping once by the composed function.
theorem List.mapMap: (xs: List a) → (f: b → c) → (g: a → b) → List.map (List.map xs g) f = List.map xs (x => f (g x))
  | [], f, g => rfl
  | [x, ..xs], f, g => rewrite List.mapMap xs f g

theorem List.filterMapMap: (xs: List a) → (f: b → Option c) → (g: a → b) → List.filterMap (List.map xs g) f = List.filterMap xs (x => f (g x))
  | [], f, g => rfl
  | [x, ..xs], f, g => rewrite List.filterMapMap xs f g

theorem List.filterMapSome: (xs: List a) → (f: a → b) → List.filterMap xs (x => Some (f x)) = List.map xs f
  | [], f => rfl
  | [x, ..xs], f => rewrite List.filterMapSome xs f

theorem List.filterMapAppend: (xs: List a) → (ys: List a) → (f: a → Option b) →
    List.filterMap (List.append xs ys) f = List.append (List.filterMap xs f) (List.filterMap ys f)
  | [], ys, f => rfl
  | [x, ..xs], ys, f =>
    match f x with
      | None => List.filterMapAppend xs ys f
      | Some y => rewrite List.filterMapAppend xs ys f

theorem List.initMap: (xs: List a) → (f: a → b) → List.init (List.map xs f) = List.map (List.init xs) f
  | [], f => rfl
  | [x], f => rfl
  | [x, y, ..ys], f => rewrite List.initMap [y, ..ys] f

theorem List.lastMap: (xs: List a) → (f: a → b) → List.last (List.map xs f) = Option.map (List.last xs) f
  | [], f => rfl
  | [x], f => rfl
  | [x, y, ..ys], f => List.lastMap [y, ..ys] f
theorem List.mapRangeFromShift (f: Nat → b): (n: Nat) → (s: Nat) →
    List.map (List.rangeFrom n (Succ s)) f = List.map (List.rangeFrom n s) (i => f (Succ i))
  | Zero, s => rfl
  | Succ n, s => rewrite List.mapRangeFromShift f n (Succ s)

--| Shifting a range up by one: map over it is a map over the range below, with the argument shifted.
theorem List.mapRangeShift (f: Nat → b) (from: Nat) (until: Nat):
    List.map (List.range (from + 1) (until + 1)) f = List.map (List.range from until) (i => f (i + 1)) :=
  List.mapRangeFromShift f (until - from) from

--| Transposing a grid given cell by cell: row x, column y becomes row y, column x.
theorem List.transposeNGrid (rows: List a): (cols: List b) → (cell: a → b → c) →
    List.transposeN (List.length cols) (List.map rows (x => List.map cols (cell x))) = List.map cols (y => List.map rows (x => cell x y))
  | [], cell => rfl
  | [y, ..cols], cell =>
    calc List.transposeN (Succ (List.length cols)) (List.map rows (x => List.map [y, ..cols] (cell x)))
      _ = [List.filterMap (List.map rows (x => List.map [y, ..cols] (cell x))) (.get 0), ..List.transposeN (List.length cols) (List.map (List.map rows (x => List.map [y, ..cols] (cell x))) (.drop 1))]
      _ = [List.filterMap rows (x => Some (cell x y)), ..List.transposeN (List.length cols) (List.map rows (x => List.map cols (cell x)))]
        := rewrite List.filterMapMap rows (.get 0) (x => List.map [y, ..cols] (cell x)),
          List.mapMap rows (.drop 1) (x => List.map [y, ..cols] (cell x))
      _ = [List.map rows (x => cell x y), ..List.map cols (z => List.map rows (x => cell x z))]
        := rewrite List.filterMapSome rows (x => cell x y), List.transposeNGrid rows cols cell

theorem List.transposeGrid (rows: List a) (r: a) (cols: List b) (cell: a → b → c):
    List.transpose (List.map [r, ..rows] (x => List.map cols (cell x))) = List.map cols (y => List.map [r, ..rows] (x => cell x y)) :=
  calc List.transpose (List.map [r, ..rows] (x => List.map cols (cell x)))
    _ = List.transposeN (List.length (List.map cols (cell r))) (List.map [r, ..rows] (x => List.map cols (cell x)))
    _ = List.transposeN (List.length cols) (List.map [r, ..rows] (x => List.map cols (cell x))) := rewrite List.lengthMap cols (cell r)
    _ = List.map cols (y => List.map [r, ..rows] (x => cell x y)) := List.transposeNGrid [r, ..rows] cols cell

theorem List.mapReverseOnto: (xs: List a) → (acc: List a) → (f: a → b) →
    List.map (List.reverseOnto xs acc) f = List.reverseOnto (List.map xs f) (List.map acc f)
  | [], acc, f => rfl
  | [x, ..xs], acc, f => List.mapReverseOnto xs [x, ..acc] f

theorem List.mapReverse (xs: List a) (f: a → b): List.map (List.reverse xs) f = List.reverse (List.map xs f) := List.mapReverseOnto xs [] f

--| Reversing onto `acc`, then reversing that, is `acc` reversed onto the list.
theorem List.reverseOntoTwice: (xs: List a) → (acc: List a) → List.reverseOnto (List.reverseOnto xs acc) [] = List.reverseOnto acc xs
  | [], acc => rfl
  | [x, ..xs], acc => List.reverseOntoTwice xs [x, ..acc]

--| Reversing twice gives the list back.
theorem List.reverseReverse (xs: List a): List.reverse (List.reverse xs) = xs := List.reverseOntoTwice xs []

--| Reversing onto an accumulator keeps the elements of both.
theorem List.memReverseOnto (x: a): (xs: List a) → (acc: List a) → x ∈ List.reverseOnto xs acc ↔ (x ∈ xs ∨ x ∈ acc)
  | [], acc => {
    forward = m => Inr m,
    backward = h =>
      match h with
        | Inl m => Void.exfalso m
        | Inr m => m
  }
  | [y, ..ys], acc => {
    forward = m =>
      match (List.memReverseOnto x ys [y, ..acc]).forward m with
        | Inl i => Inl (Inr i)
        | Inr (Inl e) => Inl (Inl e)
        | Inr (Inr i) => Inr i,
    backward = h =>
      (List.memReverseOnto x ys [y, ..acc]).backward (
        match h with
          | Inl (Inl e) => Inr (Inl e)
          | Inl (Inr i) => Inl i
          | Inr i => Inr (Inr i))
  }

--| A list and its reverse have the same elements.
theorem List.memReverse (x: a) (xs: List a): x ∈ xs.reverse ↔ x ∈ xs := {
  forward = m =>
    match (List.memReverseOnto x xs []).forward m with
      | Inl i => i
      | Inr n => Void.exfalso n,
  backward = m => (List.memReverseOnto x xs []).backward (Inl m)
}

--| Reversing onto `acc` is reversing, then appending `acc`.
theorem List.reverseOntoAppend: (xs: List a) → (acc: List a) → List.reverseOnto xs acc = List.append (List.reverseOnto xs []) acc
  | [], acc => rfl
  | [x, ..xs], acc =>
    rewrite List.reverseOntoAppend xs [x, ..acc], List.reverseOntoAppend xs [x]
      in Eq.sym (List.appendAssoc (List.reverseOnto xs []) [x] acc)

--| Reversing a list puts its first element last.
theorem List.reverseCons (x: a) (xs: List a): List.reverse [x, ..xs] = List.append (List.reverse xs) [x] := List.reverseOntoAppend xs [x]

--| Reversing a list puts its last element first.
theorem List.reverseSnoc: (xs: List a) → (x: a) → List.reverse (List.append xs [x]) = [x, ..List.reverse xs]
  | [], x => rfl
  | [y, ..rest], x =>
    rewrite List.reverseCons y (List.append rest [x]), List.reverseSnoc rest x, List.reverseCons y rest in rfl

--| Reversing a list that is two lists joined reverses each and swaps them:
--| `(xs ++ ys).reverse = ys.reverse ++ xs.reverse`.
theorem List.reverseAppend: (xs: List a) → (ys: List a) → List.reverse (List.append xs ys) = List.append (List.reverse ys) (List.reverse xs)
  | [], ys => Eq.sym (List.appendNil (List.reverse ys))
  | [x, ..rest], ys =>
    Eq.trans (List.reverseCons x (List.append rest ys))
      (Eq.trans (Eq.cong (reversed => List.append reversed [x]) (List.reverseAppend rest ys))
        (Eq.trans (List.appendAssoc (List.reverse ys) (List.reverse rest) [x])
          (Eq.cong (tail => List.append (List.reverse ys) tail) (Eq.sym (List.reverseCons x rest)))))

theorem List.lengthReverseOnto: (xs: List a) → (acc: List a) → List.length (List.reverseOnto xs acc) = List.length xs + List.length acc
  | [], acc => rfl
  | [x, ..rest], acc => Eq.trans (List.lengthReverseOnto rest [x, ..acc]) (Nat.addSucc (List.length rest) (List.length acc))

--| Reversing keeps the length.
theorem List.lengthReverse (xs: List a): List.length (List.reverse xs) = List.length xs :=
  Eq.trans (List.lengthReverseOnto xs []) (Nat.addZero (List.length xs))

theorem List.lengthSnoc: (xs: List a) → (x: a) → List.length (List.append xs [x]) = Succ (List.length xs)
  | [], x => rfl
  | [y, ..rest], x => Eq.cong Succ (List.lengthSnoc rest x)

--| Counting in a `flatMap` over a list reversed onto `acc`.
theorem List.occurrencesFlatMapReverseOnto (f: a → List b) (p: b → Bool): (xs: List a) → (acc: List a) →
    List.occurrences (List.flatMap (List.reverseOnto xs acc) f) p =
      List.occurrences (List.flatMap xs f) p + List.occurrences (List.flatMap acc f) p
  | [], acc => rfl
  | [x, ..rest], acc =>
    let here := List.occurrences (f x) p
    let before := List.occurrences (List.flatMap rest f) p
    let after := List.occurrences (List.flatMap acc f) p
    rewrite List.occurrencesFlatMapReverseOnto f p rest [x, ..acc], List.occurrencesAppend (f x) (List.flatMap acc f) p,
      List.occurrencesAppend (f x) (List.flatMap rest f) p
      in Eq.trans (Eq.sym (Nat.addAssoc before here after)) (Eq.cong (t => t + after) (Nat.addComm before here))

--| A `flatMap` over the list reversed has the same elements.
theorem List.permFlatMapReverse (f: a → List b) (xs: List a): List.Perm (List.flatMap (List.reverse xs) f) (List.flatMap xs f) :=
  p => Eq.trans (List.occurrencesFlatMapReverseOnto f p xs []) (Nat.addZero (List.occurrences (List.flatMap xs f) p))

--| Adding up the values there are is adding up every value, with 0 for none.
theorem List.sumFilterMap (f: a → Option Nat): (xs: List a) →
    List.sum (List.filterMap xs f) = List.sumBy xs (x => Option.getOrElse (f x) 0)
  | [] => rfl
  | [x, ..rest] =>
    rewrite List.sumByCons rest x (y => Option.getOrElse (f y) 0), <- List.sumFilterMap f rest in
      match value: f x with
        | Some v => List.sumByCons (List.filterMap rest f) v (y => y)
        | None => rfl

theorem List.reverseReverseExample: List.reverse (List.reverse [1, 2, 3]) = [1, 2, 3] := List.reverseReverse [1, 2, 3]

--| A test every element passes holds for all of them.
theorem List.allTrue: (xs: List a) → (p: a → Bool) → ((x: a) → p x = True) → List.all xs p = True
  | [], p, h => rfl
  | [x, ..xs], p, h => rewrite h x in List.allTrue xs p h

--| A test no element passes holds for none of them.
theorem List.anyFalse: (xs: List a) → (p: a → Bool) → ((x: a) → p x = False) → List.any xs p = False
  | [], p, h => rfl
  | [x, ..xs], p, h => rewrite h x in List.anyFalse xs p h

--| Every element passes both tests when every element passes each.
theorem List.allAnd: (xs: List a) → (p: a → Bool) → (q: a → Bool) → List.all xs (x => p x ∧ q x) = (List.all xs p ∧ List.all xs q)
  | [], p, q => rfl
  | [x, ..xs], p, q =>
    match px: p x, qx: q x with
      | True, True => List.allAnd xs p q
      | True, False => cases
      | False, qx => rfl

theorem Option.flatMapMap: (m: Option a) → (g: b → Option c) → (f: a → b) → Option.flatMap (Option.map m f) g = Option.flatMap m (x => g (f x))
  | None, g, f => rfl
  | Some x, g, f => rfl

theorem List.lengthZipWith3 (f: a → b → c → e): (xs: List a) → (ys: List b) → (zs: List c) →
    List.length ys = List.length xs → List.length zs = List.length xs → List.length (List.zipWith3 xs ys zs f) = List.length xs
  | [], ys, zs, h1, h2 => rfl
  | [x, ..xs], [], zs, h1, h2 => Void.exfalso (Nat.zeroNotSucc (List.length xs) h1)
  | [x, ..xs], [y, ..ys], [], h1, h2 => Void.exfalso (Nat.zeroNotSucc (List.length xs) h2)
  | [x, ..xs], [y, ..ys], [z, ..zs], h1, h2 =>
    rewrite List.lengthZipWith3 f xs ys zs (Nat.succInjective (List.length ys) (List.length xs) h1) (Nat.succInjective (List.length zs) (List.length xs) h2)

--| Lists zipped in step are no longer than the first.
theorem List.lengthZipWithLe (f: a → b → c): (xs: List a) → (ys: List b) → List.length (List.zipWith xs ys f) ≤ List.length xs
  | [], ys => rfl
  | [x, ..xs], [] => rfl
  | [x, ..xs], [y, ..ys] => List.lengthZipWithLe f xs ys

theorem List.lengthZipWith3Le (f: a → b → c → d): (xs: List a) → (ys: List b) → (zs: List c) → List.length (List.zipWith3 xs ys zs f) ≤ List.length xs
  | [], ys, zs => rfl
  | [x, ..xs], [], zs => rfl
  | [x, ..xs], [y, ..ys], [] => rfl
  | [x, ..xs], [y, ..ys], [z, ..zs] => List.lengthZipWith3Le f xs ys zs

theorem List.lengthZipWith4Le (f: a → b → c → d → e): (xs: List a) → (ys: List b) → (zs: List c) → (ws: List d) →
    List.length (List.zipWith4 xs ys zs ws f) ≤ List.length xs
  | [], ys, zs, ws => rfl
  | [x, ..xs], [], zs, ws => rfl
  | [x, ..xs], [y, ..ys], [], ws => rfl
  | [x, ..xs], [y, ..ys], [z, ..zs], [] => rfl
  | [x, ..xs], [y, ..ys], [z, ..zs], [w, ..ws] => List.lengthZipWith4Le f xs ys zs ws

--| Zipping with an empty list in a later place gives nothing.
theorem List.zipWith3NilSecond (zs: List c) (f: a → b → c → d): (xs: List a) → List.zipWith3 xs [] zs f = []
  | [] => rfl
  | [x, ..xs] => rfl

theorem List.zipWith3NilThird (f: a → b → c → d): (xs: List a) → (ys: List b) → List.zipWith3 xs ys [] f = []
  | [], ys => rfl
  | [x, ..xs], [] => rfl
  | [x, ..xs], [y, ..ys] => rfl

theorem List.zipWith4NilSecond (zs: List c) (ws: List d) (f: a → b → c → d → e): (xs: List a) → List.zipWith4 xs [] zs ws f = []
  | [] => rfl
  | [x, ..xs] => rfl

theorem List.zipWith4NilThird (ws: List d) (f: a → b → c → d → e): (xs: List a) → (ys: List b) → List.zipWith4 xs ys [] ws f = []
  | [], ys => rfl
  | [x, ..xs], [] => rfl
  | [x, ..xs], [y, ..ys] => rfl

theorem List.zipWith4NilFourth (f: a → b → c → d → e): (xs: List a) → (ys: List b) → (zs: List c) → List.zipWith4 xs ys zs [] f = []
  | [], ys, zs => rfl
  | [x, ..xs], [], zs => rfl
  | [x, ..xs], [y, ..ys], [] => rfl
  | [x, ..xs], [y, ..ys], [z, ..zs] => rfl

theorem List.distinctNil: List.Distinct ([]: List a) := Trivial

theorem List.distinctCons (x: a) (xs: List a) (h: x ∉ xs) (d: List.Distinct xs): List.Distinct [x, ..xs] := Both h d

--| An element of two lists joined is in one of them.
theorem List.memAppend (x: a): (xs: List a) → (ys: List a) → x ∈ List.append xs ys → (x ∈ xs) ∨ (x ∈ ys)
  | [], ys, h => Inr h
  | [z, ..zs], ys, Inl h => Inl (Inl h)
  | [z, ..zs], ys, Inr h =>
    match List.memAppend x zs ys h with
      | Inl m => Inl (Inr m)
      | Inr m => Inr m

-- And back, `List.memAppendLeft` and `List.memAppendRight`, are in the core
-- (core/Finite.sw): derived `Finite` instances use them.

theorem List.memAppendExample: 3 ∈ List.append [1, 2] [3] := List.memAppendRight 3 [1, 2] [3] (Inl rfl)

--| `f x` is in `List.map xs f` only if `x` is in `xs`, for an injective `f`.
theorem List.memMapInjective (f: a → b) (inj: (x: a) → (y: a) → f x = f y → x = y) (x: a): (xs: List a) → f x ∈ List.map xs f → x ∈ xs
  | [], h => h
  | [z, ..zs], Inl h => Inl (inj z x h)
  | [z, ..zs], Inr h => Inr (List.memMapInjective f inj x zs h)

--| If `x` is in `xs`, `f x` is in `List.map xs f`.
theorem List.memMap: (xs: List a) → (x: a) → x ∈ xs → (f: a → b) → f x ∈ List.map xs f
  | [], x, h, f => h
  | [z, ..zs], x, Inl h, f => Inl (Eq.cong f h)
  | [z, ..zs], x, Inr h, f => Inr (List.memMap zs x h f)

--| Use "some element satisfies `p`": take that element, know it is in the
--| list, and carry on to the goal. (The library has no `Exists`.)
theorem List.anyElim (p: a → Prop) (goal: Prop): (xs: List a) → List.Any p xs → (cont: (x: a) → x ∈ xs → p x → goal) → goal
  | [], h, k => Void.exfalso h
  | [z, ..zs], Inl h, k => k z (Inl rfl) h
  | [z, ..zs], Inr h, k => List.anyElim p goal zs h (x inZs px => k x (Inr inZs) px)

--| To prove that some element satisfies `p`, give an element of the list that does. (For the
--| `Bool` `List.any`, [`List.anyOfMem`].)
theorem List.anyIntro (p: a → Prop) (x: a): (xs: List a) → x ∈ xs → p x → List.Any p xs
  | [], m, px => Void.exfalso m
  | [z, ..zs], Inl e, px => Inl (rewrite e in px)
  | [z, ..zs], Inr m, px => Inr (List.anyIntro p x zs m px)

theorem List.anyIntroExample: List.Any (n => n > 2) [1, 2, 3] := List.anyIntro (n => n > 2) 3 [1, 2, 3] (Inr (Inr (Inl rfl))) rfl

--| What is in `List.map xs f` is `f x` for some `x` in `xs` (said with
--| `List.Any`, which also says where `x` is: `Exists` wouldn't).
theorem List.memMapAny: (xs: List a) → (f: a → b) → (y: b) → y ∈ List.map xs f → List.Any (x => f x = y) xs
  | [], f, y, h => h
  | [z, ..zs], f, y, Inl h => Inl h
  | [z, ..zs], f, y, Inr h => Inr (List.memMapAny zs f y h)

--| `List.Any` gives a member that satisfies `p`.
theorem List.anyMember (p: a → Prop): (xs: List a) → List.Any p xs → Exists a (x => (x ∈ xs) ∧ (p x))
  | [], none => Void.exfalso none
  | [x, ..rest], Inl here => Witness x (Both (Inl rfl) here)
  | [x, ..rest], Inr later => Exists.elim (List.anyMember p rest later) (found both => Witness found (Both (Inr (And.left both)) (And.right both)))

--| A member of a mapped list is the image of a member.
theorem List.memMapElim (f: a → b) (y: b) (xs: List a) (member: y ∈ List.map xs f): Exists a (x => (x ∈ xs) ∧ (f x = y)) :=
  List.anyMember (x => f x = y) xs (List.memMapAny xs f y member)

--| What `(.filter p)` keeps was in the list, and passes `p`.
theorem List.memFilter: (xs: List a) → (p: a → Bool) → (x: a) → x ∈ List.filter xs p → (x ∈ xs) ∧ (p x = True)
  | [], p, x, h => Void.exfalso h
  | [y, ..ys], p, x, h =>
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

--| A `filter` that keeps nothing of the list is empty.
theorem List.filterNone (p: a → Bool): (xs: List a) → ((x: a) → x ∈ xs → p x = False) → List.filter xs p = []
  | [], h => rfl
  | [x, ..xs], h => rewrite h x (Inl rfl) in List.filterNone p xs (y m => h y (Inr m))

--| A `filter` that keeps all of the list is the list.
theorem List.filterAll (p: a → Bool): (xs: List a) → ((x: a) → x ∈ xs → p x = True) → List.filter xs p = xs
  | [], h => rfl
  | [x, ..xs], h => rewrite h x (Inl rfl) in Eq.cong (Cons x) (List.filterAll p xs (y m => h y (Inr m)))

--| No successor is zero, and every one is at least 1.
theorem List.filterNoneExample (xs: List Nat): List.filter (List.map xs Succ) (n => n == 0) = [] :=
  List.filterNone (n => n == 0) (List.map xs Succ) (n m =>
    List.anyElim (x => Succ x = n) ((n == 0) = False) xs (List.memMapAny xs Succ n m) (x inXs e => rewrite <- e in rfl))

theorem List.filterAllExample (xs: List Nat): List.filter (List.map xs Succ) (n => Nat.leq 1 n) = List.map xs Succ :=
  List.filterAll (n => Nat.leq 1 n) (List.map xs Succ) (n m =>
    List.anyElim (x => Succ x = n) (Nat.leq 1 n = True) xs (List.memMapAny xs Succ n m) (x inXs e => rewrite <- e in rfl))

--| A list's `flatMap`: an element of `f x` for an `x` of the list is in it.
theorem List.memFlatMapIntro (f: a → List b) (x: a) (y: b): (xs: List a) → x ∈ xs → y ∈ f x → y ∈ List.flatMap xs f
  | [], h, m => Void.exfalso h
  | [z, ..zs], Inl h, m => List.anyAppendLeft (w => w = y) (f z) (List.concat (List.map zs f)) (rewrite h in m)
  | [z, ..zs], Inr h, m => List.anyAppendRight (w => w = y) (f z) (List.concat (List.map zs f)) (List.memFlatMapIntro f x y zs h m)

--| What is in a `flatMap` is in `f x` for some `x` of the list.
theorem List.memFlatMapElim (f: a → List b) (y: b): (xs: List a) → y ∈ List.flatMap xs f → List.Any (x => y ∈ f x) xs
  | [], h => h
  | [z, ..zs], h =>
    match List.memAppend y (f z) (List.concat (List.map zs f)) h with
      | Inl m => Inl m
      | Inr m => Inr (List.memFlatMapElim f y zs m)

--| Mapping an injective function keeps a list distinct.
theorem List.distinctMap: (xs: List a) → List.Distinct xs → (f: a → b) → (inj: (x: a) → (y: a) → f x = f y → x = y) → List.Distinct (List.map xs f)
  | [], d, f, inj => Trivial
  | [x, ..xs], Both h d, f, inj => Both (m => h (List.memMapInjective f inj x xs m)) (List.distinctMap xs d f inj)

--| Two distinct lists with no element in common, joined, are distinct.
theorem List.distinctAppend: (xs: List a) → (ys: List a) → List.Distinct xs → List.Distinct ys → List.Disjoint xs ys → List.Distinct (List.append xs ys)
  | [], ys, dx, dy, dj => dy
  | [x, ..xs], ys, Both hx dx, dy, Both hj dj =>
    Both
      (m => match List.memAppend x xs ys m with
        | Inl inXs => hx inXs
        | Inr inYs => hj inYs)
      (List.distinctAppend xs ys dx dy dj)

--| The parts of a list with no repeats have none, and nothing in common.
theorem List.distinctAppendLeft: (xs: List a) → (ys: List a) → List.Distinct (List.append xs ys) → List.Distinct xs
  | [], ys, d => Trivial
  | [x, ..rest], ys, Both out d => Both (m => out (List.memAppendLeft x rest ys m)) (List.distinctAppendLeft rest ys d)

theorem List.distinctAppendRight: (xs: List a) → (ys: List a) → List.Distinct (List.append xs ys) → List.Distinct ys
  | [], ys, d => d
  | [x, ..rest], ys, Both out d => List.distinctAppendRight rest ys d

theorem List.distinctAppendApart: (xs: List a) → (ys: List a) → List.Distinct (List.append xs ys) → (z: a) → z ∈ xs → z ∈ ys → Void
  | [], ys, d, z, inXs, inYs => inXs
  | [x, ..rest], ys, Both out d, z, Inl e, inYs => out (List.memAppendRight x rest ys (rewrite e in inYs))
  | [x, ..rest], ys, Both out d, z, Inr inRest, inYs => List.distinctAppendApart rest ys d z inRest inYs

--| Two lists with the same head are equal only if their tails are.
theorem List.consInjective (x: a) (ys: List a) (zs: List a) (p: [x, ..ys] = [x, ..zs]): ys = zs := Eq.cong (.drop 1) p

--| Two equal non-empty lists have the same head: the complement of
--| [`List.consInjective`], which gives the tails when the heads are the same.
theorem List.consInjectiveHead (x: a) (y: a) (xs: List a) (ys: List a) (p: [x, ..xs] = [y, ..ys]): x = y :=
  Eq.cong (list => (list.get 0).getOrElse x) p

--| A list starting with x isn't among lists that all start with y, a
--| different element.
theorem List.notMemMapCons (x: a) (y: a) (ne: x ≠ y) (xs: List a): (ys: List (List a)) → [x, ..xs] ∉ List.map ys (Cons y)
  | [], m => m
  | [z, ..zs], Inl p => ne (Eq.sym (Eq.cong (.headOr x) p))
  | [z, ..zs], Inr q => List.notMemMapCons x y ne xs zs q

--| Lists that all start with x and lists that all start with a different y
--| have none in common.
theorem List.disjointMapCons (ys: List (List a)) (x: a) (y: a) (ne: x ≠ y): (xs: List (List a)) →
    List.Disjoint (List.map xs (Cons x)) (List.map ys (Cons y))
  | [] => Trivial
  | [z, ..zs] => Both (List.notMemMapCons x y ne z ys) (List.disjointMapCons ys x y ne zs)

--| A run of numbers has no repeats.
theorem List.distinctRangeFrom: (c: Nat) → (s: Nat) → List.Distinct (List.rangeFrom c s)
  | Zero, s => Trivial
  | Succ c, s =>
    Both (m => match List.memRangeFrom s c (Succ s) m with
        | Both above _ => Nat.lessIrrefl s above)
      (List.distinctRangeFrom c (Succ s))

--| A range has no repeats.
theorem List.distinctRange (a: Nat) (b: Nat): List.Distinct (List.range a b) := List.distinctRangeFrom (b - a) a

--| Every element of the list passes, given that each element that is in it does.
theorem List.allOfMem (p: a → Prop): (xs: List a) → ((x: a) → x ∈ xs → p x) → List.All p xs
  | [], h => Trivial
  | [z, ..zs], h => Both (h z (Inl rfl)) (List.allOfMem p zs (x inZs => h x (Inr inZs)))

--| A `flatMap` of distinct lists has no repeats if the list mapped over has none
--| and the lists apart: `key` says which element of `xs` each result came from.
theorem List.distinctFlatMap (f: a → List b) (key: b → a): (xs: List a) → List.Distinct xs →
    ((x: a) → x ∈ xs → List.Distinct (f x)) →
    ((x: a) → x ∈ xs → (y: b) → y ∈ f x → key y = x) →
    List.Distinct (List.flatMap xs f)
  | [], d, distinctEach, keyed => Trivial
  | [x, ..xs], Both notLater later, distinctEach, keyed =>
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

theorem List.consInjectiveExample (ys: List Nat) (zs: List Nat) (p: [1, ..ys] = [1, ..zs]): ys = zs := List.consInjective 1 ys zs p

theorem List.disjointMapConsExample: List.Disjoint (List.map [[1], [2]] (Cons 0)) (List.map [[1], []] (Cons 1)) :=
  List.disjointMapCons [[1], []] 0 1 (p => Nat.succNotZero 0 (Eq.sym p)) [[1], [2]]

theorem List.distinctMapConsExample: List.Distinct (List.append (List.map [[]] (Cons 0)) (List.map [[]] (Cons 1))) :=
  List.distinctAppend (List.map [[]] (Cons 0)) (List.map [[]] (Cons 1))
    (List.distinctMap [[]] (Both (m => m) Trivial) (Cons 0) (List.consInjective 0))
    (List.distinctMap [[]] (Both (m => m) Trivial) (Cons 1) (List.consInjective 1))
    (List.disjointMapCons [[]] 0 1 (p => Nat.succNotZero 0 (Eq.sym p)) [[]])

theorem List.memRangeExample: 3 ∈ List.range 1 6 := (List.memRange 3 1 6).backward (Both rfl rfl)

theorem List.memFlatMapExample: 20 ∈ List.flatMap [1, 2] (x => [x, x * 10]) :=
  List.memFlatMapIntro (x => [x, x * 10]) 2 20 [1, 2] (Inr (Inl rfl)) (Inr (Inl rfl))

theorem List.distinctAppendExample: List.Distinct (List.append [1] [2]) :=
  List.distinctAppend [1] [2]
    (Both (m => m) Trivial)
    (Both (m => m) Trivial)
    (Both (m => match m with
      | Inl p => Nat.succNotZero 0 (Nat.succInjective 1 0 p)
      | Inr v => v) Trivial)

--| What `List.All` says of an element of the list.
theorem List.allMem (p: a → Prop) (x: a): (xs: List a) → List.All p xs → x ∈ xs → p x
  | [], h, m => Void.exfalso m
  | [z, ..zs], Both pz h, Inl e => rewrite <- e in pz
  | [z, ..zs], Both pz h, Inr m => List.allMem p x zs h m

-- `List.find` and `List.any`, and keys that are distinct (SW-363): lemmas
-- for code that finds records by an id.

--| What `List.find` finds passes the test and is in the list.
theorem List.findSome: (xs: List a) → (p: a → Bool) → (y: a) → List.find xs p = Some y → (p y = True) ∧ (y ∈ xs)
  | [], p, y, h => Void.exfalso (Option.noneNotSome y h)
  | [x, ..xs], p, y, h =>
    match e: p x with
      | True => Both (Eq.trans (Eq.cong p (Eq.sym (Option.someInjective x y h))) e) (Inl (Option.someInjective x y h))
      | False =>
        match List.findSome xs p y h with
          | Both py m => Both py (Inr m)

--| `List.find` finds nothing only when no element passes.
theorem List.findNoneNotMem: (xs: List a) → (p: a → Bool) → (x: a) → (px: p x = True) → x ∈ xs → List.find xs p = None → Void
  | [], p, x, px, m, h => m
  | [z, ..zs], p, x, px, Inl e, h => Option.someNotNone x (rewrite e, px at h)
  | [z, ..zs], p, x, px, Inr m, h =>
    match c: p z with
      | True => Option.someNotNone z h
      | False => List.findNoneNotMem zs p x px m h

--| Finding nothing means every element fails, as an `all`. So
--| `find xs bad = None` gives `xs.all (x => ¬(bad x))`, and a search for
--| one that isn't `good` finding nothing gives `xs.all good`.
theorem List.findNoneAll: (xs: List a) → (p: a → Bool) → List.find xs p = None → List.all xs (x => ¬(p x)) = True
  | [], p, h => rfl
  | [x, ..rest], p, h =>
    match e: p x with
      | False => List.findNoneAll rest p h
      | True => Void.exfalso (Option.someNotNone x h)

theorem List.findNotNoneAll: (xs: List a) → (good: a → Bool) → List.find xs (x => ¬(good x)) = None → List.all xs good = True
  | [], good, h => rfl
  | [x, ..rest], good, h =>
    match e: good x with
      | True => List.findNotNoneAll rest good h
      | False => Void.exfalso (Option.someNotNone x h)

--| Searching the elements paired with their indices (`withIndex`) by the
--| element alone finds nothing exactly when searching the list does.
theorem List.findWithIndexFromNone (p: a → Bool): (i: Nat) → (xs: List a) →
    List.find (List.withIndexFrom i xs) (((_, x)) => p x) = None → List.find xs p = None
  | i, [], h => rfl
  | i, [x, ..rest], h =>
    match e: p x with
      | False => List.findWithIndexFromNone p (Succ i) rest h
      | True => Void.exfalso (Option.someNotNone (MkPair i x) h)

-- `List.find` over `List.range`: what it finds is the least number that
-- passes, and when it finds nothing, no number in the range passes.

--| No number from `start` up to the one found passes.
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

--| What is found passes, is in the range, and no smaller number passes.
theorem List.findRangeSome (passes: Nat → Bool) (count: Nat) (found: Nat) (h: (List.range 0 count).find passes = Some found):
    (passes found = True) ∧ ((found < count) ∧ ((earlier: Nat) → earlier < found → passes earlier = False)) :=
  match List.findSome (List.range 0 count) passes found h with
    | Both foundPasses member =>
      Both foundPasses
        (Both (And.right (List.memRangeFrom found count 0 member))
          (earlier before => List.findRangeFirst passes count 0 found h earlier (Nat.zeroLe earlier) before))

--| Finding nothing means no number in the range passes.
theorem List.findRangeNone (passes: Nat → Bool) (count: Nat) (h: (List.range 0 count).find passes = None) (n: Nat) (below: n < count):
    passes n = False :=
  match c: passes n with
    | True => Void.exfalso (List.findNoneNotMem (List.range 0 count) passes n c (List.memRangeFromIntro n count 0 (Nat.zeroLe n) below) h)
    | False => rfl

test "List.findRangeSome" := List.range 0 10 |> .find (n => n * n > 20) == Some 5

-- `List.minimum`: the least of a list that holds `least` and nothing else
-- is `least`, an empty list has none, and what it finds is in the list and
-- at most each element.

--| Folding `Ord.min` from `least` over elements that are all `least`.
theorem List.foldMinAll [auto ord: Ord a] (least: a): (xs: List a) → ((x: a) → x ∈ xs → x = least) → List.foldLeft xs least Ord.min = least
  | [], all => rfl
  | [x, ..rest], all =>
    rewrite all x (Inl rfl), Ord.minSelf least in List.foldMinAll least rest (y member => all y (Inr member))

theorem List.minimumAllEqual [auto ord: Ord a] (least: a): (xs: List a) → least ∈ xs → ((x: a) → x ∈ xs → x = least) → List.minimum xs = Some least
  | [], member, all => Void.exfalso member
  | [x, ..rest], member, all =>
    rewrite all x (Inl rfl) in Eq.cong Some (List.foldMinAll least rest (y member => all y (Inr member)))

theorem List.minimumEmpty [auto ord: Ord a]: (xs: List a) → ((x: a) → x ∈ xs → Void) → List.minimum xs = None
  | [], none => rfl
  | [x, ..rest], none => Void.exfalso (none x (Inl rfl))

--| Folding with `Ord.min` gives at most the start and each element, and
--| gives the start or an element.
theorem List.foldMinLeStart [auto ord: Ord a]: (xs: List a) → (start: a) → List.foldLeft xs start Ord.min <= start
  | [], start => Ord.leRefl start
  | [y, ..ys], start =>
    Ord.leTrans (List.foldLeft ys (Ord.min start y) Ord.min) (Ord.min start y) start (List.foldMinLeStart ys (Ord.min start y)) (Ord.minLeLeft start y)

theorem List.foldMinLeMember [auto ord: Ord a]: (xs: List a) → (start: a) → (x: a) → x ∈ xs → List.foldLeft xs start Ord.min <= x
  | [], start, x, member => Void.exfalso member
  | [y, ..ys], start, x, Inl same =>
    rewrite Eq.sym same in
      Ord.leTrans (List.foldLeft ys (Ord.min start y) Ord.min) (Ord.min start y) y (List.foldMinLeStart ys (Ord.min start y)) (Ord.minLeRight start y)
  | [y, ..ys], start, x, Inr member => List.foldMinLeMember ys (Ord.min start y) x member

theorem List.foldMinMember [auto ord: Ord a]: (xs: List a) → (start: a) → (List.foldLeft xs start Ord.min = start) ∨ (List.foldLeft xs start Ord.min ∈ xs)
  | [], start => Inl rfl
  | [y, ..ys], start =>
    match List.foldMinMember ys (Ord.min start y) with
      | Inr member => Inr (Inr member)
      | Inl same =>
        match Ord.minEither start y with
          | Inl isStart => Inl (Eq.trans same isStart)
          | Inr isY => Inr (Inl (Eq.sym (Eq.trans same isY)))

--| The least element is in the list and at most every element.
theorem List.minimumSome [auto ord: Ord a] (xs: List a) (least: a) (found: List.minimum xs = Some least): (least ∈ xs) ∧ ((x: a) → x ∈ xs → least <= x) :=
  match xs with
    | [] => Void.exfalso (Option.noneNotSome least found)
    | [y, ..ys] =>
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

--| A list with an element has a least one.
theorem List.minimumExists [auto ord: Ord a]: (xs: List a) → (x: a) → x ∈ xs → ∃ (least: a) => List.minimum xs = Some least
  | [], x, member => Void.exfalso member
  | [y, ..ys], x, member => Witness (List.foldLeft ys y Ord.min) rfl

--| A list with an element has a least one: `List.minimum` isn't `None`.
theorem List.minimumNone [auto ord: Ord a] (xs: List a) (none: List.minimum xs = None) (x: a) (member: x ∈ xs): Void :=
  match xs with
    | [] => member
    | [y, ..ys] => Option.someNotNone (List.foldLeft ys y Ord.min) none

--| Lists with the same members have the same least member.
theorem List.minimumSameMembers [auto ord: Ord a] (xs: List a) (ys: List a) (into: (v: a) → v ∈ xs → v ∈ ys) (back: (v: a) → v ∈ ys → v ∈ xs):
    List.minimum xs = List.minimum ys :=
  match mx: List.minimum xs with
    | None =>
      match my: List.minimum ys with
        | None => rfl
        | Some y => Void.exfalso (List.minimumNone xs mx y (back y (List.minimumSome ys y my).left))
    | Some x =>
      match my: List.minimum ys with
        | None => Void.exfalso (List.minimumNone ys my x (into x (List.minimumSome xs x mx).left))
        | Some y =>
          let (Both xIn xLeast) := List.minimumSome xs x mx
          let (Both yIn yLeast) := List.minimumSome ys y my
          Eq.cong Some (Ord.leAntisymm x y (xLeast y (back y yIn)) (yLeast x (into x xIn)))

-- `List.maximum`, as for `List.minimum` above: the greatest of a list that
-- holds `most` and nothing else is `most`, an empty list has none, and what
-- it finds is in the list and at least each element. (`List.foldMaxGe`,
-- `List.leFoldMax` and `List.foldMaxMem` below are about folds of
-- `Nat.max`; these are about `Ord.max`, which `List.maximum` folds.)

--| Folding `Ord.max` from `most` over elements that are all `most`.
theorem List.foldMaxAll [auto ord: Ord a] (most: a): (xs: List a) → ((x: a) → x ∈ xs → x = most) → List.foldLeft xs most Ord.max = most
  | [], all => rfl
  | [x, ..rest], all =>
    rewrite all x (Inl rfl), Ord.maxSelf most in List.foldMaxAll most rest (y member => all y (Inr member))

theorem List.maximumAllEqual [auto ord: Ord a] (most: a): (xs: List a) → most ∈ xs → ((x: a) → x ∈ xs → x = most) → List.maximum xs = Some most
  | [], member, all => Void.exfalso member
  | [x, ..rest], member, all =>
    rewrite all x (Inl rfl) in Eq.cong Some (List.foldMaxAll most rest (y member => all y (Inr member)))

theorem List.maximumEmpty [auto ord: Ord a]: (xs: List a) → ((x: a) → x ∈ xs → Void) → List.maximum xs = None
  | [], none => rfl
  | [x, ..rest], none => Void.exfalso (none x (Inl rfl))

--| Folding with `Ord.max` gives at least the start and each element, and
--| gives the start or an element.
theorem List.foldMaxGeStart [auto ord: Ord a]: (xs: List a) → (start: a) → start <= List.foldLeft xs start Ord.max
  | [], start => Ord.leRefl start
  | [y, ..ys], start =>
    Ord.leTrans start (Ord.max start y) (List.foldLeft ys (Ord.max start y) Ord.max) (Ord.leMaxLeft start y) (List.foldMaxGeStart ys (Ord.max start y))

theorem List.foldMaxGeMember [auto ord: Ord a]: (xs: List a) → (start: a) → (x: a) → x ∈ xs → x <= List.foldLeft xs start Ord.max
  | [], start, x, member => Void.exfalso member
  | [y, ..ys], start, x, Inl same =>
    rewrite Eq.sym same in
      Ord.leTrans y (Ord.max start y) (List.foldLeft ys (Ord.max start y) Ord.max) (Ord.leMaxRight start y) (List.foldMaxGeStart ys (Ord.max start y))
  | [y, ..ys], start, x, Inr member => List.foldMaxGeMember ys (Ord.max start y) x member

theorem List.foldMaxMember [auto ord: Ord a]: (xs: List a) → (start: a) → (List.foldLeft xs start Ord.max = start) ∨ (List.foldLeft xs start Ord.max ∈ xs)
  | [], start => Inl rfl
  | [y, ..ys], start =>
    match List.foldMaxMember ys (Ord.max start y) with
      | Inr member => Inr (Inr member)
      | Inl same =>
        match Ord.maxEither start y with
          | Inl isStart => Inl (Eq.trans same isStart)
          | Inr isY => Inr (Inl (Eq.sym (Eq.trans same isY)))

--| The greatest element is in the list and at least every element.
theorem List.maximumSome [auto ord: Ord a] (xs: List a) (most: a) (found: List.maximum xs = Some most): (most ∈ xs) ∧ ((x: a) → x ∈ xs → x <= most) :=
  match xs with
    | [] => Void.exfalso (Option.noneNotSome most found)
    | [y, ..ys] =>
      let same := Option.someInjective (List.foldLeft ys y Ord.max) most found
      Both
        (match List.foldMaxMember ys y with
          | Inl isY => Inl (Eq.sym (Eq.trans (Eq.sym same) isY))
          | Inr member => Inr (rewrite same at member))
        (x member =>
          rewrite Eq.sym same in
            match member with
              | Inl isY => rewrite Eq.sym isY in List.foldMaxGeStart ys y
              | Inr inRest => List.foldMaxGeMember ys y x inRest)

--| A list with an element has a greatest one: it isn't `None`.
theorem List.maximumExists [auto ord: Ord a]: (xs: List a) → (x: a) → x ∈ xs → ∃ (most: a) => List.maximum xs = Some most
  | [], x, member => Void.exfalso member
  | [y, ..ys], x, member => Witness (List.foldLeft ys y Ord.max) rfl

theorem List.maximumNone [auto ord: Ord a] (xs: List a) (none: List.maximum xs = None) (x: a) (member: x ∈ xs): Void :=
  match xs with
    | [] => member
    | [y, ..ys] => Option.someNotNone (List.foldLeft ys y Ord.max) none

--| Lists with the same members have the same greatest member.
theorem List.maximumSameMembers [auto ord: Ord a] (xs: List a) (ys: List a) (into: (v: a) → v ∈ xs → v ∈ ys) (back: (v: a) → v ∈ ys → v ∈ xs):
    List.maximum xs = List.maximum ys :=
  match mx: List.maximum xs with
    | None =>
      match my: List.maximum ys with
        | None => rfl
        | Some y => Void.exfalso (List.maximumNone xs mx y (back y (List.maximumSome ys y my).left))
    | Some x =>
      match my: List.maximum ys with
        | None => Void.exfalso (List.maximumNone ys my x (into x (List.maximumSome xs x mx).left))
        | Some y =>
          let (Both xIn xMost) := List.maximumSome xs x mx
          let (Both yIn yMost) := List.maximumSome ys y my
          Eq.cong Some (Ord.leAntisymm x y (yMost x (into x xIn)) (xMost y (back y yIn)))

test "List.maximum and List.minimum" := List.maximum [3, 9, 2] == Some 9 ∧ List.minimum [3, 9, 2] == Some 2 ∧ List.maximum ([]: List Nat) == None

--| An element that passes makes `List.any` true.
theorem List.anyOfMem: (xs: List a) → (q: a → Bool) → (y: a) → (qy: q y = True) → y ∈ xs → List.any xs q = True
  | [], q, y, qy, m => Void.exfalso m
  | [x, ..xs], q, y, qy, Inl e => rewrite e, qy in rfl
  | [x, ..xs], q, y, qy, Inr m =>
    match c: q x with
      | True => rfl
      | False => List.anyOfMem xs q y qy m

--| When `List.any` is true, some element of the list passes.
theorem List.anyTrueElim: (xs: List a) → (p: a → Bool) → (goal: Prop) → List.any xs p = True → (cont: (x: a) → x ∈ xs → p x = True → goal) → goal
  | [], p, goal, h, k => Void.exfalso (Bool.falseNotTrue h)
  | [z, ..zs], p, goal, h, k =>
    match c: p z with
      | True => k z (Inl rfl) c
      | False => List.anyTrueElim zs p goal h (x inZs px => k x (Inr inZs) px)

--| `List.contains xs x` is `True` exactly when `x` is in `xs`.
theorem List.memContains [auto eq: DecEq a] (xs: List a) (x: a): (List.contains xs x = True) ↔ (x ∈ xs) := {
  forward = found =>
    List.anyTrueElim xs (member => member == x) (x ∈ xs) found (member isIn same => rewrite <- DecEq.sound member x same in isIn),
  backward = isIn => List.anyOfMem xs (member => member == x) x (DecEq.refl x) isIn
}

--| In a list without repeats, a value matches at most one element, and exactly
--| one when it is a member: `xs.count (== v)` is 1 if `xs.contains v` and 0 if
--| not. With [`List.lengthFilter`] this turns "the filter keeps exactly one"
--| into `xs.contains v`, e.g. for a fixed list of allowed names. The `Distinct`
--| argument for a literal list is `byDecision` (`import Std (byDecision)`);
--| it is not filled in by `auto`.
--| Example: `List.countEqDistinct "b" ["a", "b", "c"] byDecision` says
--| `["a", "b", "c"].count (== "b") = Bool.toNat (["a", "b", "c"].contains "b")`.
theorem List.countEqDistinct [auto eq: DecEq a] (v: a): (xs: List a) → List.Distinct xs → List.count xs (== v) = Bool.toNat (List.contains xs v)
  | [], d => rfl
  | [y, ..ys], Both notMem d =>
    Eq.trans
      (Eq.trans (List.countCons ys y (== v)) (Eq.cong (n => Bool.toNat (y == v) + n) (List.countEqDistinct v ys d)))
      (match same: y == v with
        | True =>
          match later: List.contains ys v with
            | True => Void.exfalso (notMem (rewrite DecEq.sound y v same in (List.memContains ys v).forward later))
            | False => rfl
        | False => rfl)

--| What `(.find p)` finds passes any other test some element passes.
theorem List.findAny (xs: List a) (p: a → Bool) (q: a → Bool) (y: a) (qy: q y = True) (h: List.find xs p = Some y): List.any xs q = True :=
  match List.findSome xs p y h with
    | Both py m => List.anyOfMem xs q y qy m

--| With distinct keys, finding by an element's key finds that element (and
--| [`List.findKey`], std/List/SortLemmas.sw, says what is found has the key).
theorem List.findKeyDistinct [auto eq: DecEq k] (key: a → k): (xs: List a) → List.Distinct (List.map xs key) → (x: a) → x ∈ xs →
    List.find xs (y => key y == key x) = Some x
  | [], d, x, m => Void.exfalso m
  | [z, ..zs], Both notMem d, x, Inl e => rewrite e, DecEq.refl (key x) in rfl
  | [z, ..zs], Both notMem d, x, Inr m =>
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

--| A key of part of the list is a key of the list.
theorem List.memMapOfSub (key: a → k) (s: List a) (xs: List a) (sub: (y: a) → y ∈ s → y ∈ xs) (z: k)
    (m: z ∈ List.map s key): z ∈ List.map xs key :=
  List.anyElim (y => key y = z) (z ∈ List.map xs key) s (List.memMapAny s key z m)
    (y inS e => rewrite <- e in List.memMap xs y (sub y inS) key)

--| Keeping some elements keeps their keys distinct.
theorem List.distinctMapFilter: (xs: List a) → (key: a → k) → (p: a → Bool) → List.Distinct (List.map xs key) →
    List.Distinct (List.map (List.filter xs p) key)
  | [], key, p, d => Trivial
  | [x, ..xs], key, p, Both notMem d =>
    match e: p x with
      | True =>
        Both
          (m => notMem (List.memMapOfSub key (List.filter xs p) xs (y inFiltered => match List.memFilter xs p y inFiltered with
            | Both inXs py => inXs) (key x) m))
          (List.distinctMapFilter xs key p d)
      | False => List.distinctMapFilter xs key p d

--| Keeping some elements keeps them distinct.
theorem List.distinctFilter: (xs: List a) → (p: a → Bool) → List.Distinct xs → List.Distinct (List.filter xs p)
  | [], p, d => Trivial
  | [x, ..xs], p, Both notMem d =>
    match e: p x with
      | True => Both (m => notMem (And.left (List.memFilter xs p x m))) (List.distinctFilter xs p d)
      | False => List.distinctFilter xs p d

--| A key of a `filterMap`'s result is the key of an element it came from,
--| when each result has the key of its element.
theorem List.memMapFilterMap (f: a → Option b) (ka: a → k) (kb: b → k) (hk: (x: a) → (y: b) → f x = Some y → kb y = ka x) (z: k):
    (xs: List a) → z ∈ List.map (List.filterMap xs f) kb → z ∈ List.map xs ka
  | [], m => m
  | [x, ..xs], m =>
    match e: f x with
      | None => Inr (List.memMapFilterMap f ka kb hk z xs m)
      | Some y =>
        match m with
          | Inl q => Inl (Eq.trans (Eq.sym (hk x y e)) q)
          | Inr r => Inr (List.memMapFilterMap f ka kb hk z xs r)

--| `filterMap` keeps keys distinct, when `f` keeps each element's key.
theorem List.distinctMapFilterMap (f: a → Option b) (ka: a → k) (kb: b → k) (hk: (x: a) → (y: b) → f x = Some y → kb y = ka x):
    (xs: List a) → List.Distinct (List.map xs ka) → List.Distinct (List.map (List.filterMap xs f) kb)
  | [], d => Trivial
  | [x, ..xs], Both notMem d =>
    match e: f x with
      | None => List.distinctMapFilterMap f ka kb hk xs d
      | Some y =>
        Both (m => notMem (rewrite <- hk x y e in List.memMapFilterMap f ka kb hk (kb y) xs m))
          (List.distinctMapFilterMap f ka kb hk xs d)

--| Two lists with distinct keys and no key in common, joined, have distinct keys.
theorem List.distinctMapAppend (key: a → k) (xs: List a) (ys: List a) (dx: List.Distinct (List.map xs key)) (dy: List.Distinct (List.map ys key))
    (dj: List.Disjoint (List.map xs key) (List.map ys key)): List.Distinct (List.map (List.append xs ys) key) :=
  rewrite List.mapAppend xs ys key in List.distinctAppend (List.map xs key) (List.map ys key) dx dy dj

theorem List.distinctMapFilterExample: List.Distinct (List.map (List.filter [1, 2] (x => Nat.leq 2 x)) Succ) :=
  List.distinctMapFilter [1, 2] Succ (x => Nat.leq 2 x) List.distinctMapExample

--| `findMap` is the first of the `filterMap` results, found without building
--| the rest.
theorem List.findMapIsHeadFilterMap: (xs: List a) → (f: a → Option b) → List.findMap xs f = List.head (List.filterMap xs f)
  | [], f => rfl
  | [x, ..xs], f =>
    match f x with
      | None => List.findMapIsHeadFilterMap xs f
      | Some y => rfl

theorem List.lengthTails: (xs: List a) → List.length (List.tails xs) = Succ (List.length xs)
  | [] => rfl
  | [x, ..xs] => Eq.cong Succ (List.lengthTails xs)

theorem List.splitAtFst (xs: List a) (n: Nat): Pair.fst (List.splitAt xs n) = List.take xs n := rfl

--| The loop's prefix is `takeWhile`'s, after what it had taken.
theorem List.spanOntoTakeDrop (p: a → Bool): (taken: List a) → (xs: List a) →
    List.spanOnto taken p xs = MkPair (List.reverseOnto taken (List.takeWhile xs p)) (List.dropWhile xs p)
  | taken, [] => rfl
  | taken, [x, ..xs] =>
    match p x with
      | True => List.spanOntoTakeDrop p [x, ..taken] xs
      | False => rfl

--| `span` is `takeWhile` and `dropWhile`.
-- (its definition before it became one pass)
theorem List.spanTakeDrop (xs: List a) (p: a → Bool): List.span xs p = MkPair (List.takeWhile xs p) (List.dropWhile xs p) :=
  List.spanOntoTakeDrop p [] xs

theorem List.spanExample: List.span [1, 2, 3, 1] (x => Nat.leq x 2) = MkPair [1, 2] [3, 1] := rfl

--| `takeWhile` over a prefix that passes: the prefix, then what passes after.
theorem List.takeWhileAppend (p: a → Bool) (rest: List a): (prefix: List a) → List.all prefix p = True →
    List.takeWhile (List.append prefix rest) p = List.append prefix (List.takeWhile rest p)
  | [], all => rfl
  | [x, ..xs], all =>
    match p x with
      | True => Eq.cong (Cons x) (List.takeWhileAppend p rest xs all)
      | False => Void.exfalso (Bool.falseNotTrue all)

--| `dropWhile` over a prefix that passes drops it.
theorem List.dropWhileAppend (p: a → Bool) (rest: List a): (prefix: List a) → List.all prefix p = True →
    List.dropWhile (List.append prefix rest) p = List.dropWhile rest p
  | [], all => rfl
  | [x, ..xs], all =>
    match p x with
      | True => List.dropWhileAppend p rest xs all
      | False => Void.exfalso (Bool.falseNotTrue all)

--| Where `takeWhile` takes nothing, `dropWhile` drops nothing.
theorem List.dropWhileStops (p: a → Bool): (xs: List a) → List.takeWhile xs p = [] → List.dropWhile xs p = xs
  | [], stops => rfl
  | [x, ..xs], stops =>
    match p x with
      | True => Void.exfalso (List.consNotNil x (List.takeWhile xs p) stops)
      | False => rfl

--| What `takeWhile` takes and `dropWhile` leaves make up the list.
theorem List.takeWhileDropWhile (p: a → Bool): (xs: List a) → List.append (List.takeWhile xs p) (List.dropWhile xs p) = xs
  | [] => rfl
  | [x, ..xs] =>
    match p x with
      | True => Eq.cong (Cons x) (List.takeWhileDropWhile p xs)
      | False => rfl

--| Taking from a mapped list while `p` holds is mapping what is taken from the
--| list while `p` of the mapped element holds.
theorem List.takeWhileMap (f: a → b) (p: b → Bool): (xs: List a) →
    List.takeWhile (List.map xs f) p = List.map (List.takeWhile xs (x => p (f x))) f
  | [] => rfl
  | [x, ..rest] => rewrite List.takeWhileMap f p rest in cases

--| Counting up from `start`, `takeWhile` stops by `cutoff` when nothing from
--| `cutoff` on passes, so any count reaching it gives the same.
theorem List.takeWhileRangeCutoff (p: Nat → Bool) (cutoff: Nat) (fails: (k: Nat) → cutoff ≤ k → p k = False):
    (n: Nat) → (m: Nat) → (start: Nat) → cutoff ≤ start + n → cutoff ≤ start + m →
    List.takeWhile (List.rangeFrom n start) p = List.takeWhile (List.rangeFrom m start) p
  | Zero, Zero, start, reachesN, reachesM => rfl
  | Zero, Succ m, start, reachesN, reachesM => rewrite fails start omega in rfl
  | Succ n, Zero, start, reachesN, reachesM => rewrite fails start omega in rfl
  | Succ n, Succ m, start, reachesN, reachesM =>
    match passes: p start with
      | True => rewrite List.takeWhileRangeCutoff p cutoff fails n m (Succ start) omega omega in rfl
      | False => rfl

--| Everything `takeWhile` takes passes.
theorem List.allTakeWhile (p: a → Bool): (xs: List a) → List.all (List.takeWhile xs p) p = True
  | [] => rfl
  | [x, ..xs] =>
    match e: p x with
      | True => rewrite e in List.allTakeWhile p xs
      | False => rfl

--| `span` of a prefix that passes, then a rest that starts with an element
--| that doesn't (or is empty), splits between the two.
theorem List.spanAppend (p: a → Bool) (taken: List a) (rest: List a) (all: List.all taken p = True)
    (stops: List.takeWhile rest p = []):
    List.span (List.append taken rest) p = MkPair taken rest :=
  rewrite List.spanTakeDrop (List.append taken rest) p, List.takeWhileAppend p rest taken all, stops, List.appendNil taken,
    List.dropWhileAppend p rest taken all, List.dropWhileStops p rest stops in
    rfl

-- `map` through the other list functions (SW-198, day 8).

theorem List.mapAppend: (xs: List a) → (ys: List a) → (f: a → b) → List.map (List.append xs ys) f = List.append (List.map xs f) (List.map ys f)
  | [], ys, f => rfl
  | [x, ..xs], ys, f => rewrite List.mapAppend xs ys f

theorem List.takeMap: (xs: List a) → (k: Nat) → (f: a → b) → List.take (List.map xs f) k = List.map (List.take xs k) f
  | xs, Zero, f => rfl
  | [], Succ k, f => rfl
  | [x, ..xs], Succ k, f => rewrite List.takeMap xs k f

--| The first `k` of two lists combined are the first `k` of each combined.
theorem List.takeZipWith (f: a → b → c): (xs: List a) → (ys: List b) → (k: Nat) →
    List.take (List.zipWith xs ys f) k = List.zipWith (List.take xs k) (List.take ys k) f
  | xs, ys, Zero => rfl
  | [], ys, Succ k => rfl
  | [x, ..xs], [], Succ k => rfl
  | [x, ..xs], [y, ..ys], Succ k => Eq.cong (Cons (f x y)) (List.takeZipWith f xs ys k)

theorem List.takeZipWithExample: List.take (List.zipWith [1, 2, 3] [10, 20, 30] Nat.add) 2 = List.zipWith [1, 2] [10, 20] Nat.add :=
  List.takeZipWith Nat.add [1, 2, 3] [10, 20, 30] 2

theorem List.foldLeftMap: (xs: List a) → (z: c) → (f: c → b → c) → (g: a → b) →
    List.foldLeft (List.map xs g) z f = List.foldLeft xs z (acc x => f acc (g x))
  | [], z, f, g => rfl
  | [x, ..xs], z, f, g => List.foldLeftMap xs (f z (g x)) f g

--| A fold over `zipWith` folds over the pairs, combining each as it goes.
theorem List.foldLeftZipWith (g: a → b → c) (f: d → c → d): (xs: List a) → (ys: List b) → (z: d) →
    List.foldLeft (List.zipWith xs ys g) z f = List.foldLeft (List.zip xs ys) z (acc p => f acc (g p.fst p.snd))
  | [], ys, z => rfl
  | [x, ..xs], [], z => rfl
  | [x, ..xs], [y, ..ys], z => List.foldLeftZipWith g f xs ys (f z (g x y))

--| A fold over `zip xs ys` whose step uses only each pair's first element is
--| the fold over `xs`, when `ys` is at least as long.
theorem List.foldLeftZipLeft (step: c → Pair a b → c) (f: c → a → c) (same: (acc: c) → (x: a) → (y: b) → step acc (MkPair x y) = f acc x):
    (xs: List a) → (ys: List b) → (z: c) → List.length xs ≤ List.length ys → List.foldLeft (List.zip xs ys) z step = List.foldLeft xs z f
  | [], ys, z, le => rfl
  | [x, ..xs], [], z, le => Void.exfalso (Bool.falseNotTrue le)
  | [x, ..xs], [y, ..ys], z, le => rewrite same z x y in List.foldLeftZipLeft step f same xs ys (f z x) le

theorem List.foldRightZipLeft (step: Pair a b → c → c) (f: a → c → c) (same: (x: a) → (y: b) → (acc: c) → step (MkPair x y) acc = f x acc):
    (xs: List a) → (ys: List b) → (z: c) → List.length xs ≤ List.length ys → List.foldRight (List.zip xs ys) z step = List.foldRight xs z f
  | [], ys, z, le => rfl
  | [x, ..xs], [], z, le => Void.exfalso (Bool.falseNotTrue le)
  | [x, ..xs], [y, ..ys], z, le =>
    calc List.foldRight [MkPair x y, ..List.zip xs ys] z step
      _ = step (MkPair x y) (List.foldRight (List.zip xs ys) z step) := List.foldRightCons (List.zip xs ys) (MkPair x y) z step
      _ = f x (List.foldRight (List.zip xs ys) z step) := same x y (List.foldRight (List.zip xs ys) z step)
      _ = f x (List.foldRight xs z f) := rewrite List.foldRightZipLeft step f same xs ys z le
      _ = List.foldRight [x, ..xs] z f := Eq.sym (List.foldRightCons xs x z f)

test "List.foldLeftZipLeft" := List.foldLeft (List.zip [1, 2, 3] ["a", "b", "c", "d"]) 0 (acc pair => acc + pair.fst) == 6

theorem List.anyMap: (xs: List a) → (p: b → Bool) → (f: a → b) → List.any (List.map xs f) p = List.any xs (x => p (f x))
  | [], p, f => rfl
  | [x, ..xs], p, f => rewrite List.anyMap xs p f

--| `List.all` of a `map` is `List.all` of the composed test. ([`List.allMap`] is about the proposition `List.All`.)
theorem List.allMapBool: (xs: List a) → (p: b → Bool) → (f: a → b) → List.all (List.map xs f) p = List.all xs (x => p (f x))
  | [], p, f => rfl
  | [x, ..xs], p, f => rewrite List.allMapBool xs p f in rfl

--| Some element of a `flatMap` passes exactly when some list it is made of
--| has one.
theorem List.anyFlatMap (f: a → List b) (p: b → Bool): (xs: List a) → List.any (List.flatMap xs f) p = List.any xs (x => List.any (f x) p)
  | [] => rfl
  | [x, ..xs] =>
    Eq.trans (List.anyAppend (f x) (List.flatMap xs f) p) (Eq.cong (later => List.any (f x) p ∨ later) (List.anyFlatMap f p xs))

--| `List.any` of an `∨` is the `∨` of the `List.any`s.
theorem List.anyOr (p: a → Bool) (q: a → Bool): (xs: List a) → List.any xs (x => p x ∨ q x) = (List.any xs p ∨ List.any xs q)
  | [] => rfl
  | [x, ..xs] => rewrite List.anyOr p q xs in cases

--| Two `List.any`s, in either order.
theorem List.anyComm (related: a → b → Bool) (ys: List b): (xs: List a) →
    List.any xs (x => List.any ys (y => related x y)) = List.any ys (y => List.any xs (x => related x y))
  | [] => Eq.sym (List.anyFalse ys (y => False) (y => rfl))
  | [x, ..xs] =>
    rewrite List.anyComm related ys xs in
      Eq.sym (List.anyOr (y => related x y) (y => List.any xs (other => related other y)) ys)

theorem List.anyFlatMapExample: List.any (List.flatMap [1, 2] (x => [x, x * 10])) (== 20) = List.any [1, 2] (x => List.any [x, x * 10] (== 20)) :=
  List.anyFlatMap (x => [x, x * 10]) (== 20) [1, 2]

theorem List.countMap (xs: List a) (p: b → Bool) (f: a → b): List.count (List.map xs f) p = List.count xs (x => p (f x)) :=
  List.foldLeftMap xs 0 (n x => Nat.succIf n (p x)) f

theorem List.occurrencesMap: (xs: List a) → (f: a → b) → (p: b → Bool) → List.occurrences (List.map xs f) p = List.occurrences xs (x => p (f x))
  | [], f, p => rfl
  | [x, ..xs], f, p => rewrite List.occurrencesMap xs f p in rfl

--| Mapping both lists of a permutation keeps it one.
theorem List.permMap (xs: List a) (ys: List a) (h: List.Perm xs ys) (f: a → b): List.Perm (List.map xs f) (List.map ys f) :=
  p => rewrite List.occurrencesMap xs f p, List.occurrencesMap ys f p in h (x => p (f x))

--| Counting what `(.filter keep)` kept is counting what passes both tests.
theorem List.occurrencesFilter: (xs: List a) → (keep: a → Bool) → (p: a → Bool) →
    List.occurrences (List.filter xs keep) p = List.occurrences xs (x => p x ∧ keep x)
  | [], keep, p => rfl
  | [x, ..xs], keep, p =>
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

--| The first k numbers of a longer run.
theorem List.takeRangeFrom: (k: Nat) → (n: Nat) → (s: Nat) → k ≤ n → List.take (List.rangeFrom n s) k = List.rangeFrom k s
  | Zero, n, s, h => rfl
  | Succ k, Zero, s, h => Void.exfalso (Bool.falseNotTrue h)
  | Succ k, Succ n, s, h => rewrite List.takeRangeFrom k n (Succ s) h

--| The pairs of a mapped list are the list's pairs, mapped.
theorem List.pairsMap: (xs: List a) → (f: a → b) → List.pairs (List.map xs f) = List.map (List.pairs xs) (p => MkPair (f (Pair.fst p)) (f (Pair.snd p)))
  | [], f => rfl
  | [x, ..xs], f =>
    rewrite List.mapAppend (List.map xs (y => MkPair x y)) (List.pairs xs) (p => MkPair (f (Pair.fst p)) (f (Pair.snd p))),
      List.mapMap xs (y => MkPair (f x) y) f, List.mapMap xs (p => MkPair (f (Pair.fst p)) (f (Pair.snd p))) (y => MkPair x y),
      List.pairsMap xs f

--| A `filterMap` that keeps every element, changed by `g`, is a `map`.
theorem List.filterMapSomeMem (xs: List a) (f: a → Option b) (g: a → b) (h: (x: a) → x ∈ xs → f x = Some (g x)):
    List.filterMap xs f = List.map xs g :=
  Eq.trans (List.filterMapCongMem xs f (x => Some (g x)) h) (List.filterMapSome xs g)

--| A `filterMap` that keeps every element as it is gives the list back.
theorem List.filterMapAll (f: a → Option a): (xs: List a) → ((x: a) → x ∈ xs → f x = Some x) → List.filterMap xs f = xs
  | [], h => rfl
  | [x, ..xs], h => rewrite h x (Inl rfl) in Eq.cong (Cons x) (List.filterMapAll f xs (y m => h y (Inr m)))

--| `filterMap` after `map`, when each element maps back to itself.
theorem List.filterMapMapSelf (g: a → b) (f: b → Option a) (xs: List a) (h: (x: a) → x ∈ xs → f (g x) = Some x):
    List.filterMap (List.map xs g) f = xs :=
  Eq.trans (List.filterMapMap xs f g) (List.filterMapAll (x => f (g x)) xs h)

test "List.pairsMap" := (List.map [1, 2, 3] Succ).pairs == List.map [1, 2, 3].pairs (p => MkPair (Succ p.fst) (Succ p.snd))

-- the largest by folding Nat.max --------------------------------------------

--| The fold starts at `start` and never goes down.
theorem List.foldMaxGe: (xs: List Nat) → (start: Nat) → start ≤ List.foldLeft xs start Nat.max
  | [], start => Nat.leRefl start
  | [x, ..xs], start => Nat.leTrans start (Nat.max start x) (List.foldLeft xs (Nat.max start x) Nat.max) (Nat.leMaxLeft start x) (List.foldMaxGe xs (Nat.max start x))

--| Every element is at most the largest.
theorem List.leFoldMax: (xs: List Nat) → (x: Nat) → (start: Nat) → x ∈ xs → x ≤ List.foldLeft xs start Nat.max
  | [], x, start, m => Void.exfalso m
  | [y, ..ys], x, start, Inl e => rewrite <- e in Nat.leTrans y (Nat.max start y) (List.foldLeft ys (Nat.max start y) Nat.max) (Nat.leMaxRight start y) (List.foldMaxGe ys (Nat.max start y))
  | [y, ..ys], x, start, Inr m => List.leFoldMax ys x (Nat.max start y) m

--| The largest is the start or one of the elements.
theorem List.foldMaxMem: (xs: List Nat) → (start: Nat) → (List.foldLeft xs start Nat.max = start) ∨ (List.foldLeft xs start Nat.max ∈ xs)
  | [], start => Inl rfl
  | [y, ..ys], start =>
    match List.foldMaxMem ys (Nat.max start y) with
      | Inr m => Inr (Inr m)
      | Inl e =>
        match h: Nat.leq start y with
          | True => Inr (Inl (Eq.sym e))
          | False => Inl e

-- lengths, and sums over ranges ---------------------------------------------

--| Zipping two lists of at least n elements gives at least n.
theorem List.lengthZipWithAtLeast: (u: List a) → (n: Nat) → (v: List b) → n ≤ List.length u → n ≤ List.length v → (f: a → b → c) →
    n ≤ List.length (List.zipWith u v f)
  | u, Zero, v, hu, hv, f => rfl
  | [], Succ n, v, hu, hv, f => hu
  | [x, ..xs], Succ n, [], hu, hv, f => hv
  | [x, ..xs], Succ n, [y, ..ys], hu, hv, f => List.lengthZipWithAtLeast xs n ys hu hv f

--| Running results: one more than the elements, the start first.
theorem List.lengthScanLeft: (xs: List a) → (start: b) → (f: b → a → b) → List.length (List.scanLeft xs start f) = Succ (List.length xs)
  | [], start, f => rfl
  | [x, ..xs], start, f => Eq.cong Succ (List.lengthScanLeft xs (f start x) f)

--| A sum over the numbers below b is the sum below t and the sum from t up to b.
theorem List.sumByRangeSplit (f: Nat → Nat) (t: Nat) (b: Nat) (tb: t ≤ b):
    List.sumBy (List.rangeFrom b 0) f = List.sumBy (List.rangeFrom t 0) f + List.sumBy (List.rangeFrom (b - t) t) f :=
  calc List.sumBy (List.rangeFrom b 0) f
    _ = List.sumBy (List.rangeFrom (t + (b - t)) 0) f := Eq.cong (n => List.sumBy (List.rangeFrom n 0) f) (Eq.sym (Nat.addSubCancel t b tb))
    _ = List.sumBy (List.append (List.rangeFrom t 0) (List.rangeFrom (b - t) (0 + t))) f := Eq.cong (.sumBy f) (List.rangeFromAppend t (b - t) 0)
    _ = List.sumBy (List.rangeFrom t 0) f + List.sumBy (List.rangeFrom (b - t) t) f := List.sumByAppend (List.rangeFrom t 0) (List.rangeFrom (b - t) t) f

-- sums of zero -----------------------------------------------------------------

--| A sum of numbers is 0 only if each is.
theorem List.sumByZeroElim: (xs: List a) → (f: a → Nat) → List.sumBy xs f = 0 → (x: a) → x ∈ xs → f x = 0
  | [], f, h, x, m => Void.exfalso m
  | [y, ..ys], f, h, x, Inl e => rewrite <- e in (Nat.addEqZero (f y) (List.sumBy ys f) (Eq.trans (Eq.sym (List.sumByCons ys y f)) h)).left
  | [y, ..ys], f, h, x, Inr m => List.sumByZeroElim ys f (Nat.addEqZero (f y) (List.sumBy ys f) (Eq.trans (Eq.sym (List.sumByCons ys y f)) h)).right x m

theorem List.sumByZeroIntro: (xs: List a) → (f: a → Nat) → ((x: a) → x ∈ xs → f x = 0) → List.sumBy xs f = 0
  | [], f, h => rfl
  | [y, ..ys], f, h => rewrite List.sumByCons ys y f, h y (Inl rfl), List.sumByZeroIntro ys f (x m => h x (Inr m)) in rfl

-- filtering what can't pass anyway ------------------------------------------

--| Dropping elements that fail `q`, when only elements that pass `q` can pass
--| `p`, changes neither `any p` nor `count p`.
theorem List.anyFilter: (xs: List a) → (p: a → Bool) → (q: a → Bool) → (h: (x: a) → p x = True → q x = True) → List.any (List.filter xs q) p = List.any xs p
  | [], p, q, h => rfl
  | [x, ..xs], p, q, h =>
    match e: q x with
      | True => rewrite List.anyFilter xs p q h in rfl
      | False =>
        match f: p x with
          | True => Void.exfalso (Bool.falseNotTrue (Eq.trans (Eq.sym e) (h x f)))
          | False => List.anyFilter xs p q h

theorem List.countFromFilter: (xs: List a) → (n: Nat) → (p: a → Bool) → (q: a → Bool) → (h: (x: a) → p x = True → q x = True) →
    List.foldLeft (List.filter xs q) n (k x => Nat.succIf k (p x)) = List.foldLeft xs n (k x => Nat.succIf k (p x))
  | [], n, p, q, h => rfl
  | [x, ..xs], n, p, q, h =>
    match e: q x with
      | True => List.countFromFilter xs (Nat.succIf n (p x)) p q h
      | False =>
        match f: p x with
          | True => Void.exfalso (Bool.falseNotTrue (Eq.trans (Eq.sym e) (h x f)))
          | False => List.countFromFilter xs n p q h

theorem List.countFilter (xs: List a) (p: a → Bool) (q: a → Bool) (h: (x: a) → p x = True → q x = True): List.count (List.filter xs q) p = List.count xs p :=
  List.countFromFilter xs 0 p q h

-- membership through zip, take, drop and filter ------------------------------

--| A pair in `List.zip xs ys` is an element of `xs` with one of `ys`.
theorem List.memZip (p: (a, b)): (xs: List a) → (ys: List b) → p ∈ List.zip xs ys → (p.fst ∈ xs) ∧ (p.snd ∈ ys)
  | [], ys, m => Void.exfalso m
  | [x, ..xs], [], m => Void.exfalso m
  | [x, ..xs], [y, ..ys], Inl e => rewrite <- e in Both (Inl rfl) (Inl rfl)
  | [x, ..xs], [y, ..ys], Inr m =>
    match List.memZip p xs ys m with
      | Both inXs inYs => Both (Inr inXs) (Inr inYs)

theorem List.memTake: (xs: List a) → (v: a) → (n: Nat) → v ∈ List.take xs n → v ∈ xs
  | xs, v, Zero, m => Void.exfalso m
  | [], v, Succ n, m => m
  | [x, ..xs], v, Succ n, Inl e => Inl e
  | [x, ..xs], v, Succ n, Inr m => Inr (List.memTake xs v n m)

theorem List.memDrop: (xs: List a) → (v: a) → (n: Nat) → v ∈ List.drop xs n → v ∈ xs
  | xs, v, Zero, m => m
  | [], v, Succ n, m => m
  | [x, ..xs], v, Succ n, m => Inr (List.memDrop xs v n m)

--| What passes the test is kept.
theorem List.memFilterIntro: (xs: List a) → (p: a → Bool) → (v: a) → v ∈ xs → p v = True → v ∈ List.filter xs p
  | [], p, v, m, h => m
  | [x, ..xs], p, v, Inl e, h => rewrite <- e at h in (rewrite h in Inl e)
  | [x, ..xs], p, v, Inr m, h =>
    match e: p x with
      | True => Inr (List.memFilterIntro xs p v m h)
      | False => List.memFilterIntro xs p v m h

--| Filtering a mapped list is mapping the filtered list.
theorem List.filterOfMap: (xs: List a) → (q: b → Bool) → (g: a → b) → List.filter (List.map xs g) q = List.map (List.filter xs (x => q (g x))) g
  | [], q, g => rfl
  | [x, ..xs], q, g =>
    match e: q (g x) with
      | True => rewrite List.filterOfMap xs q g in rfl
      | False => List.filterOfMap xs q g

--| A pair in `List.pairs xs` is two elements of `xs`.
theorem List.memPairs (p: (a, a)): (xs: List a) → p ∈ List.pairs xs → (p.fst ∈ xs) ∧ (p.snd ∈ xs)
  | [], m => Void.exfalso m
  | [x, ..xs], m =>
    match List.memAppend p (List.map xs (y => (x, y))) (List.pairs xs) m with
      | Inl first =>
        List.anyElim (y => (x, y) = p) ((p.fst ∈ [x, ..xs]) ∧ (p.snd ∈ [x, ..xs])) xs (List.memMapAny xs (y => (x, y)) p first)
          (y inXs e => rewrite <- e in Both (Inl rfl) (Inr inXs))
      | Inr later =>
        match List.memPairs p xs later with
          | Both one other => Both (Inr one) (Inr other)

--| A pair in a list mapped to pairs with a fixed first part: that part, and a member of the list.
theorem List.memMapPair (c: a) (u: a) (v: b) (xs: List b): ((u, v) ∈ List.map xs (y => (c, y))) ↔ ((u = c) ∧ (v ∈ xs)) :=
  {
    forward = m =>
      Exists.elim (List.memMapElim (y => (c, y)) (u, v) xs m) (y both =>
        Both (Eq.sym (Pair.mkInjectiveFst _ _ _ _ (And.right both)))
          (rewrite <- Pair.mkInjectiveSnd _ _ _ _ (And.right both) in And.left both)),
    backward = both => rewrite And.left both in List.memMap xs v (And.right both) (y => (c, y))
  }

--| Taking apart a pair of `List.pairs (Cons x rest)`: `x` with a later element, or a pair of `rest`.
--| (Each way round, so a proof can use it both to take a pair apart and to put one together.)
theorem List.memPairsCons (u: a) (v: a) (x: a) (rest: List a):
    ((u, v) ∈ List.pairs [x, ..rest]) ↔ (((u = x) ∧ (v ∈ rest)) ∨ ((u, v) ∈ List.pairs rest)) :=
  {
    forward = m =>
      match List.memAppend (u, v) (List.map rest (y => (x, y))) (List.pairs rest) m with
        | Inl inMap => Inl ((List.memMapPair x u v rest).forward inMap)
        | Inr inRest => Inr inRest,
    backward = h =>
      match h with
        | Inl both => List.memAppendLeft (u, v) (List.map rest (y => (x, y))) (List.pairs rest) ((List.memMapPair x u v rest).backward both)
        | Inr inRest => List.memAppendRight (u, v) (List.map rest (y => (x, y))) (List.pairs rest) inRest
  }

theorem List.memPairsConsExample: (1, 3) ∈ List.pairs [1, 2, 3] := (List.memPairsCons 1 3 1 [2, 3]).backward (Inl (Both rfl (Inr (Inl rfl))))

--| The last element, if there is one, is an element.
theorem List.lastMem: (xs: List a) → (x: a) → List.last xs = Some x → x ∈ xs
  | [], x, h => Void.exfalso (Option.noneNotSome x h)
  | [y], x, h => Inl (Option.someInjective y x h)
  | [y, z, ..zs], x, h => Inr (List.lastMem [z, ..zs] x h)

theorem List.lastMemExample: 3 ∈ [1, 2, 3] := List.lastMem [1, 2, 3] 3 rfl

--| The last element of a list with `x` added at the end is `x`.
theorem List.lastSnoc (x: a): (xs: List a) → List.last (List.append xs [x]) = Some x
  | [] => rfl
  | [y] => rfl
  | [y, z, ..zs] => List.lastSnoc x [z, ..zs]

--| `filterMap` keeps `y` when an element maps to `Some y`.
theorem List.memFilterMapIntro (f: a → Option b) (x: a) (y: b): (xs: List a) → x ∈ xs → f x = Some y → y ∈ List.filterMap xs f
  | [], m, e => Void.exfalso m
  | [z, ..zs], Inl q, e => rewrite q, e in Inl rfl
  | [z, ..zs], Inr m, e =>
    match c: f z with
      | None => List.memFilterMapIntro f x y zs m e
      | Some w => Inr (List.memFilterMapIntro f x y zs m e)

--| What `filterMap` keeps is `Some` of some element.
theorem List.memFilterMapElim (f: a → Option b) (y: b): (xs: List a) → y ∈ List.filterMap xs f → List.Any (x => f x = Some y) xs
  | [], m => m
  | [z, ..zs], m =>
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
theorem List.memFilterMap (f: a → Option b) (y: b) (xs: List a): (y ∈ List.filterMap xs f) ↔ (∃ (x: a) => (x ∈ xs) ∧ (f x = Some y)) := {
  forward = m => List.anyMember (x => f x = Some y) xs (List.memFilterMapElim f y xs m),
  backward = found => Exists.elim found (x both => List.memFilterMapIntro f x y xs (And.left both) (And.right both))
}

--| `somes` keeps `y` exactly when `Some y` is an element.
theorem List.memSomes (y: a) (xs: List (Option a)): (y ∈ List.somes xs) ↔ (Some y ∈ xs) := {
  forward = m => Exists.elim ((List.memFilterMap id y xs).forward m) (x both => Eq.subst (z => z ∈ xs) (And.right both: x = Some y) (And.left both)),
  backward = m => (List.memFilterMap id y xs).backward (Witness (Some y) (Both m (rfl: id (Some y) = Some y)))
}

--| Everything `filterMap` keeps has `q` when every element's `Some` result
--| would; and back.
theorem List.allFilterMap (q: b → Prop) (f: a → Option b): (xs: List a) → List.All (x => (y: b) → f x = Some y → q y) xs → List.All q (List.filterMap xs f)
  | [], h => Trivial
  | [z, ..zs], Both hz h =>
    match c: f z with
      | None => List.allFilterMap q f zs h
      | Some w => Both (hz w rfl) (List.allFilterMap q f zs h)

theorem List.allFilterMapElim (q: b → Prop) (f: a → Option b): (xs: List a) → List.All q (List.filterMap xs f) → List.All (x => (y: b) → f x = Some y → q y) xs
  | [], h => Trivial
  | [z, ..zs], h =>
    match c: f z with
      | None => Both (y e => Void.exfalso (Option.noneNotSome y e)) (List.allFilterMapElim q f zs h)
      | Some w =>
        match h with
          | Both hw rest => Both (y e => rewrite <- Option.someInjective w y e in hw) (List.allFilterMapElim q f zs rest)

theorem List.memFilterMapExample: 4 ∈ List.filterMap [1, 2, 3] (x => if x == 2 then Some (x * 2) else None) :=
  List.memFilterMapIntro (x => if x == 2 then Some (x * 2) else None) 2 4 [1, 2, 3] (Inr (Inl rfl)) rfl

--| `List.all` and `List.any` (the `Bool`s a program computes) are `List.All`
--| and `List.Any` (the propositions proofs use), so a lemma needs only one
--| form.
theorem List.allToAll (p: a → Bool): (xs: List a) → List.all xs p = True → List.All (x => p x = True) xs
  | [], h => Trivial
  | [x, ..xs], h =>
    match c: p x with
      | True => Both rfl (List.allToAll p xs h)
      | False => Void.exfalso (Bool.falseNotTrue h)

theorem List.allOfAll (p: a → Bool): (xs: List a) → List.All (x => p x = True) xs → List.all xs p = True
  | [], h => rfl
  | [x, ..xs], Both px h => rewrite px in List.allOfAll p xs h

theorem List.allIff (xs: List a) (p: a → Bool): List.all xs p = True ↔ List.All (x => p x = True) xs :=
  { forward = List.allToAll p xs, backward = List.allOfAll p xs }

--| `List.all` holds of each member.
theorem List.allMember (p: a → Bool) (xs: List a) (all: List.all xs p = True) (x: a) (member: x ∈ xs): p x = True :=
  List.allMem (y => p y = True) x xs (List.allToAll p xs all) member

theorem List.anyToAny (p: a → Bool): (xs: List a) → List.any xs p = True → List.Any (x => p x = True) xs
  | [], h => Void.exfalso (Bool.falseNotTrue h)
  | [x, ..xs], h =>
    match c: p x with
      | True => Inl rfl
      | False => Inr (List.anyToAny p xs h)

theorem List.anyOfAny (p: a → Bool): (xs: List a) → List.Any (x => p x = True) xs → List.any xs p = True
  | [], h => Void.exfalso h
  | [x, ..xs], Inl px => rewrite px in rfl
  | [x, ..xs], Inr h =>
    match c: p x with
      | True => rfl
      | False => List.anyOfAny p xs h

theorem List.anyIff (xs: List a) (p: a → Bool): List.any xs p = True ↔ List.Any (x => p x = True) xs :=
  { forward = List.anyToAny p xs, backward = List.anyOfAny p xs }

--| Membership written with `any` and `==` is `x ∈ xs`. (`x ∈ xs` as a
--| `Bool` is `List.decMem`'s decision: [`Decidable.toBoolSound`] and
--| [`Decidable.toBoolOf`] take it to the proposition and back.)
theorem List.anyEqIff [auto eq: DecEq a] (x: a) (xs: List a): List.any xs (== x) = True ↔ x ∈ xs := {
  forward = h => List.anyTrueElim xs (== x) (x ∈ xs) h (y m e => rewrite <- DecEq.sound y x e in m),
  backward = m => List.anyOfMem xs (== x) x (DecEq.refl x) m
}

theorem List.allIffExample: List.All (x => Nat.leq 1 x = True) [1, 2, 3] := (List.allIff [1, 2, 3] (x => Nat.leq 1 x)).forward rfl

--| `any` is whether `find` finds something.
theorem List.anyFind (p: a → Bool): (xs: List a) → List.any xs p = Option.isSome (List.find xs p)
  | [] => rfl
  | [x, ..xs] =>
    match c: p x with
      | True => rfl
      | False => List.anyFind p xs

--| The first step, for induction, of running accumulations beside the elements, by computation.
--| `List.zipWith xs (List.scanLeft xs z f) g` is `g` of each element and the fold of the
--| elements before it ([`List.getOrZipWithScanLeft`], std/List/Index.sw). It
--| lays items end to end from `z`, say, with `f` adding an item's size and
--| `g` placing it.
theorem List.zipWithScanLeftCons (x: a) (xs: List a) (z: b) (f: b → a → b) (g: a → b → c):
    List.zipWith [x, ..xs] (List.scanLeft [x, ..xs] z f) g = [g x z, ..List.zipWith xs (List.scanLeft xs (f z x) f) g] := rfl

theorem List.zipWithScanLeftExample:
    List.zipWith [2, 3, 4] (List.scanLeft [2, 3, 4] 10 (offset width => offset + width)) (width offset => (offset, width)) = [(10, 2), (12, 3), (15, 4)] := rfl

--| Running accumulations beside the elements have one for each element.
theorem List.lengthZipWithScanLeft (f: b → a → b) (g: a → b → c): (xs: List a) → (z: b) →
    List.length (List.zipWith xs (List.scanLeft xs z f) g) = List.length xs
  | [], z => rfl
  | [x, ..xs], z => Eq.cong Succ (List.lengthZipWithScanLeft f g xs (f z x))

--| What `g` keeps of an element (`h`, an id say) doesn't depend on the other
--| list, so mapping it over the zip is mapping over the first list.
theorem List.mapZipWithLeft (h: c → d) (k: a → d) (g: a → b → c) (same: (x: a) → (y: b) → h (g x y) = k x):
    (xs: List a) → (ys: List b) → List.length xs ≤ List.length ys → List.map (List.zipWith xs ys g) h = List.map xs k
  | [], ys, le => rfl
  | [x, ..xs], [], le => Void.exfalso (Bool.falseNotTrue le)
  | [x, ..xs], [y, ..ys], le => rewrite same x y, List.mapZipWithLeft h k g same xs ys le in rfl

theorem List.mapZipWithScanLeft (h: c → d) (k: a → d) (g: a → b → c) (same: (x: a) → (y: b) → h (g x y) = k x)
    (xs: List a) (z: b) (f: b → a → b): List.map (List.zipWith xs (List.scanLeft xs z f) g) h = List.map xs k :=
  List.mapZipWithLeft h k g same xs (List.scanLeft xs z f) (rewrite List.lengthScanLeft xs z f in Nat.leSucc (List.length xs))

--| `mapAccumLeft` is a fold for its final state, and for its list the zip of
--| the elements with the running states.
theorem List.mapAccumLeftGoSpec (f: s → a → Pair s b): (xs: List a) → (state: s) → (done: List b) →
    List.mapAccumLeftGo f state done xs
      = MkPair (List.foldLeft xs state (st x => Pair.fst (f st x)))
        (List.reverseOnto done (List.zipWith xs (List.scanLeft xs state (st x => Pair.fst (f st x))) (x st => Pair.snd (f st x))))
  | [], state, done => rfl
  | [x, ..xs], state, done => List.mapAccumLeftGoSpec f xs (Pair.fst (f state x)) [Pair.snd (f state x), ..done]

theorem List.mapAccumLeftState (xs: List a) (initial: s) (f: s → a → Pair s b):
    Pair.fst (List.mapAccumLeft xs initial f) = List.foldLeft xs initial (st x => Pair.fst (f st x)) :=
  Eq.cong Pair.fst (List.mapAccumLeftGoSpec f xs initial [])

theorem List.mapAccumLeftList (xs: List a) (initial: s) (f: s → a → Pair s b):
    Pair.snd (List.mapAccumLeft xs initial f) = List.zipWith xs (List.scanLeft xs initial (st x => Pair.fst (f st x))) (x st => Pair.snd (f st x)) :=
  Eq.cong Pair.snd (List.mapAccumLeftGoSpec f xs initial [])

theorem List.lengthMapAccumLeft (xs: List a) (initial: s) (f: s → a → Pair s b):
    List.length (Pair.snd (List.mapAccumLeft xs initial f)) = List.length xs :=
  rewrite List.mapAccumLeftList xs initial f in List.lengthZipWithScanLeft (st x => Pair.fst (f st x)) (x st => Pair.snd (f st x)) xs initial

theorem List.mapAccumLeftExample: List.mapAccumLeft [1, 2, 3] 0 (sum x => MkPair (sum + x) sum) = MkPair 6 [0, 1, 3] := rfl

-- `List.get`, the element at an index if there is one: it is `Some` exactly
-- within the list, what it finds is an element, and it goes through `map`,
-- `zipWith`, `append` and `take`. (`List.getOrGet`, std/List/Index.sw, is
-- `List.getOr` from it.)

--| `get` finds something exactly when the index is within the list.
theorem List.isSomeGet: (xs: List a) → (k: Nat) → Option.isSome (List.get xs k) = Nat.leq (Succ k) (List.length xs)
  | [], k => rfl
  | [x, ..xs], Zero => rfl
  | [x, ..xs], Succ k => List.isSomeGet xs k

theorem List.getInRange (xs: List a) (k: Nat): k < List.length xs ↔ Option.isSome (List.get xs k) = True := {
  forward = h => Eq.trans (List.isSomeGet xs k) h,
  backward = h => Eq.trans (Eq.sym (List.isSomeGet xs k)) h
}

--| Past the end, `get` finds nothing.
theorem List.getPast: (xs: List a) → (k: Nat) → List.length xs ≤ k → List.get xs k = None
  | [], k, h => rfl
  | [x, ..xs], Zero, h => Void.exfalso (Bool.falseNotTrue h)
  | [x, ..xs], Succ k, h => List.getPast xs k h

--| What `get` finds is an element of the list.
theorem List.memOfGet: (xs: List a) → (k: Nat) → (v: a) → List.get xs k = Some v → v ∈ xs
  | [], k, v, h => Void.exfalso (Option.noneNotSome v h)
  | [x, ..xs], Zero, v, h => Inl (Option.someInjective x v h)
  | [x, ..xs], Succ k, v, h => Inr (List.memOfGet xs k v h)

theorem List.getMap: (xs: List a) → (f: a → b) → (k: Nat) → List.get (List.map xs f) k = Option.map (List.get xs k) f
  | [], f, k => rfl
  | [x, ..xs], f, Zero => rfl
  | [x, ..xs], f, Succ k => List.getMap xs f k

--| `withIndexFrom` is as long as the list; element k is the
--| list's element k with k (counted from `start`).
theorem List.lengthWithIndexFrom: (start: Nat) → (xs: List a) → List.length (List.withIndexFrom start xs) = List.length xs
  | start, [] => rfl
  | start, [x, ..xs] => Eq.cong Succ (List.lengthWithIndexFrom (Succ start) xs)

theorem List.lengthWithIndex (xs: List a): List.length (List.withIndex xs) = List.length xs := List.lengthWithIndexFrom 0 xs

theorem List.getWithIndexFrom: (start: Nat) → (xs: List a) → (k: Nat) →
    List.get (List.withIndexFrom start xs) k = Option.map (List.get xs k) (x => MkPair (start + k) x)
  | start, [], k => rfl
  | start, [x, ..xs], Zero => rewrite Nat.addZero start in rfl
  | start, [x, ..xs], Succ k => rewrite Nat.addSucc start k in List.getWithIndexFrom (Succ start) xs k

theorem List.getWithIndex (xs: List a) (k: Nat): List.get (List.withIndex xs) k = Option.map (List.get xs k) (x => MkPair k x) :=
  List.getWithIndexFrom 0 xs k

--| `mapWithIndex` keeps the length, and element k is `f k` of the list's
--| element k.
theorem List.lengthMapWithIndex (xs: List a) (f: Nat → a → b): List.length (List.mapWithIndex xs f) = List.length xs :=
  Eq.trans (List.lengthMap (List.withIndex xs) (pair => f pair.fst pair.snd)) (List.lengthWithIndex xs)

theorem List.getMapWithIndex (xs: List a) (f: Nat → a → b) (k: Nat): List.get (List.mapWithIndex xs f) k = Option.map (List.get xs k) (f k) :=
  let mapped: List.get (List.mapWithIndex xs f) k = Option.map (Option.map (List.get xs k) (x => MkPair k x)) (pair => f pair.fst pair.snd) :=
    rewrite <- List.getWithIndex xs k in List.getMap (List.withIndex xs) (pair => f pair.fst pair.snd) k
  rewrite mapped in
    match List.get xs k with
      | None => rfl
      | Some x => rfl

--| `zipWith` has `f x y` where both lists have an element, `x` and `y`.
theorem List.getZipWith (f: a → b → c): (xs: List a) → (ys: List b) → (k: Nat) →
    List.get (List.zipWith xs ys f) k = Option.flatMap (List.get xs k) (x => Option.map (List.get ys k) (f x))
  | [], ys, k => rfl
  | [x, ..xs], [], Zero => rfl
  | [x, ..xs], [], Succ k =>
    match c: List.get xs k with
      | None => rfl
      | Some u => rfl
  | [x, ..xs], [y, ..ys], Zero => rfl
  | [x, ..xs], [y, ..ys], Succ k => List.getZipWith f xs ys k

--| `zip`, `zipWith3` and `zipWith4` have the combined elements where every
--| list has one.
theorem List.getZip: (xs: List a) → (ys: List b) → (k: Nat) → List.get (List.zip xs ys) k = Option.map2 MkPair (List.get xs k) (List.get ys k)
  | [], ys, k => rfl
  | [x, ..xs], [], k => Eq.sym (Option.map2None MkPair _)
  | [x, ..xs], [y, ..ys], Zero => rfl
  | [x, ..xs], [y, ..ys], Succ k => List.getZip xs ys k

theorem List.getZipWith3 (f: a → b → c → d): (xs: List a) → (ys: List b) → (zs: List c) → (k: Nat) →
    List.get (List.zipWith3 xs ys zs f) k = Option.map3 f (List.get xs k) (List.get ys k) (List.get zs k)
  | [], ys, zs, k => rfl
  | [x, ..xs], [], zs, k => Eq.sym (Option.map3None2 f _ _)
  | [x, ..xs], [y, ..ys], [], k => Eq.sym (Option.map3None3 f _ _)
  | [x, ..xs], [y, ..ys], [z, ..zs], Zero => rfl
  | [x, ..xs], [y, ..ys], [z, ..zs], Succ k => List.getZipWith3 f xs ys zs k

theorem List.getZipWith4 (f: a → b → c → d → e): (xs: List a) → (ys: List b) → (zs: List c) → (ws: List d) → (k: Nat) →
    List.get (List.zipWith4 xs ys zs ws f) k = Option.map4 f (List.get xs k) (List.get ys k) (List.get zs k) (List.get ws k)
  | [], ys, zs, ws, k => rfl
  | [x, ..xs], [], zs, ws, k => Eq.sym (Option.map4None2 f _ _ _)
  | [x, ..xs], [y, ..ys], [], ws, k => Eq.sym (Option.map4None3 f _ _ _)
  | [x, ..xs], [y, ..ys], [z, ..zs], [], k => Eq.sym (Option.map4None4 f _ _ _)
  | [x, ..xs], [y, ..ys], [z, ..zs], [w, ..ws], Zero => rfl
  | [x, ..xs], [y, ..ys], [z, ..zs], [w, ..ws], Succ k => List.getZipWith4 f xs ys zs ws k

theorem List.getZipWith3Example: List.get (List.zipWith3 [1, 2] [10, 20, 30] [100, 200] (x y z => x + y + z)) 1 = Some 222 := rfl

--| `append`: the first list's element, else the second's, counting on from
--| the end of the first.
theorem List.getAppend: (xs: List a) → (ys: List a) → (k: Nat) →
    List.get (List.append xs ys) k = Option.orElse (List.get xs k) (List.get ys (k - List.length xs))
  | [], ys, k => rfl
  | [x, ..xs], ys, Zero => rfl
  | [x, ..xs], ys, Succ k => List.getAppend xs ys k

theorem List.getAppendLeft: (xs: List a) → (ys: List a) → (k: Nat) → k < List.length xs → List.get (List.append xs ys) k = List.get xs k
  | [], ys, k, h => Void.exfalso (Bool.falseNotTrue h)
  | [x, ..xs], ys, Zero, h => rfl
  | [x, ..xs], ys, Succ k, h => List.getAppendLeft xs ys k h

theorem List.getAppendRight: (xs: List a) → (ys: List a) → (k: Nat) → List.length xs ≤ k →
    List.get (List.append xs ys) k = List.get ys (k - List.length xs)
  | [], ys, k, h => rfl
  | [x, ..xs], ys, Zero, h => Void.exfalso (Bool.falseNotTrue h)
  | [x, ..xs], ys, Succ k, h => List.getAppendRight xs ys k h

--| `take n` keeps the elements before `n`, and nothing from `n` on.
theorem List.getTake: (xs: List a) → (n: Nat) → (k: Nat) → k < n → List.get (List.take xs n) k = List.get xs k
  | xs, Zero, k, h => Void.exfalso (Bool.falseNotTrue h)
  | [], Succ n, k, h => rfl
  | [x, ..xs], Succ n, Zero, h => rfl
  | [x, ..xs], Succ n, Succ k, h => List.getTake xs n k h

theorem List.getTakePast: (xs: List a) → (n: Nat) → (k: Nat) → n ≤ k → List.get (List.take xs n) k = None
  | xs, Zero, k, h => rfl
  | [], Succ n, k, h => rfl
  | [x, ..xs], Succ n, Zero, h => Void.exfalso (Bool.falseNotTrue h)
  | [x, ..xs], Succ n, Succ k, h => List.getTakePast xs n k h

--| Index j after dropping k is index k + j before.
theorem List.getDrop: (xs: List a) → (k: Nat) → (j: Nat) → List.get (List.drop xs k) j = List.get xs (k + j)
  | xs, Zero, j => rfl
  | [], Succ k, j => rfl
  | [x, ..xs], Succ k, j => List.getDrop xs k j

--| What `List.transposeN`'s columns are: column i holds element i of every
--| row that has one. From column `p` on, for the rows with their first `p`
--| elements dropped (`transposeN`'s own loop):
theorem List.transposeNColumnsFrom (rows: List (List a)): (k: Nat) → (p: Nat) →
    List.transposeN k (List.map rows (row => List.drop row p))
      = List.map (List.rangeFrom k p) (i => List.filterMap rows (row => List.get row i))
  | Zero, p => rfl
  | Succ k, p =>
    rewrite List.filterMapMap rows (x => List.get x 0) (row => List.drop row p),
      List.mapMap rows (x => List.drop x 1) (row => List.drop row p), List.getDrop _ p 0, Nat.addZero p, <- List.dropAdd p 1 in
      Eq.cong (later => [List.filterMap rows (row => List.get row p), ..later]) (List.transposeNColumnsFrom rows k (p + 1))

--| `transposeN k` gives column i, for each i below k, as element i of every row that has one.
theorem List.transposeNColumns (rows: List (List a)) (k: Nat):
    List.transposeN k rows = List.map (List.range 0 k) (i => List.filterMap rows (row => List.get row i)) :=
  Eq.trans (Eq.cong (rows => List.transposeN k rows) (Eq.sym (List.mapId rows))) (List.transposeNColumnsFrom rows k 0)

--| Column i of `List.transpose` holds element i of every row that has one,
--| for each i below the first row's length.
theorem List.transposeColumns (rows: List (List a)):
    List.transpose rows = List.map (List.range 0 (List.length (List.headOr rows []))) (i => List.filterMap rows (row => List.get row i)) :=
  List.transposeNColumns rows (List.length (List.headOr rows []))

--| Entry k of the running accumulations is the fold of the first k
--| elements ([`List.getOrScanLeft`], std/List/Index.sw, with a fallback).
theorem List.getScanLeft (f: b → a → b): (xs: List a) → (z: b) → (k: Nat) → k ≤ List.length xs →
    List.get (List.scanLeft xs z f) k = Some (List.foldLeft (List.take xs k) z f)
  | [], z, Zero, h => rfl
  | [], z, Succ k, h => Void.exfalso (Bool.falseNotTrue h)
  | [x, ..xs], z, Zero, h => rfl
  | [x, ..xs], z, Succ k, h => List.getScanLeft f xs (f z x) k h

--| Element k of each element beside the running accumulations is `g` of
--| element k and the fold of the elements before it, and nothing past the end.
theorem List.getZipWithScanLeft (f: b → a → b) (g: a → b → c): (xs: List a) → (z: b) → (k: Nat) →
    List.get (List.zipWith xs (List.scanLeft xs z f) g) k = Option.map (List.get xs k) (x => g x (List.foldLeft (List.take xs k) z f))
  | [], z, k => rfl
  | [x, ..xs], z, Zero => rfl
  | [x, ..xs], z, Succ k => List.getZipWithScanLeft f g xs (f z x) k

theorem List.getExample: List.get (List.append [1, 2] (List.map [3, 4] Succ)) 3 = Some 5 := rfl

--| For any list of successors, what `get` finds is not zero.
theorem List.getMapExample (xs: List Nat) (k: Nat) (v: Nat) (h: List.get (List.map xs Succ) k = Some v): v ≠ 0 :=
  Option.mapEqSome (List.get xs k) Succ v (Eq.trans (Eq.sym (List.getMap xs Succ k)) h) (u found e => rewrite <- e in Nat.succNotZero u)

--| `List.All2 r xs ys`: the lists are as long, and `r` holds of each pair of
--| elements at the same place (Coq's `Forall2`, Lean's `List.Forall₂`). What
--| [`Parse.eachLineReads`] says of the lines and the values read from them.
@[noReceiver]
def List.All2 (r: a → b → Prop): (xs: List a) → (ys: List b) → Prop
  | [], [] => Unit
  | [x, ..xs], [y, ..ys] => r x y ∧ List.All2 r xs ys
  | [], [y, ..ys] => Void
  | [x, ..xs], [] => Void

theorem List.all2Weaken (r: a → b → Prop) (s: a → b → Prop) (implies: (x: a) → (y: b) → r x y → s x y):
    (xs: List a) → (ys: List b) → List.All2 r xs ys → List.All2 s xs ys
  | [], [], all => Trivial
  | [x, ..xs], [y, ..ys], all => Both (implies x y (And.left all)) (List.all2Weaken r s implies xs ys (And.right all))
  | [], [y, ..ys], all => Void.exfalso all
  | [x, ..xs], [], all => Void.exfalso all

--| Where each element is `f` of its partner, the list is the partners mapped.
theorem List.all2Map (f: b → a): (xs: List a) → (ys: List b) → List.All2 (x y => x = f y) xs ys → xs = ys.map f
  | [], [], all => rfl
  | [x, ..xs], [y, ..ys], all => rewrite And.left all, List.all2Map f xs ys (And.right all) in rfl
  | [], [y, ..ys], all => Void.exfalso all
  | [x, ..xs], [], all => Void.exfalso all

theorem List.all2MapLeft (f: a → c) (r: c → b → Prop): (xs: List a) → (ys: List b) → List.All2 (x y => r (f x) y) xs ys → List.All2 r (xs.map f) ys
  | [], [], all => Trivial
  | [x, ..xs], [y, ..ys], all => Both (And.left all) (List.all2MapLeft f r xs ys (And.right all))
  | [], [y, ..ys], all => Void.exfalso all
  | [x, ..xs], [], all => Void.exfalso all

theorem List.all2Length (r: a → b → Prop): (xs: List a) → (ys: List b) → List.All2 r xs ys → xs.length = ys.length
  | [], [], all => rfl
  | [x, ..xs], [y, ..ys], all => Eq.cong Succ (List.all2Length r xs ys (And.right all))
  | [], [y, ..ys], all => Void.exfalso all
  | [x, ..xs], [], all => Void.exfalso all

--| Numbering the left list changes nothing a relation of the elements sees.
theorem List.all2WithIndex (r: a → b → Prop): (start: Nat) → (xs: List a) → (ys: List b) →
    List.All2 (entry y => r entry.snd y) (List.withIndexFrom start xs) ys → List.All2 r xs ys
  | start, [], [], all => Trivial
  | start, [x, ..xs], [y, ..ys], all => Both (And.left all) (List.all2WithIndex r (Succ start) xs ys (And.right all))
  | start, [], [y, ..ys], all => Void.exfalso all
  | start, [x, ..xs], [], all => Void.exfalso all
