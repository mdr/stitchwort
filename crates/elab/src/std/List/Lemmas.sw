--| Lemmas about the list toolkit's functions (List/Toolkit.sw): lengths, sums
--| and counts, membership, permutations, congruence, `get`, and the like, with
--| the examples and tests that use them.

theorem List.lengthAppend ∀ (xs ys: List a): List.length (List.append xs ys) = List.length xs + List.length ys :=
  match xs with
    | [] => byComputing
    | [x, ..xs] => Eq.cong Succ (List.lengthAppend xs ys)

--| The loop the runtimes run for `List.length` counts the same.
theorem List.lengthOntoEq ∀ (xs: List a) (n: Nat): List.lengthOnto xs n = n + List.length xs := match xs with
  | [] => (Nat.addZero n).flipped
  | [x, ..xs] => Eq.trans (List.lengthOntoEq xs (Succ n)) (Eq.flipped (Nat.addSucc n (List.length xs)))

--| Splitting a list at `n` and joining the parts gives it back.
theorem List.appendTakeDrop ∀ (xs: List a) (n: Nat): List.append (List.take xs n) (List.drop xs n) = xs :=
  match xs, n with
    | xs, Zero => byComputing
    | [], Succ n => byComputing
    | [x, ..xs], Succ n => Eq.cong (Cons x) (List.appendTakeDrop xs n)

theorem List.scanLeftNil: List.scanLeft [] 5 (acc x => acc + x) = [5] := byComputing

theorem List.scanLeftSums: List.scanLeft [1, 2, 3] 0 (acc x => acc + x) = [0, 1, 3, 6] := byComputing

theorem List.foldLeftReverseOnto ∀ (xs acc: List a) (z: b) (f: a → b → b):
    List.foldLeft (List.reverseOnto xs acc) z (r x => f x r)
      = List.foldLeft acc (List.foldLeft (List.reverseOnto xs []) z (r x => f x r)) (r x => f x r) :=
  match xs with
    | [] => byComputing
    | [x, ..xs] =>
      Eq.trans
        (List.foldLeftReverseOnto xs [x, ..acc] z f)
        (Eq.flipped (Eq.cong (r => List.foldLeft acc r (r2 y => f y r2)) (List.foldLeftReverseOnto xs [x] z f)))

--| The step of the right fold, which the loop form hides.
theorem List.foldRightCons ∀ (xs: List a) (x: a) (z: b) (f: a → b → b):
    List.foldRight [x, ..xs] z f = f x (List.foldRight xs z f) :=
  List.foldLeftReverseOnto xs [x] z f

theorem List.sumByDoubles: List.sumBy [1, 2, 3] (x => x * 2) = 12 := byComputing

theorem List.sumInts: List.sum [(3: Int), -5, 1] = -1 := byComputing

theorem List.sumByInts: List.sumBy [(1: Int), 2, 3] (x => Int.sub 1 x) = -3 := byComputing

--| A sum is a `sumBy` of each element itself.
theorem List.sumIsSumBy ∀ [auto add: Add a] (xs: List a): List.sum xs = List.sumBy xs (x => x) := byComputing

theorem List.zipWithNextExample: List.zipWithNext [1, 2, 3] = [MkPair 1 2, MkPair 2 3] := byComputing

--| One pair fewer than there are elements.
theorem List.lengthZipWithNext ∀ (xs: List a): List.length (List.zipWithNext xs) = List.length xs - 1 := match xs with
  | [] => byComputing
  | [x] => byComputing
  | [x, next, ..rest] => rewrite List.lengthZipWithNext [next, ..rest]

--| The list zipped with its own tail.
theorem List.zipWithNextZip ∀ (xs: List a): List.zipWithNext xs = List.zip xs (List.tailOf xs) := match xs with
  | [] => byComputing
  | [x] => byComputing
  | [x, next, ..rest] => rewrite List.zipWithNextZip [next, ..rest]

theorem List.chainEmpty ∀ (holds: a → a → Bool): List.chain [] holds = True := byComputing

theorem List.chainSingle ∀ (x: a) (holds: a → a → Bool): List.chain [x] holds = True := byComputing

theorem List.chainCons ∀ (x next: a) (rest: List a) (holds: a → a → Bool):
    List.chain [x, next, ..rest] holds = (holds x next ∧ List.chain [next, ..rest] holds) :=
  byComputing

--| `holds` is true of every pair `zipWithNext` gives.
theorem List.chainZipWithNext ∀ (xs: List a) (holds: a → a → Bool):
    List.chain xs holds = (List.zipWithNext xs |> .all (pair => holds pair.fst pair.snd)) :=
  match xs with
    | [] => byComputing
    | [x] => byComputing
    | [x, next, ..rest] => rewrite List.chainZipWithNext [next, ..rest] holds

--| Without the first element, it still holds.
theorem List.chainTail ∀ (xs: List a) (holds: a → a → Bool)
    (chained: List.chain xs holds = True):
    List.chain (List.tailOf xs) holds = True :=
  match xs with
    | [] => byComputing
    | [x] => byComputing
    | [x, next, ..rest] =>
      let Both _ more := chained
      more

--| Without the last element (`List.init`), it still holds.
theorem List.chainInit ∀ (xs: List a) (holds: a → a → Bool)
    (chained: List.chain xs holds = True):
    List.chain (List.init xs) holds = True :=
  match xs with
    | [] => byComputing
    | [x, ..rest] => List.chainInitCons x rest holds chained

theorem List.chainInitCons ∀ (x: a) (rest: List a) (holds: a → a → Bool)
    (chained: List.chain [x, ..rest] holds = True):
    List.chain (List.init [x, ..rest]) holds = True :=
  match rest with
    | [] => byComputing
    | [next] => byComputing
    | [next, after, ..more] =>
      let Both first rest := chained
      Both first (List.chainInitCons next [after, ..more] holds rest)

--| A `chain` of two tests together holds when the chain of each one does.
theorem List.chainAnd ∀ (xs: List a) (holds1 holds2: a → a → Bool):
    List.chain xs (x y => holds1 x y ∧ holds2 x y) = (List.chain xs holds1 ∧ List.chain xs holds2) :=
  match xs with
    | [] => byComputing
    | [x] => byComputing
    | [x, next, ..rest] => rewrite List.chainAnd [next, ..rest] holds1 holds2 then cases

--| `all` over a cons: the head's answer, then the rest's.
theorem List.allCons ∀ (p: a → Bool) (x: a) (xs: List a): List.all [x, ..xs] p = (p x ∧ List.all xs p) := byComputing

--| `any` over a cons: the head's answer, then the rest's.
theorem List.anyCons ∀ (p: a → Bool) (x: a) (xs: List a): List.any [x, ..xs] p = (p x ∨ List.any xs p) := byComputing

--| A run of `a + b` numbers is a run of `a` followed by a run of `b`.
theorem List.rangeFromAppend ∀ (a b s: Nat):
    List.rangeFrom (a + b) s = List.append (List.rangeFrom a s) (List.rangeFrom b (s + a)) :=
  match a with
    | Zero => Eq.cong (t => List.rangeFrom b t) (Nat.addZero s).flipped
    | Succ a =>
      Eq.cong
        (Cons s)
        (Eq.trans
          (List.rangeFromAppend a b (Succ s))
          (Eq.cong (t => List.append (List.rangeFrom a (Succ s)) (List.rangeFrom b t)) (Nat.addSucc s a).flipped))

--| `List.range a b` has `b - a` elements: none when `b ≤ a`.
theorem List.lengthRange ∀ (a b: Nat): List.length (List.range a b) = b - a := List.lengthRangeFrom (b - a) a

test "List.lengthRange" :=
  List.length (List.range 3 4) == 1 ∧ List.length (List.range 5 3) == 0 ∧ List.length (List.range 2 7) == 5

--| A range whose end is not past its start is empty.
theorem List.rangeEmpty ∀ (a b: Nat) (h: b ≤ a): List.range a b = [] :=
  Eq.cong (t => List.rangeFrom t a) (arithmetic: b - a = 0)

--| A non-empty range is its first number and the range from the next one.
theorem List.rangeCons ∀ (a b: Nat) (h: a < b): List.range a b = [a, ..List.range (a + 1) b] :=
  Eq.cong (t => List.rangeFrom t a) (arithmetic: b - a = Succ (b - (a + 1)))

--| Ranges that meet end to end join into one.
theorem List.rangeAppend ∀ (a b c: Nat) (ab: a ≤ b) (bc: b ≤ c): List.range a b ++ List.range b c = List.range a c :=
  calc List.rangeFrom (b - a) a ++ List.rangeFrom (c - b) b
    _ = List.rangeFrom (b - a) a ++ List.rangeFrom (c - b) (a + (b - a)) :=
      Eq.cong
        (t => List.append (List.rangeFrom (b - a) a) (List.rangeFrom (c - b) t))
        (Eq.flipped (arithmetic: a + (b - a) = b))
    _ = List.rangeFrom (b - a + (c - b)) a := Eq.flipped (List.rangeFromAppend (b - a) (c - b) a)
    _ = List.rangeFrom (c - a) a := Eq.cong (t => List.rangeFrom t a) (arithmetic: (b - a) + (c - b) = c - a)

--| A range that includes its end is the range before the end, then the end.
theorem List.rangeSnoc ∀ (a b: Nat) (h: a ≤ b): List.range a (b + 1) = [..List.range a b, b] :=
  Eq.trans
    (Eq.flipped (List.rangeAppend a b (b + 1) h (arithmetic)))
    (Eq.cong (t => List.append (List.range a b) t) (Eq.cong (t => List.rangeFrom t b) (arithmetic: b + 1 - b = 1)))

theorem List.headExample: List.head [3, 4] = Some 3 := byComputing

theorem List.headEmpty: List.head ([]: List Nat) = None := byComputing

theorem List.initExample: List.init [1, 2, 3] = [1, 2] := byComputing

theorem List.initEmpty: List.init ([]: List Nat) = [] := byComputing

--| The loop's sides are the two `filter`s, each after what it had sorted.
theorem List.partitionOntoFilters ∀ (p: a → Bool) (xs kept dropped: List a):
    List.partitionOnto p xs (MkPair kept dropped)
      = MkPair (List.reverseOnto kept (List.filter xs p)) (List.reverseOnto dropped (List.filter xs (x => ¬(p x)))) :=
  match xs with
    | [] => byComputing
    | [x, ..xs] =>
      match p x with
        | True => List.partitionOntoFilters p xs [x, ..kept] dropped
        | False => List.partitionOntoFilters p xs kept [x, ..dropped]

--| `partition` is the two `filter`s.
-- (its definition before it became one pass)
theorem List.partitionFilters ∀ (xs: List a) (p: a → Bool):
    List.partition xs p = MkPair (List.filter xs p) (List.filter xs (x => ¬(p x))) :=
  List.partitionOntoFilters p xs [] []

theorem List.partitionExample: List.partition [1, 5, 2, 7] (x => x > 4) = MkPair [5, 7] [1, 2] := byComputing

theorem List.lengthReplicate ∀ (x: a) (n: Nat): List.length (List.replicate n x) = n := match n with
  | Zero => byComputing
  | Succ n => Eq.cong Succ (List.lengthReplicate x n)

--| `m + n` copies of `x` are `m` copies and then `n` copies:
--| `replicate (m + n) x = replicate m x ++ replicate n x`.
theorem List.replicateAdd ∀ (x: a) (m n: Nat): List.replicate (m + n) x = List.replicate m x ++ List.replicate n x :=
  match m with
    | Zero => rewrite (arithmetic: 0 + n = n)
    | Succ m => rewrite List.replicateAdd x m n

--| Padding makes a list exactly n long, when it was no longer than that.
theorem List.padRightLength ∀ (xs: List a) (n: Nat) (x: a)
    (h: List.length xs ≤ n):
    List.length (List.padRight xs n x) = n :=
  calc (xs ++ List.replicate (n - xs.length) x).length
    _ = xs.length + (List.replicate (n - xs.length) x).length :=
      List.lengthAppend xs (List.replicate (n - List.length xs) x)
    _ = xs.length + (n - xs.length) := Eq.cong (t => List.length xs + t) (List.lengthReplicate x (n - List.length xs))
    _ = n := Nat.addSubCancel (List.length xs) n h

theorem List.padRightExample: List.padRight [1, 2] 4 0 = [1, 2, 0, 0] := byComputing

theorem List.padRightLongEnough: List.padRight [1, 2] 1 0 = [1, 2] := byComputing

-- Lemmas about `List.transpose`: it has as many columns as the first row is
-- long, and for a rectangular list, doing it twice gives back the list.

--| `map` keeps the length.
theorem List.lengthMap ∀ (xs: List a) (f: a → b): List.length (List.map xs f) = List.length xs := match xs with
  | [] => byComputing
  | [x, ..xs] => Eq.cong Succ (List.lengthMap xs f)

theorem List.transposeExample: List.transpose [[1, 2, 3], [4, 5, 6]] = [[1, 4], [2, 5], [3, 6]] := byComputing

theorem List.transposeNone: List.transpose ([]: List (List Nat)) = [] := byComputing

theorem List.transposeShortRow: List.transpose [[1, 2], [3], [4, 5]] = [[1, 3, 4], [2, 5]] := byComputing

theorem List.transposeNLength ∀ (n: Nat) (rows: List (List a)): List.length (List.transposeN n rows) = n := match n with
  | Zero => byComputing
  | Succ n => Eq.cong Succ (List.transposeNLength n (List.map rows (.drop 1)))

theorem List.allAppend ∀ (p: a → Prop) (xs ys: List a)
    (h: List.All p xs)
    (hy: List.All p ys):
    List.All p (List.append xs ys) :=
  match xs, h with
    | [], hx => hy
    | [x, ..xs], Both hx hxs => Both hx (List.allAppend p xs ys hxs hy)

theorem List.allAppendLeft ∀ (p: a → Prop) (xs ys: List a) (h1: List.All p (List.append xs ys)): List.All p xs :=
  match xs, h1 with
    | [], h => Trivial
    | [x, ..xs], Both h hxs => Both h (List.allAppendLeft p xs ys hxs)

theorem List.allAppendRight ∀ (p: a → Prop) (xs ys: List a) (h1: List.All p (List.append xs ys)): List.All p ys :=
  match xs, h1 with
    | [], h => h
    | [x, ..xs], Both h hxs => List.allAppendRight p xs ys hxs

theorem List.allMap ∀ (xs: List a) (p: b → Prop) (f: a → b)
    (h1: List.All (x => p (f x)) xs):
    List.All p (List.map xs f) :=
  match xs, h1 with
    | [], h => Trivial
    | [x, ..xs], Both h hxs => Both h (List.allMap xs p f hxs)

theorem List.allImplies ∀ (p q: a → Prop) (h: ∀ (x: a) => p x → q x) (xs: List a) (hp: List.All p xs): List.All q xs :=
  match xs, hp with
    | [], hp => Trivial
    | [x, ..xs], Both hpx hpxs => Both (h x hpx) (List.allImplies p q h xs hpxs)

theorem List.anyAppendLeft ∀ (p: a → Prop) (xs ys: List a) (h1: List.Any p xs): List.Any p (List.append xs ys) :=
  match xs, h1 with
    | [], h => h.impossible
    | [x, ..xs], Inl h => Inl h
    | [x, ..xs], Inr h => Inr (List.anyAppendLeft p xs ys h)

theorem List.anyAppendRight ∀ (p: a → Prop) (xs ys: List a) (h: List.Any p ys): List.Any p (List.append xs ys) :=
  match xs with
    | [] => h
    | [x, ..xs] => Inr (List.anyAppendRight p xs ys h)

--| `List.any` of two lists joined: either list has one.
theorem List.anyAppend ∀ (xs ys: List a) (p: a → Bool):
    List.any (List.append xs ys) p = (List.any xs p ∨ List.any ys p) :=
  match xs with
    | [] => byComputing
    | [x, ..xs] =>
      match e: p x with
        | True => byComputing
        | False => List.anyAppend xs ys p

theorem List.anyAppendExample: List.any (List.append [1, 2] [3]) (x => x == 3) = (False ∨ True) := byComputing

theorem List.lengthZero ∀ (xs: List a) (h: List.length xs = 0): xs = [] := match xs with
  | [] => byComputing
  | [y, ..ys] => Void.impossible (Nat.succNotZero (List.length ys) h)

theorem List.transposeNNil ∀ (n: Nat): List.transposeN n ([]: List (List a)) = List.replicate n [] := match n with
  | Zero => byComputing
  | Succ n => Eq.cong (Cons []) (List.transposeNNil n)

theorem List.allLengthZero ∀ (rows: List (List a)) (n: Nat)
    (hl: List.length rows = n)
    (h: List.AllLength 0 rows):
    rows = List.replicate n [] :=
  match rows, n, h with
    | [], n, hr => J (y q => ([]: List (List a)) = List.replicate y ([]: List a)) byComputing hl
    | [r, ..rs], Succ m, Both hr hrs =>
      Eq.trans
        (Eq.cong (t => [t, ..rs]) (List.lengthZero r hr))
        (Eq.cong (Cons []) (List.allLengthZero rs m (Nat.succInjective hl) hrs))

theorem List.tailsAllLength ∀ (rows: List (List a)) (k: Nat)
    (h: List.AllLength (Succ k) rows):
    List.AllLength k (List.map rows (.drop 1)) :=
  match rows, h with
    | [], hr => Trivial
    | [[], ..rs], Both hr hrs => (Nat.zeroNotSucc k hr).impossible
    | [[y, ..ys], ..rs], Both hr hrs => Both (Nat.succInjective hr) (List.tailsAllLength rs k hrs)

theorem List.headsLength ∀ (rows: List (List a)) (k: Nat)
    (h: List.AllLength (Succ k) rows):
    List.length (List.filterMap rows (.get 0)) = List.length rows :=
  match rows, h with
    | [], hr => byComputing
    | [[], ..rs], Both hr hrs => (Nat.zeroNotSucc k hr).impossible
    | [[y, ..ys], ..rs], Both hr hrs => Eq.cong Succ (List.headsLength rs k hrs)

theorem List.rowsAreHeadsAndTails ∀ (rows: List (List a)) (k: Nat)
    (h: List.AllLength (Succ k) rows):
    rows = List.zipWith (List.filterMap rows (.get 0)) (List.map rows (.drop 1)) Cons :=
  match rows, h with
    | [], hr => byComputing
    | [[], ..rs], Both hr hrs => (Nat.zeroNotSucc k hr).impossible
    | [[y, ..ys], ..rs], Both hr hrs => Eq.cong (Cons [y, ..ys]) (List.rowsAreHeadsAndTails rs k hrs)

theorem List.columnsAllLength ∀ (w: Nat) (rows: List (List a)) (h: Nat)
    (hl: List.length rows = h)
    (hr: List.AllLength w rows):
    List.AllLength h (List.transposeN w rows) :=
  match w with
    | Zero => Trivial
    | Succ k =>
      Both
        (Eq.trans (List.headsLength rows k hr) hl)
        (List.columnsAllLength k
          (List.map rows (.drop 1))
          h
          (Eq.trans (List.lengthMap rows (.drop 1)) hl)
          (List.tailsAllLength rows k hr))

theorem List.transposeNCons ∀ (heads: List a) (h: Nat) (cols: List (List a))
    (hl: List.length heads = h)
    (hc: List.AllLength h cols):
    List.transposeN h [heads, ..cols] = List.zipWith heads (List.transposeN h cols) Cons :=
  match heads, h with
    | [], Zero => byComputing
    | [], Succ m => (Nat.zeroNotSucc m hl).impossible
    | [x, ..xs], Succ m =>
      Eq.cong
        (Cons [x, ..List.filterMap cols (.get 0)])
        (List.transposeNCons xs m (List.map cols (.drop 1)) (Nat.succInjective hl) (List.tailsAllLength cols m hc))

theorem List.transposeNTwice ∀ (w h: Nat) (rows: List (List a))
    (hl: List.length rows = h)
    (hr: List.AllLength w rows):
    List.transposeN h (List.transposeN w rows) = rows :=
  match w with
    | Zero => Eq.trans (List.transposeNNil h) (List.allLengthZero rows h hl hr).flipped
    | Succ k =>
      calc List.transposeN h [rows.filterMap (x => x.get 0), ..List.transposeN k (rows.map (x => x.drop 1))]
        _ = (rows.filterMap (x => x.get 0)).zipWith
            (List.transposeN h (List.transposeN k (rows.map (x => x.drop 1))))
            (head tail => [head, ..tail]) :=
          List.transposeNCons
            (List.filterMap rows (.get 0))
            h
            (List.transposeN k (List.map rows (.drop 1)))
            (Eq.trans (List.headsLength rows k hr) hl)
            (List.columnsAllLength k
              (List.map rows (.drop 1))
              h
              (Eq.trans (List.lengthMap rows (.drop 1)) hl)
              (List.tailsAllLength rows k hr))
        _ = (rows.filterMap (x => x.get 0)).zipWith (rows.map (x => x.drop 1)) (head tail => [head, ..tail]) :=
          Eq.cong
            (tails => List.zipWith (List.filterMap rows (.get 0)) tails Cons)
            (List.transposeNTwice k h
              (List.map rows (.drop 1))
              (Eq.trans (List.lengthMap rows (.drop 1)) hl)
              (List.tailsAllLength rows k hr))
        _ = rows := Eq.flipped (List.rowsAreHeadsAndTails rows k hr)

--| There are as many columns as the first row is long.
theorem List.transposeLength ∀ (rows: List (List a)):
    List.length (List.transpose rows) = List.length (List.headOr rows []) :=
  List.transposeNLength (List.length (List.headOr rows [])) rows

--| Transposing a rectangular list (every row the same non-zero length) twice
--| gives the list back. (With rows of length 0, the first transpose is empty
--| and the rows are lost.)
theorem List.transposeTwice ∀ (k: Nat) (rows: List (List a))
    (h: List.AllLength (Succ k) rows):
    List.transpose (List.transpose rows) = rows :=
  match rows, h with
    | [], hr => byComputing
    | [r, ..rs], Both hr hrs =>
      J
        (y q =>
          List.transposeN (List.length (List.headOr (List.transposeN y [r, ..rs]) [])) (List.transposeN y [r, ..rs])
            = [r, ..rs])
        (List.transposeNTwice
          (Succ k)
          (List.length (List.headOr (List.transposeN (Succ k) [r, ..rs]) []))
          [r, ..rs]
          (Eq.flipped (List.headsLength [r, ..rs] k (Both hr hrs)))
          (Both hr hrs))
        hr.flipped

-- Sums from a starting total, and one element at a time, for any `Add`:
-- the laws `zeroAdd`, `assoc` and `comm`.
-- (docs/proposals/interfaces.md §7.7)

--| Adding zero on the right changes nothing, for any `Add`.
theorem Add.addZero ∀ [auto add: Add a] (x: a): x + Add.zero = x := Eq.trans (add.comm x Add.zero) (add.zeroAdd x)

theorem Add.addSwap ∀ [auto add: Add a] (w x y z: a): (w + x) + (y + z) = (w + y) + (x + z) := calc (w + x) + (y + z)
  _ = w + (x + (y + z)) := add.assoc w x (y + z)
  _ = w + ((x + y) + z) := Eq.cong (t => w + t) (add.assoc x y z).flipped
  _ = w + ((y + x) + z) := Eq.cong (t => w + (t + z)) (add.comm x y)
  _ = w + (y + (x + z)) := Eq.cong (t => w + t) (add.assoc y x z)
  _ = (w + y) + (x + z) := Eq.flipped (add.assoc w y (x + z))

theorem Add.addLeftComm ∀ [auto add: Add a] (x y z: a): x + (y + z) = y + (x + z) := calc x + (y + z)
  _ = (x + y) + z := (add.assoc x y z).flipped
  _ = (y + x) + z := Eq.cong (t => t + z) (add.comm x y)
  _ = y + (x + z) := add.assoc y x z

theorem List.sumByFrom ∀ [auto add: Add b] (xs: List a) (z: b) (f: a → b):
    List.foldLeft xs z (acc x => acc + f x) = z + List.sumBy xs f :=
  match xs with
    | [] => (Add.addZero z).flipped
    | [x, ..xs] =>
      calc List.foldLeft xs (z + f x) (acc x => acc + f x)
        _ = (z + f x) + List.sumBy xs f := List.sumByFrom xs (z + f x) f
        _ = z + (f x + List.sumBy xs f) := add.assoc z (f x) (List.sumBy xs f)
        _ = z + List.foldLeft xs (f x) (acc x => acc + f x) :=
          Eq.cong (t => z + t) (Eq.flipped (List.sumByFrom xs (f x) f))
        _ = z + List.sumBy [x, ..xs] f :=
          Eq.cong (t => z + List.foldLeft xs t (acc x => acc + f x)) (Eq.flipped (add.zeroAdd (f x)))

theorem List.sumByCons ∀ [auto add: Add b] (xs: List a) (x: a) (f: a → b):
    List.sumBy [x, ..xs] f = f x + List.sumBy xs f :=
  Eq.trans (Eq.cong (t => List.foldLeft xs t (acc x => acc + f x)) (add.zeroAdd (f x))) (List.sumByFrom xs (f x) f)

--| The sum of `f` over `length` numbers counting up from `start`, without
--| building the list of them: `Nat.sumFrom 3 f 2` is `f 3 + f 4`. It is
--| `List.sumBy (List.rangeFrom length start) f` ([`Nat.sumFromRangeFrom`]).
def Nat.sumFrom (start: Nat) (f: Nat → Nat): (length: Nat) → Nat
  | Zero => 0
  | Succ more => f start + Nat.sumFrom (Succ start) f more

--| Summing over numbers counting up from `start` is summing over the list
--| of them, `List.rangeFrom length start`: the specification of [`Nat.sumFrom`].
theorem Nat.sumFromRangeFrom ∀ (f: Nat → Nat) (length start: Nat):
    Nat.sumFrom start f length = List.sumBy (List.rangeFrom length start) f :=
  match length with
    | Zero => byComputing
    | Succ more =>
      rewrite List.sumByCons (List.rangeFrom more (Succ start)) start f, Nat.sumFromRangeFrom f more (Succ start)

theorem List.sumByAppend ∀ [auto add: Add b] (xs ys: List a) (f: a → b):
    List.sumBy (List.append xs ys) f = List.sumBy xs f + List.sumBy ys f :=
  Eq.trans (List.foldLeftAppend xs Add.zero ys (acc x => acc + f x)) (List.sumByFrom ys (List.sumBy xs f) f)

theorem List.filterKeep ∀ (xs: List a) (p: a → Bool) (x: a)
    (h: p x = True):
    List.filter [x, ..xs] p = [x, ..List.filter xs p] :=
  J (c q => List.filterStep x (List.filter xs p) c = [x, ..List.filter xs p]) byComputing h.flipped

theorem List.filterSkip ∀ (xs: List a) (p: a → Bool) (x: a)
    (h: p x = False):
    List.filter [x, ..xs] p = List.filter xs p :=
  J (c q => List.filterStep x (List.filter xs p) c = List.filter xs p) byComputing h.flipped

--| Filtering a joined list filters each part:
--| `(xs ++ ys).filter p = xs.filter p ++ ys.filter p`.
theorem List.filterAppend ∀ (xs ys: List a) (p: a → Bool):
    List.filter (xs ++ ys) p = List.filter xs p ++ List.filter ys p :=
  match xs with
    | [] => byComputing
    | [x, ..rest] =>
      match t: p x with
        | True => rewrite List.filterAppend rest ys p
        | False => rewrite List.filterAppend rest ys p

theorem List.foldLeftAppend ∀ (xs: List a) (z: b) (ys: List a) (f: b → a → b):
    List.foldLeft (List.append xs ys) z f = List.foldLeft ys (List.foldLeft xs z f) f :=
  match xs with
    | [] => byComputing
    | [x, ..xs] => List.foldLeftAppend xs (f z x) ys f

-- Appending and taking; sums of `Nat.keepIf` terms, which pick out some
-- elements; swapping two sums; sums and `any` over a run `s .. s + c` that
-- pick nothing or exactly one element.

--| Appending the empty list changes nothing.
theorem List.appendNil ∀ (xs: List a): List.append xs [] = xs := match xs with
  | [] => byComputing
  | [x, ..xs] => Eq.cong (Cons x) (List.appendNil xs)

--| Appending to a list that isn't empty, or appending one that isn't, gives
--| a list that isn't empty.
theorem List.appendNotNilLeft ∀ (xs ys: List a) (some: xs ≠ []): List.append xs ys ≠ [] := match xs with
  | [] => empty => some byComputing
  | [x, ..rest] => empty => List.consNotNil x (List.append rest ys) empty

theorem List.appendNotNilRight ∀ (xs ys: List a) (some: ys ≠ []): List.append xs ys ≠ [] := match xs with
  | [] => empty => some empty
  | [x, ..rest] => empty => List.consNotNil x (List.append rest ys) empty

--| Appending is associative: `(xs ++ ys) ++ zs = xs ++ (ys ++ zs)`.
theorem List.appendAssoc ∀ (xs ys zs: List a):
    List.append (List.append xs ys) zs = List.append xs (List.append ys zs) :=
  match xs with
    | [] => byComputing
    | [x, ..xs] => Eq.cong (Cons x) (List.appendAssoc xs ys zs)

-- `List.count` is a fold with an accumulator; `List.occurrences` recurses on
-- the list, which suits proofs. They agree, so the lemmas below are stated
-- for `List.count` (the program's) and proved through `List.occurrences`.
-- Also here: counting and `List.scanLeft` over `++`, and permutations.

--| Rearranging sums, for the counting lemmas below.
theorem Nat.addRotate ∀ (a b c: Nat): (a + b) + c = b + (a + c) :=
  Eq.trans (Eq.cong (t => t + c) (Nat.addComm a b)) (Nat.addAssoc b a c)

theorem Nat.addLeftComm ∀ (a b c: Nat): a + (b + c) = b + (a + c) :=
  Eq.trans (Nat.addAssoc a b c).flipped (Nat.addRotate a b c)

theorem List.countStep ∀ (b: Bool) (k o: Nat): Nat.succIf k b + o = k + (Bool.toNat b + o) := match b with
  | True => (Nat.addSucc k o).flipped
  | False => byComputing

theorem List.countFold ∀ (xs: List a) (k: Nat) (p: a → Bool):
    List.foldLeft xs k (n x => Nat.succIf n (p x)) = k + List.occurrences xs p :=
  match xs with
    | [] => (Nat.addZero k).flipped
    | [x, ..xs] => Eq.trans (List.countFold xs (Nat.succIf k (p x)) p) (List.countStep (p x) k (List.occurrences xs p))

theorem List.countOccurrences ∀ (xs: List a) (p: a → Bool): List.count xs p = List.occurrences xs p :=
  List.countFold xs 0 p

theorem List.occurrencesSumBy ∀ (xs: List a) (p: a → Bool):
    List.occurrences xs p = List.sumBy xs (x => Bool.toNat (p x)) :=
  match xs with
    | [] => byComputing
    | [x, ..xs] => rewrite List.sumByCons xs x (x => Bool.toNat (p x)), List.occurrencesSumBy xs p

--| A count is a sum of 1s and 0s, so the sum lemmas apply to it.
theorem List.countSumBy ∀ (xs: List a) (p: a → Bool): List.count xs p = List.sumBy xs (x => Bool.toNat (p x)) :=
  Eq.trans (List.countOccurrences xs p) (List.occurrencesSumBy xs p)

theorem List.occurrencesAppend ∀ (xs ys: List a) (p: a → Bool):
    List.occurrences (List.append xs ys) p = List.occurrences xs p + List.occurrences ys p :=
  match xs with
    | [] => byComputing
    | [x, ..xs] =>
      Eq.trans
        (Eq.cong (t => Bool.toNat (p x) + t) (List.occurrencesAppend xs ys p))
        (Eq.flipped (Nat.addAssoc (Bool.toNat (p x)) (List.occurrences xs p) (List.occurrences ys p)))

theorem List.countNil ∀ (p: a → Bool): List.count [] p = 0 := byComputing

theorem List.countCons ∀ (xs: List a) (x: a) (p: a → Bool):
    List.count [x, ..xs] p = Bool.toNat (p x) + List.count xs p :=
  Eq.trans
    (List.countOccurrences [x, ..xs] p)
    (Eq.cong (n => Bool.toNat (p x) + n) (List.countOccurrences xs p).flipped)

theorem List.countAppend ∀ (xs ys: List a) (p: a → Bool):
    List.count (List.append xs ys) p = List.count xs p + List.count ys p :=
  calc (xs ++ ys).count p
    _ = (xs ++ ys).occurrences p := List.countOccurrences (List.append xs ys) p
    _ = xs.occurrences p + ys.occurrences p := List.occurrencesAppend xs ys p
    _ = xs.count p + ys.occurrences p := Eq.cong (n => n + List.occurrences ys p) (List.countOccurrences xs p).flipped
    _ = xs.count p + ys.count p := Eq.cong (n => List.count xs p + n) (List.countOccurrences ys p).flipped

--| The length of a `filter` is the `count` with the same test.
theorem List.lengthFilter ∀ (xs: List a) (p: a → Bool): List.length (List.filter xs p) = List.count xs p :=
  match xs with
    | [] => byComputing
    | [x, ..rest] =>
      rewrite List.countCons rest x p, <- List.lengthFilter rest p then
        match keep: p x with
          | True => byComputing
          | False => byComputing

--| A count is at most the length, and so is a `filter`'s length; filtering
--| out an element that is there makes the list shorter.
theorem List.countLeLength ∀ (xs: List a) (p: a → Bool): List.count xs p ≤ List.length xs := match xs with
  | [] => Nat.leRefl 0
  | [x, ..rest] => rewrite List.countCons rest x p then arithmetic [List.countLeLength rest p, Bool.toNatLeOne (p x)]

theorem List.lengthFilterLe ∀ (xs: List a) (p: a → Bool): List.length (List.filter xs p) ≤ List.length xs :=
  rewrite List.lengthFilter xs p then List.countLeLength xs p

theorem List.lengthFilterLt ∀ (p: a → Bool) (x: a)
    (dropped: p x = False) (xs: List a)
    (member: x ∈ xs):
    List.length (List.filter xs p) < List.length xs :=
  match xs, member with
    | [], member => member.impossible
    | [y, ..rest], Inl same => rewrite same, dropped then arithmetic [List.lengthFilterLe rest p]
    | [y, ..rest], Inr later =>
      match p y with
        | True => List.lengthFilterLt p x dropped rest later
        | False => arithmetic [List.lengthFilterLt p x dropped rest later]

--| An element that passes makes the count positive, and the other way
--| round, for an element counted by `== c`.
theorem List.countPositive ∀ (xs: List a) (p: a → Bool) (x: a)
    (member: x ∈ xs)
    (passes: p x = True):
    0 < List.count xs p :=
  match xs, member with
    | [], member => member.impossible
    | [y, ..rest], Inl same => rewrite List.countCons rest y p, same, passes then arithmetic
    | [y, ..rest], Inr later =>
      rewrite List.countCons rest y p then arithmetic [List.countPositive rest p x later passes]

theorem List.memOfCountPositive ∀ [auto eq: DecEq a] (c: a) (xs: List a) (positive: 0 < List.count xs (== c)): c ∈ xs :=
  match xs with
    | [x, ..rest] =>
      match t: x == c with
        | True => Inl t.read
        | False => Inr (List.memOfCountPositive c rest (arithmetic [List.countCons rest x (== c)]))

--| Filtering twice is filtering once by both tests.
theorem List.filterFilter ∀ (p q: a → Bool) (xs: List a):
    List.filter (List.filter xs p) q = List.filter xs (x => p x ∧ q x) :=
  match xs with
    | [] => byComputing
    | [x, ..rest] => rewrite <- List.filterFilter p q rest then cases

theorem List.countFalse ∀ (xs: List a): List.count xs (x => False) = 0 := match xs with
  | [] => byComputing
  | [x, ..rest] => List.countFalse rest

--| A count where no element passes is 0.
theorem List.countNone ∀ (xs: List a) (p: a → Bool) (none: ∀ (x: a) => x ∈ xs → p x = False): List.count xs p = 0 :=
  match xs with
    | [] => byComputing
    | [x, ..rest] =>
      rewrite List.countCons rest x p, none x (Inl byComputing), List.countNone rest p (y member => none y (Inr member))

theorem List.anyEmpty ∀ (xs: List a) (p: a → Bool) (empty: List.length xs = 0): List.any xs p = False := match xs with
  | [] => byComputing
  | [x, ..rest] => Void.impossible (Nat.succNotZero (List.length rest) empty)

--| The length of a `flatMap` is the sum of the lengths of the lists it joins.
theorem List.lengthFlatMap ∀ (f: a → List b) (xs: List a):
    List.length (List.flatMap xs f) = List.sumBy xs (x => List.length (f x)) :=
  match xs with
    | [] => byComputing
    | [x, ..rest] =>
      rewrite List.sumByCons rest x (x => List.length (f x)), <- List.lengthFlatMap f rest then
        List.lengthAppend (f x) (List.flatMap rest f)

theorem List.lengthFlatMapExample: List.length (List.flatMap [1, 2, 3] (n => List.replicate n n)) = 6 := byComputing

--| Counting over a `flatMap` adds up the counts over each list it joins.
theorem List.countFlatMap ∀ (f: a → List b) (p: b → Bool) (xs: List a):
    List.count (List.flatMap xs f) p = List.sumBy xs (x => List.count (f x) p) :=
  match xs with
    | [] => byComputing
    | [x, ..rest] =>
      rewrite List.countAppend (f x) (List.flatMap rest f) p,
          List.sumByCons rest x (x => List.count (f x) p),
          List.countFlatMap f p rest

--| `answer` of `items` have the property `p`: counting by a proposition,
--| for a `p` with no decision procedure to count with (a statement that
--| quantifies over functions, say). With a procedure, [`List.countWithIff`]
--| says the answer is [`List.count`]. For counting the values `x` with `p x`
--| over all values, see [`List.NumberWith`].
@[noReceiver]
def List.CountWith (p: a → Prop): (items: List a) → (answer: Nat) → Prop
  | [], answer => answer = 0
  | [item, ..rest], answer =>
    (p item ∧ ∃ (others: Nat) => List.CountWith p rest others ∧ answer = others + 1)
      ∨ (¬p item ∧ List.CountWith p rest answer)

--| Counting by a proposition is [`List.count`] by a `Bool` that decides it.
theorem List.countWithIff ∀ [p: a → Prop] (decide: a → Bool)
    (decides: ∀ (item: a) => decide item = True ↔ p item)
    (items: List a) (answer: Nat):
    List.CountWith p items answer ↔ answer = items.count decide :=
  match items with
    | [] => { forward = none => none, backward = none => none }
    | [item, ..rest] =>
      let later := List.countWithIff decide decides rest
      rewrite List.countCons rest item decide then
        match decided: decide item with
          | True =>
            let holds := (decides item).forward decided
            {
              forward = counted =>
                match counted with
                  | Inl (Both yes (Witness others (Both number more))) => arithmetic [(later others).forward number]
                  | Inr (Both no number) => (no holds).impossible,
              backward = same =>
                Inl
                  (Both holds
                    (Witness
                      (rest.count decide)
                      (Both ((later (rest.count decide)).backward byComputing) (arithmetic))))
            }
          | False =>
            let fails: ¬p item := holds => Bool.falseNotTrue (Eq.trans decided.flipped ((decides item).backward holds))
            {
              forward = counted =>
                match counted with
                  | Inl (Both yes more) => (fails yes).impossible
                  | Inr (Both no number) => (later answer).forward number,
              backward = same => Inr (Both fails ((later answer).backward (arithmetic)))
            }

--| Dropping a list's start leaves what was appended to it.
theorem List.dropAppend ∀ (start rest: List a): List.drop (List.append start rest) (List.length start) = rest :=
  match start with
    | [] => byComputing
    | [x, ..xs] => List.dropAppend xs rest

--| Nothing is left of the empty list, however much is dropped.
theorem List.dropNil ∀ (n: Nat): List.drop ([]: List a) n = [] := match n with
  | Zero => byComputing
  | Succ n => byComputing

--| Dropping `n + m` is dropping `n`, then `m`.
theorem List.dropAdd ∀ (n m: Nat) (xs: List a): List.drop xs (n + m) = List.drop (List.drop xs n) m := match n, xs with
  | Zero, xs => byComputing
  | Succ n, [] => (List.dropNil m).flipped
  | Succ n, [x, ..xs] => List.dropAdd n m xs

--| Taking `n + m` is taking `n`, then `m` of what is after them.
theorem List.takeAdd ∀ (xs: List a) (n m: Nat):
    List.take xs (n + m) = List.append (List.take xs n) (List.take (List.drop xs n) m) :=
  match xs, n with
    | xs, Zero => byComputing
    | [], Succ n => (List.takeNil m).flipped
    | [x, ..xs], Succ n => Eq.cong (Cons x) (List.takeAdd xs n m)

--| Dropping the whole length leaves nothing.
theorem List.dropLength ∀ (xs: List a): List.drop xs (List.length xs) = [] := match xs with
  | [] => byComputing
  | [x, ..xs] => List.dropLength xs

--| The empty list has nothing to take, whatever the count. Like
--| [`List.dropNil`] for `drop`; the proof takes the count apart because
--| `take` matches the count before the list.
theorem List.takeNil ∀ (n: Nat): List.take ([]: List a) n = [] := match n with
  | Zero => byComputing
  | Succ n => byComputing

--| A prefix is no longer than the list it came from, whether or not the
--| count reached the end. [`List.lengthTake`] gives the exact length when
--| the count is within the list, and [`List.takeAll`] gives the whole list
--| when it is past the end.
theorem List.lengthTakeLe ∀ (xs: List a) (n: Nat): List.length (List.take xs n) ≤ List.length xs := match xs, n with
  | [], Zero => arithmetic
  | [], Succ n => arithmetic
  | [x, ..xs], Zero => arithmetic
  | [x, ..xs], Succ n => List.lengthTakeLe xs n

--| Taking a prefix's own length gives the same prefix: taking more would
--| not add anything once the list has ended. This is the equality behind
--| [`List.lengthTakeLe`]; [`List.takeAll`] gives the same fact when the
--| count is known to be past the end.
theorem List.takeOwnLength ∀ (xs: List a) (n: Nat): List.take xs (List.length (List.take xs n)) = List.take xs n :=
  match xs, n with
    | xs, Zero => byComputing
    | [], Succ n => byComputing
    | [x, ..xs], Succ n => rewrite List.takeOwnLength xs n

--| Taking one past a drop that starts with `y` gives the prefix before `y`
--| and then `y`, and puts `y` inside the list. A run search knows the
--| `drop`, so this needs no element lookup with a fallback: [`List.takeSucc`]
--| states the same step through `List.getOr`, and needs `k < length` in
--| advance (which this concludes); [`List.dropAt`] says what the drop starts
--| with.
theorem List.takeOfDropCons ∀ (xs: List a) (k: Nat) (y: a) (ys: List a)
    (d: List.drop xs k = [y, ..ys]):
    List.take xs (k + 1) = List.append (List.take xs k) [y] ∧ k < List.length xs :=
  match xs, k with
    | [], Zero => cases
    | [x, ..xs], Zero => Both (rewrite List.consInjectiveHead x y xs ys d) (arithmetic)
    | [x, ..xs], Succ k =>
      let (Both taken below) := List.takeOfDropCons xs k y ys d
      Both (rewrite taken) (arithmetic)

--| A longer prefix of `Nat`s sums to at least as much, since every element
--| is non-negative. [`List.sumDropTakeLe`] compares a slice with the prefix
--| that contains it, and [`List.sumAppend`] splits a sum at a boundary.
theorem List.sumTakeMono ∀ (xs: List Nat) (i j: Nat)
    (le: i ≤ j):
    List.sum (List.take xs i) ≤ List.sum (List.take xs j) :=
  match xs, i, j with
    | xs, Zero, j => arithmetic
    | [], Succ i, Succ j => byComputing
    | [x, ..xs], Succ i, Succ j =>
      let ih: List.sumBy (List.take xs i) (y => y) ≤ List.sumBy (List.take xs j) (y => y) :=
        rewrite List.sumIsSumBy (List.take xs i), List.sumIsSumBy (List.take xs j) then
          List.sumTakeMono xs i j (arithmetic)
      rewrite List.sumIsSumBy [x, ..List.take xs i],
          List.sumIsSumBy [x, ..List.take xs j],
          List.sumByCons (List.take xs i) x (y => y),
          List.sumByCons (List.take xs j) x (y => y) then
        arithmetic [ih]

--| A slice sums to no more than the prefix that ends where it does: the
--| numbers before the slice, and those after the prefix's end, only add.
--| [`List.sumTakeMono`] is the case `d = 0`, and [`List.dropAdd`] moves the
--| slice's start.
theorem List.sumDropTakeLe ∀ (xs: List Nat) (d n: Nat):
    List.sum (List.take (List.drop xs d) n) ≤ List.sum (List.take xs (d + n)) :=
  match xs, d, n with
    | xs, Zero, n => arithmetic
    | [], Succ d, Zero => byComputing
    | [], Succ d, Succ n => byComputing
    | [x, ..xs], Succ d, n =>
      let ih: List.sumBy (List.take (List.drop xs d) n) (y => y) ≤ List.sumBy (List.take xs (d + n)) (y => y) :=
        rewrite List.sumIsSumBy (List.take (List.drop xs d) n), List.sumIsSumBy (List.take xs (d + n)) then
          List.sumDropTakeLe xs d n
      rewrite List.sumIsSumBy (List.take (List.drop [x, ..xs] (Succ d)) n),
          List.sumIsSumBy [x, ..List.take xs (d + n)],
          List.sumByCons (List.take xs (d + n)) x (y => y) then
        arithmetic [ih]

--| A prefix strips off a list that starts with it, when `same` holds of each
--| item and itself.
theorem List.stripPrefixByAppend ∀ (same: a → a → Bool)
    (reflexive: ∀ (x: a) => same x x = True) (prefix rest: List a):
    List.stripPrefixBy (List.append prefix rest) prefix same = Some rest :=
  match prefix with
    | [] => byComputing
    | [p, ..ps] => rewrite reflexive p, List.stripPrefixByAppend same reflexive ps rest

--| When `same` holds only of equal items, stripping `prefix` from `xs` leaves
--| `rest` only if `xs` is `prefix` followed by `rest`.
theorem List.stripPrefixByForward ∀ (same: a → a → Bool)
    (exact: ∀ (x y: a) => same x y = True → x = y)
    (xs prefix: List a) [rest: List a]
    (h: List.stripPrefixBy xs prefix same = Some rest):
    xs = List.append prefix rest :=
  match xs, prefix with
    | xs, [] => Option.someInjective h
    | [x, ..more], [p, ..ps] =>
      match holds: same p x with
        | True => rewrite exact p x holds then Eq.cong (Cons x) (List.stripPrefixByForward same exact more ps h)

--| Stripping `prefix` from `xs` leaves `rest` exactly when `xs` is `prefix`
--| followed by `rest`, for a `same` that holds of every item and itself and
--| only of equal items: `List.stripPrefixBy xs prefix same = Some rest ↔
--| xs = prefix ++ rest`. [`List.stripPrefixByForward`] is its forward
--| direction, and [`List.stripPrefixByAppend`] its backward direction.
theorem List.stripPrefixBySome ∀ (same: a → a → Bool)
    (reflexive: ∀ (x: a) => same x x = True)
    (exact: ∀ (x y: a) => same x y = True → x = y) (xs prefix rest: List a):
    List.stripPrefixBy xs prefix same = Some rest ↔ xs = List.append prefix rest :=
  {
    forward = List.stripPrefixByForward same exact xs prefix,
    backward = e => rewrite e then List.stripPrefixByAppend same reflexive prefix rest
  }

--| Stripping `prefix` from `xs` gives `None` when `xs` is not `prefix`
--| followed by any list, for a `same` that holds only of equal items. Use it
--| to show that a text or list does not start with a prefix;
--| [`List.stripPrefixBySome`] is the same fact with the result in hand.
theorem List.stripPrefixByNone ∀ (same: a → a → Bool)
    (exact: ∀ (x y: a) => same x y = True → x = y) (xs prefix: List a)
    (absent: ∀ (rest: List a) => xs ≠ List.append prefix rest):
    List.stripPrefixBy xs prefix same = None :=
  match found: List.stripPrefixBy xs prefix same with
    | None => byComputing
    | Some rest => Void.impossible (absent rest (List.stripPrefixByForward same exact xs prefix found))

--| Where `same` implies `r`, stripping `prefix` from `xs` leaves `rest` only if
--| `xs` is some `taken` followed by `rest`, with `r` holding of each item of
--| `prefix` and the one it was compared with. [`List.stripPrefixByForward`]
--| is the case where `r` is equality.
theorem List.stripPrefixByRelated ∀ (same: a → a → Bool) (r: a → a → Prop)
    (sound: ∀ (x y: a) => same x y = True → r x y) (xs prefix: List a) [rest: List a]
    (h: List.stripPrefixBy xs prefix same = Some rest):
    ∃ (taken: List a) => xs = List.append taken rest ∧ List.All2 r prefix taken :=
  match xs, prefix with
    | xs, [] => Witness [] (Both (Option.someInjective h) Trivial)
    | [x, ..more], [p, ..ps] =>
      match holds: same p x with
        | True =>
          match List.stripPrefixByRelated same r sound more ps h with
            | Witness taken (Both split related) =>
              Witness [x, ..taken] (Both (rewrite split) (Both (sound p x holds) related))

--| A list starts with what was appended to.
theorem List.startsWithAppend ∀ [auto eq: DecEq a] (prefix rest: List a):
    List.startsWith (List.append prefix rest) prefix = True :=
  match prefix with
    | [] => byComputing
    | [p, ..ps] => rewrite DecEq.refl p, List.startsWithAppend ps rest

--| A list that starts with `prefix` is `prefix`, then the rest of it.
theorem List.startsWithSplit ∀ [auto eq: DecEq a] (xs prefix: List a)
    (starts: List.startsWith xs prefix = True):
    List.append prefix (List.drop xs (List.length prefix)) = xs :=
  match xs, prefix with
    | xs, [] => byComputing
    | [x, ..xs], [p, ..ps] =>
      let Both sameHead more := starts
      rewrite sameHead.read, List.startsWithSplit xs ps more

--| A prefix is no longer than the list.
theorem List.startsWithLength ∀ [auto eq: DecEq a] (xs prefix: List a)
    (starts: List.startsWith xs prefix = True):
    List.length prefix ≤ List.length xs :=
  match xs, prefix with
    | xs, [] => byComputing
    | [x, ..xs], [p, ..ps] =>
      let Both _ more := starts
      List.startsWithLength xs ps more

--| Appending to `prefix` gives `xs` exactly when the appended list is the
--| rest of `xs`, once `xs` starts with `prefix`.
theorem List.appendEqDrop ∀ [auto eq: DecEq a] (xs prefix: List a)
    (starts: List.startsWith xs prefix = True) (rest: List a):
    (List.append prefix rest == xs) = (rest == List.drop xs (List.length prefix)) :=
  match same: rest == List.drop xs (List.length prefix) with
    | True => rewrite same.read, List.startsWithSplit xs prefix starts then DecEq.refl xs
    | False =>
      match made: List.append prefix rest == xs with
        | True =>
          let dropped :=
            Eq.trans (List.dropAppend prefix rest).flipped (Eq.cong (ys => List.drop ys (List.length prefix)) made.read)
          Void.impossible (same.read dropped)
        | False => byComputing

--| Nothing appended to `prefix` gives a list that doesn't start with it.
theorem List.appendNotEq ∀ [auto eq: DecEq a] (xs prefix: List a)
    (starts: List.startsWith xs prefix = False) (rest: List a):
    (List.append prefix rest == xs) = False :=
  match made: List.append prefix rest == xs with
    | True =>
      let startsAfter: List.startsWith xs prefix = True := rewrite <- made.read then List.startsWithAppend prefix rest
      Void.impossible (Bool.falseNotTrue (Eq.trans starts.flipped startsAfter))
    | False => byComputing

--| Stripping what was appended to gives the rest.
theorem List.stripPrefixAppend ∀ [auto eq: DecEq a] (prefix rest: List a):
    List.stripPrefix (List.append prefix rest) prefix = Some rest :=
  match prefix with
    | [] => byComputing
    | [p, ..ps] => rewrite DecEq.refl p then List.stripPrefixAppend ps rest

--| `stripPrefix` is `startsWith`, then `drop`.
theorem List.stripPrefixStartsWith ∀ [auto eq: DecEq a] (xs prefix: List a):
    List.stripPrefix xs prefix
      = (if List.startsWith xs prefix then Some (List.drop xs (List.length prefix)) else None) :=
  match xs, prefix with
    | xs, [] => byComputing
    | [], [p, ..ps] => byComputing
    | [x, ..xs], [p, ..ps] =>
      match same: x == p with
        | True => List.stripPrefixStartsWith xs ps
        | False => byComputing

--| `isEmpty` is `== []`.
theorem List.isEmptyEqNil ∀ [auto eq: DecEq a] (xs: List a): List.isEmpty xs = (xs == []) := match xs with
  | [] => byComputing
  | [x, ..xs] => byComputing

--| What passes a test after a `flatMap`: what passes in each list it joins,
--| added up.
theorem List.occurrencesFlatMap ∀ (f: a → List b) (p: b → Bool) (xs: List a):
    List.occurrences (List.flatMap xs f) p = List.sumBy xs (x => List.occurrences (f x) p) :=
  match xs with
    | [] => byComputing
    | [x, ..rest] =>
      rewrite List.occurrencesAppend (f x) (List.flatMap rest f) p,
          List.occurrencesFlatMap f p rest,
          List.sumByCons rest x (x => List.occurrences (f x) p)

--| Summing 1 for each element counts them.
theorem List.sumByOne ∀ (xs: List a): List.sumBy xs (x => 1) = List.length xs := match xs with
  | [] => byComputing
  | [x, ..rest] => rewrite List.sumByCons rest x (x => 1) then Eq.cong Succ (List.sumByOne rest)

--| An element's term is at most the sum.
theorem List.memLeSumBy ∀ (f: a → Nat) (xs: List a) (x: a) (none: x ∈ xs): f x ≤ List.sumBy xs f := match xs, none with
  | [], none => none.impossible
  | [first, ..rest], Inl same => rewrite List.sumByCons rest first f, same then Nat.leAddRight (f x) (List.sumBy rest f)
  | [first, ..rest], Inr later =>
    rewrite List.sumByCons rest first f then
      Nat.leTrans _ _ _ (List.memLeSumBy f rest x later) (Nat.leAddLeft (f first) (List.sumBy rest f))

test "List.sumByOne" := List.sumBy ["a", "b", "c"] (x => 1) == 3

theorem List.scanLeftCons ∀ (xs: List a) (z: b) (f: b → a → b):
    List.scanLeft xs z f = [z, ..List.drop (List.scanLeft xs z f) 1] :=
  match xs with
    | [] => byComputing
    | [x, ..xs] => byComputing

theorem List.scanLeftAppend ∀ (xs: List a) (z: b) (ys: List a) (f: b → a → b):
    List.drop (List.scanLeft (List.append xs ys) z f) 1
      = List.append (List.drop (List.scanLeft xs z f) 1) (List.drop (List.scanLeft ys (List.foldLeft xs z f) f) 1) :=
  match xs with
    | [] => byComputing
    | [x, ..xs] =>
      calc (xs ++ ys).scanLeft (f z x) f
        _ = [f z x, ..((xs ++ ys).scanLeft (f z x) f).drop 1] := List.scanLeftCons (List.append xs ys) (f z x) f
        _ = [f z x, ..(xs.scanLeft (f z x) f).drop 1 ++ (ys.scanLeft (xs.foldLeft (f z x) f) f).drop 1] :=
          Eq.cong (Cons (f z x)) (List.scanLeftAppend xs (f z x) ys f)
        _ = xs.scanLeft (f z x) f ++ (ys.scanLeft (xs.foldLeft (f z x) f) f).drop 1 :=
          Eq.cong
            (l => List.append l (List.drop (List.scanLeft ys (List.foldLeft xs (f z x) f) f) 1))
            (Eq.flipped (List.scanLeftCons xs (f z x) f))

theorem List.permRefl ∀ (xs: List a): List.Perm xs xs := p => byComputing

theorem List.permSym ∀ (xs ys: List a) (h: List.Perm xs ys): List.Perm ys xs := p => (h p).flipped

theorem List.permTrans ∀ (xs ys zs: List a) (h1: List.Perm xs ys) (h2: List.Perm ys zs): List.Perm xs zs := p =>
  Eq.trans (h1 p) (h2 p)

theorem List.occurrencesTrue ∀ (xs: List a): List.occurrences xs (x => True) = List.length xs := match xs with
  | [] => byComputing
  | [x, ..xs] => Eq.cong Succ (List.occurrencesTrue xs)

theorem List.permLength ∀ (xs ys: List a) (h: List.Perm xs ys): List.length xs = List.length ys := calc List.length xs
  _ = List.occurrences xs (x => True) := (List.occurrencesTrue xs).flipped
  _ = List.occurrences ys (x => True) := h (x => True)
  _ = List.length ys := List.occurrencesTrue ys

--| Some element passes `p` exactly when at least one does, so permutations
--| agree on `any`.
theorem List.anyOccurrences ∀ (xs: List a) (p: a → Bool): List.any xs p = Nat.leq 1 (List.occurrences xs p) :=
  match xs with
    | [] => byComputing
    | [x, ..xs] =>
      Bool.inspect
        (p x)
        (c => Bool.ifThenElse c (u => True) (u => List.any xs p) = Nat.leq 1 (Bool.toNat c + List.occurrences xs p))
        (t => byComputing)
        (f => List.anyOccurrences xs p)

theorem List.anyPerm ∀ (xs ys: List a) (h: List.Perm xs ys) (p: a → Bool): List.any xs p = List.any ys p :=
  calc List.any xs p
    _ = Nat.leq 1 (List.occurrences xs p) := List.anyOccurrences xs p
    _ = Nat.leq 1 (List.occurrences ys p) := Eq.cong (n => Nat.leq 1 n) (h p)
    _ = List.any ys p := (List.anyOccurrences ys p).flipped

-- Reversing is a permutation, and keeps sums.

--| Counting in a list reversed onto `acc` counts in the list and in `acc`.
theorem List.occurrencesReverseOnto ∀ (xs acc: List a) (p: a → Bool):
    List.occurrences (List.reverseOnto xs acc) p = List.occurrences xs p + List.occurrences acc p :=
  match xs with
    | [] => byComputing
    | [x, ..xs] =>
      calc (xs.reverseOnto [x, ..acc]).occurrences p
        _ = xs.occurrences p + ((p x).toNat + acc.occurrences p) := List.occurrencesReverseOnto xs [x, ..acc] p
        _ = (p x).toNat + (xs.occurrences p + acc.occurrences p) :=
          Nat.addLeftComm (List.occurrences xs p) (Bool.toNat (p x)) (List.occurrences acc p)
        _ = (p x).toNat + xs.occurrences p + acc.occurrences p :=
          Eq.flipped (Nat.addAssoc (Bool.toNat (p x)) (List.occurrences xs p) (List.occurrences acc p))

--| Reversing a list gives a permutation of it.
theorem List.reversePerm ∀ (xs: List a): List.Perm (List.reverse xs) xs := p =>
  Eq.trans (List.occurrencesReverseOnto xs [] p) (Nat.addZero (List.occurrences xs p))

theorem List.sumByReverseOnto ∀ (xs acc: List a) (f: a → Nat):
    List.sumBy (List.reverseOnto xs acc) f = List.sumBy xs f + List.sumBy acc f :=
  match xs with
    | [] => byComputing
    | [x, ..xs] =>
      calc (xs.reverseOnto [x, ..acc]).sumBy f
        _ = xs.sumBy f + [x, ..acc].sumBy f := List.sumByReverseOnto xs [x, ..acc] f
        _ = xs.sumBy f + (f x + List.sumBy acc (x => f x)) :=
          Eq.cong (t => List.sumBy xs f + t) (List.sumByCons acc x f)
        _ = f x + (xs.sumBy f + acc.sumBy f) := Nat.addLeftComm (List.sumBy xs f) (f x) (List.sumBy acc f)
        _ = f x + xs.sumBy f + acc.sumBy f := Eq.flipped (Nat.addAssoc (f x) (List.sumBy xs f) (List.sumBy acc f))
        _ = xs.foldLeft (f x) (acc x => acc + f x) + acc.sumBy f :=
          Eq.cong (t => t + List.sumBy acc f) (List.sumByCons xs x f).flipped

theorem List.sumByReverse ∀ (xs: List a) (f: a → Nat): List.sumBy (List.reverse xs) f = List.sumBy xs f :=
  Eq.trans (List.sumByReverseOnto xs [] f) (Nat.addZero (List.sumBy xs f))

--| Counting with a test nothing passes finds nothing.
theorem List.occurrencesNone ∀ (xs: List a) (p: a → Bool) (h: ∀ (x: a) => p x = False): List.occurrences xs p = 0 :=
  match xs with
    | [] => byComputing
    | [x, ..xs] => Eq.trans (Eq.cong (b => Bool.toNat b + List.occurrences xs p) (h x)) (List.occurrencesNone xs p h)

--| When nothing passes both `p` and `q`, the elements passing either are those
--| passing `p` plus those passing `q`.
theorem List.occurrencesOr ∀ (xs: List a) (p q: a → Bool)
    (h: ∀ (x: a) => p x = True → q x = False):
    List.occurrences xs (x => p x ∨ q x) = List.occurrences xs p + List.occurrences xs q :=
  match xs with
    | [] => byComputing
    | [x, ..xs] =>
      Bool.inspect
        (p x)
        (c =>
          Bool.toNat (c ∨ q x) + List.occurrences xs (x => p x ∨ q x)
            = (Bool.toNat c + List.occurrences xs p) + (Bool.toNat (q x) + List.occurrences xs q))
        (t =>
          Eq.trans
            (Eq.cong (n => 1 + n) (List.occurrencesOr xs p q h))
            (Eq.cong (b => (1 + List.occurrences xs p) + (Bool.toNat b + List.occurrences xs q)) (h x t).flipped))
        (f =>
          Eq.trans
            (Eq.cong (n => Bool.toNat (q x) + n) (List.occurrencesOr xs p q h))
            (Nat.addLeftComm (Bool.toNat (q x)) (List.occurrences xs p) (List.occurrences xs q)))

-- Lemmas for proofs about grids: runs' lengths, `map` and `filterMap` fused,
-- `init`, `last` and `reverse` of a `map`, and transposing a grid given cell
-- by cell.

--| `List.rangeFrom n s` has `n` elements.
theorem List.lengthRangeFrom ∀ (n s: Nat): List.length (List.rangeFrom n s) = n := match n with
  | Zero => byComputing
  | Succ n => rewrite List.lengthRangeFrom n (Succ s)

--| Mapping twice is mapping once by the composed function.
theorem List.mapMap ∀ (xs: List a) (f: b → c) (g: a → b): List.map (List.map xs g) f = List.map xs (x => f (g x)) :=
  match xs with
    | [] => byComputing
    | [x, ..xs] => rewrite List.mapMap xs f g

theorem List.filterMapMap ∀ (xs: List a) (f: b → Option c) (g: a → b):
    List.filterMap (List.map xs g) f = List.filterMap xs (x => f (g x)) :=
  match xs with
    | [] => byComputing
    | [x, ..xs] => rewrite List.filterMapMap xs f g

theorem List.filterMapSome ∀ (xs: List a) (f: a → b): List.filterMap xs (x => Some (f x)) = List.map xs f :=
  match xs with
    | [] => byComputing
    | [x, ..xs] => rewrite List.filterMapSome xs f

theorem List.filterMapAppend ∀ (xs ys: List a) (f: a → Option b):
    List.filterMap (List.append xs ys) f = List.append (List.filterMap xs f) (List.filterMap ys f) :=
  match xs with
    | [] => byComputing
    | [x, ..xs] =>
      match f x with
        | None => List.filterMapAppend xs ys f
        | Some y => rewrite List.filterMapAppend xs ys f

theorem List.initMap ∀ (xs: List a) (f: a → b): List.init (List.map xs f) = List.map (List.init xs) f := match xs with
  | [] => byComputing
  | [x] => byComputing
  | [x, y, ..ys] => rewrite List.initMap [y, ..ys] f

theorem List.lastMap ∀ (xs: List a) (f: a → b): List.last (List.map xs f) = Option.map (List.last xs) f := match xs with
  | [] => byComputing
  | [x] => byComputing
  | [x, y, ..ys] => List.lastMap [y, ..ys] f
theorem List.mapRangeFromShift ∀ (f: Nat → b) (n s: Nat):
    List.map (List.rangeFrom n (Succ s)) f = List.map (List.rangeFrom n s) (i => f (Succ i)) :=
  match n with
    | Zero => byComputing
    | Succ n => rewrite List.mapRangeFromShift f n (Succ s)

--| Shifting a range up by one: map over it is a map over the range below, with the argument shifted.
theorem List.mapRangeShift ∀ (f: Nat → b) (from until: Nat):
    List.map (List.range (from + 1) (until + 1)) f = List.map (List.range from until) (i => f (i + 1)) :=
  List.mapRangeFromShift f (until - from) from

--| Transposing a grid given cell by cell: row x, column y becomes row y, column x.
theorem List.transposeNGrid ∀ (rows: List a) (cols: List b) (cell: a → b → c):
    List.transposeN (List.length cols) (List.map rows (x => List.map cols (cell x)))
      = List.map cols (y => List.map rows (x => cell x y)) :=
  match cols with
    | [] => byComputing
    | [y, ..cols] =>
      calc List.transposeN (Succ (List.length cols)) (List.map rows (x => List.map [y, ..cols] (cell x)))
        _ = [
          List.filterMap (List.map rows (x => List.map [y, ..cols] (cell x))) (.get 0),
          ..List.transposeN (List.length cols) (List.map (List.map rows (x => List.map [y, ..cols] (cell x))) (.drop 1))
        ]
        _ = [
            List.filterMap rows (x => Some (cell x y)),
            ..List.transposeN (List.length cols) (List.map rows (x => List.map cols (cell x)))
          ] :=
          rewrite List.filterMapMap rows (.get 0) (x => List.map [y, ..cols] (cell x)),
              List.mapMap rows (.drop 1) (x => List.map [y, ..cols] (cell x))
        _ = [List.map rows (x => cell x y), ..List.map cols (z => List.map rows (x => cell x z))] :=
          rewrite List.filterMapSome rows (x => cell x y), List.transposeNGrid rows cols cell

theorem List.transposeGrid ∀ (rows: List a) (r: a) (cols: List b) (cell: a → b → c):
    List.transpose (List.map [r, ..rows] (x => List.map cols (cell x)))
      = List.map cols (y => List.map [r, ..rows] (x => cell x y)) :=
  calc List.transpose (List.map [r, ..rows] (x => List.map cols (cell x)))
    _ = List.transposeN (List.length (List.map cols (cell r))) (List.map [r, ..rows] (x => List.map cols (cell x)))
    _ = List.transposeN (List.length cols) (List.map [r, ..rows] (x => List.map cols (cell x))) :=
      rewrite List.lengthMap cols (cell r)
    _ = List.map cols (y => List.map [r, ..rows] (x => cell x y)) := List.transposeNGrid [r, ..rows] cols cell

theorem List.mapReverseOnto ∀ (xs acc: List a) (f: a → b):
    List.map (List.reverseOnto xs acc) f = List.reverseOnto (List.map xs f) (List.map acc f) :=
  match xs with
    | [] => byComputing
    | [x, ..xs] => List.mapReverseOnto xs [x, ..acc] f

theorem List.mapReverse ∀ (xs: List a) (f: a → b): List.map (List.reverse xs) f = List.reverse (List.map xs f) :=
  List.mapReverseOnto xs [] f

--| Reversing onto `acc`, then reversing that, is `acc` reversed onto the list.
theorem List.reverseOntoTwice ∀ (xs acc: List a):
    List.reverseOnto (List.reverseOnto xs acc) [] = List.reverseOnto acc xs :=
  match xs with
    | [] => byComputing
    | [x, ..xs] => List.reverseOntoTwice xs [x, ..acc]

--| Reversing twice gives the list back.
theorem List.reverseReverse ∀ (xs: List a): List.reverse (List.reverse xs) = xs := List.reverseOntoTwice xs []

--| Two lists with the same reverse are equal: reversing is injective.
theorem List.reverseInjective ∀ (xs ys: List a) (h: List.reverse xs = List.reverse ys): xs = ys :=
  Function.involutionInjective List.reverse List.reverseReverse xs ys h

--| Reversing onto an accumulator keeps the elements of both.
theorem List.memReverseOnto ∀ (x: a) (xs acc: List a): x ∈ List.reverseOnto xs acc ↔ (x ∈ xs ∨ x ∈ acc) := match xs with
  | [] => {
    forward = m => Inr m,
    backward = h =>
      match h with
        | Inl m => m.impossible
        | Inr m => m
  }
  | [y, ..ys] => {
    forward = m =>
      match (List.memReverseOnto x ys [y, ..acc]).forward m with
        | Inl i => Inl (Inr i)
        | Inr (Inl e) => Inl (Inl e)
        | Inr (Inr i) => Inr i,
    backward = h =>
      (List.memReverseOnto x ys [y, ..acc]).backward
        (match h with
          | Inl (Inl e) => Inr (Inl e)
          | Inl (Inr i) => Inl i
          | Inr i => Inr (Inr i))
  }

--| A list and its reverse have the same elements.
theorem List.memReverse ∀ (x: a) (xs: List a): x ∈ xs.reverse ↔ x ∈ xs := {
  forward = m =>
    match (List.memReverseOnto x xs []).forward m with
      | Inl i => i
      | Inr n => n.impossible,
  backward = m => (List.memReverseOnto x xs []).backward (Inl m)
}

--| Reversing onto `acc` is reversing, then appending `acc`.
theorem List.reverseOntoAppend ∀ (xs acc: List a): List.reverseOnto xs acc = List.append (List.reverseOnto xs []) acc :=
  match xs with
    | [] => byComputing
    | [x, ..xs] =>
      rewrite List.reverseOntoAppend xs [x, ..acc], List.reverseOntoAppend xs [x] then
        Eq.flipped (List.appendAssoc (List.reverseOnto xs []) [x] acc)

--| Reversing a list puts its first element last.
theorem List.reverseCons ∀ (x: a) (xs: List a): List.reverse [x, ..xs] = List.append (List.reverse xs) [x] :=
  List.reverseOntoAppend xs [x]

--| Reversing a list puts its last element first.
theorem List.reverseSnoc ∀ (xs: List a) (x: a): List.reverse (List.append xs [x]) = [x, ..List.reverse xs] :=
  match xs with
    | [] => byComputing
    | [y, ..rest] => rewrite List.reverseCons y (List.append rest [x]), List.reverseSnoc rest x, List.reverseCons y rest

--| Reversing a list that is two lists joined reverses each and swaps them:
--| `(xs ++ ys).reverse = ys.reverse ++ xs.reverse`.
theorem List.reverseAppend ∀ (xs ys: List a):
    List.reverse (List.append xs ys) = List.append (List.reverse ys) (List.reverse xs) :=
  match xs with
    | [] => Eq.flipped (List.appendNil (List.reverse ys))
    | [x, ..rest] =>
      calc [x, ..rest ++ ys].reverse
        _ = (rest ++ ys).reverse ++ [x] := List.reverseCons x (List.append rest ys)
        _ = (ys.reverse ++ rest.reverse) ++ [x] :=
          Eq.cong (reversed => List.append reversed [x]) (List.reverseAppend rest ys)
        _ = ys.reverse ++ rest.reverse ++ [x] := List.appendAssoc (List.reverse ys) (List.reverse rest) [x]
        _ = ys.reverse ++ [x, ..rest].reverse :=
          Eq.cong (tail => List.append (List.reverse ys) tail) (List.reverseCons x rest).flipped

theorem List.lengthReverseOnto ∀ (xs acc: List a):
    List.length (List.reverseOnto xs acc) = List.length xs + List.length acc :=
  match xs with
    | [] => byComputing
    | [x, ..rest] =>
      Eq.trans (List.lengthReverseOnto rest [x, ..acc]) (Nat.addSucc (List.length rest) (List.length acc))

--| Reversing keeps the length.
theorem List.lengthReverse ∀ (xs: List a): List.length (List.reverse xs) = List.length xs :=
  Eq.trans (List.lengthReverseOnto xs []) (Nat.addZero (List.length xs))

--| What holds of every item holds of every item reversed.
theorem List.allReverse ∀ (p: a → Prop) (xs: List a) (all: List.All p xs): List.All p (List.reverse xs) :=
  match xs, all with
    | [], _ => ()
    | [x, ..rest], Both hx hrest =>
      rewrite List.reverseCons x rest then
        List.allAppend p (List.reverse rest) [x] (List.allReverse p rest hrest) (Both hx ())

theorem List.lengthSnoc ∀ (xs: List a) (x: a): List.length (List.append xs [x]) = Succ (List.length xs) := match xs with
  | [] => byComputing
  | [y, ..rest] => Eq.cong Succ (List.lengthSnoc rest x)

--| Counting in a `flatMap` over a list reversed onto `acc`.
theorem List.occurrencesFlatMapReverseOnto ∀ (f: a → List b) (p: b → Bool) (xs acc: List a):
    List.occurrences (List.flatMap (List.reverseOnto xs acc) f) p
      = List.occurrences (List.flatMap xs f) p + List.occurrences (List.flatMap acc f) p :=
  match xs with
    | [] => byComputing
    | [x, ..rest] =>
      let here := List.occurrences (f x) p
      let before := List.occurrences (List.flatMap rest f) p
      let after := List.occurrences (List.flatMap acc f) p
      rewrite List.occurrencesFlatMapReverseOnto f p rest [x, ..acc],
          List.occurrencesAppend (f x) (List.flatMap acc f) p,
          List.occurrencesAppend (f x) (List.flatMap rest f) p then
        Eq.trans (Nat.addAssoc before here after).flipped (Eq.cong (t => t + after) (Nat.addComm before here))

--| A `flatMap` over the list reversed has the same elements.
theorem List.permFlatMapReverse ∀ (f: a → List b) (xs: List a):
    List.Perm (List.flatMap (List.reverse xs) f) (List.flatMap xs f) :=
  p => Eq.trans (List.occurrencesFlatMapReverseOnto f p xs []) (Nat.addZero (List.occurrences (List.flatMap xs f) p))

--| Adding up the values there are is adding up every value, with 0 for none.
theorem List.sumFilterMap ∀ (f: a → Option Nat) (xs: List a):
    List.sum (List.filterMap xs f) = List.sumBy xs (x => Option.getOrElse (f x) 0) :=
  match xs with
    | [] => byComputing
    | [x, ..rest] =>
      rewrite List.sumByCons rest x (y => Option.getOrElse (f y) 0), <- List.sumFilterMap f rest then
        match value: f x with
          | Some v => List.sumByCons (List.filterMap rest f) v (y => y)
          | None => byComputing

theorem List.reverseReverseExample: List.reverse (List.reverse [1, 2, 3]) = [1, 2, 3] := List.reverseReverse [1, 2, 3]

--| A test every element passes holds for all of them.
theorem List.allTrue ∀ (xs: List a) (p: a → Bool) (h: ∀ (x: a) => p x = True): List.all xs p = True := match xs with
  | [] => byComputing
  | [x, ..xs] => rewrite h x then List.allTrue xs p h

--| A test no element passes holds for none of them.
theorem List.anyFalse ∀ (xs: List a) (p: a → Bool) (h: ∀ (x: a) => p x = False): List.any xs p = False := match xs with
  | [] => byComputing
  | [x, ..xs] => rewrite h x then List.anyFalse xs p h

--| Every element passes both tests when every element passes each.
theorem List.allAnd ∀ (xs: List a) (p q: a → Bool): List.all xs (x => p x ∧ q x) = (List.all xs p ∧ List.all xs q) :=
  match xs with
    | [] => byComputing
    | [x, ..xs] =>
      match px: p x, qx: q x with
        | True, True => List.allAnd xs p q
        | True, False => cases
        | False, qx => byComputing

theorem Option.flatMapMap ∀ (m: Option a) (g: b → Option c) (f: a → b):
    Option.flatMap (Option.map m f) g = Option.flatMap m (x => g (f x)) :=
  match m with
    | None => byComputing
    | Some x => byComputing

theorem List.lengthZipWith3 ∀ (f: a → b → c → e) (xs: List a) (ys: List b) (zs: List c)
    (h1: List.length ys = List.length xs)
    (h2: List.length zs = List.length xs):
    List.length (List.zipWith3 xs ys zs f) = List.length xs :=
  match xs, ys, zs with
    | [], ys, zs => byComputing
    | [x, ..xs], [], zs => Void.impossible (Nat.zeroNotSucc (List.length xs) h1)
    | [x, ..xs], [y, ..ys], [] => Void.impossible (Nat.zeroNotSucc (List.length xs) h2)
    | [x, ..xs], [y, ..ys], [z, ..zs] =>
      rewrite List.lengthZipWith3 f xs ys zs (Nat.succInjective h1) (Nat.succInjective h2)

--| Lists zipped in step are no longer than the first.
theorem List.lengthZipWithLe ∀ (f: a → b → c) (xs: List a) (ys: List b):
    List.length (List.zipWith xs ys f) ≤ List.length xs :=
  match xs, ys with
    | [], ys => byComputing
    | [x, ..xs], [] => byComputing
    | [x, ..xs], [y, ..ys] => List.lengthZipWithLe f xs ys

theorem List.lengthZipWith3Le ∀ (f: a → b → c → d) (xs: List a) (ys: List b) (zs: List c):
    List.length (List.zipWith3 xs ys zs f) ≤ List.length xs :=
  match xs, ys, zs with
    | [], ys, zs => byComputing
    | [x, ..xs], [], zs => byComputing
    | [x, ..xs], [y, ..ys], [] => byComputing
    | [x, ..xs], [y, ..ys], [z, ..zs] => List.lengthZipWith3Le f xs ys zs

theorem List.lengthZipWith4Le ∀ (f: a → b → c → d → e) (xs: List a) (ys: List b) (zs: List c) (ws: List d):
    List.length (List.zipWith4 xs ys zs ws f) ≤ List.length xs :=
  match xs, ys, zs, ws with
    | [], ys, zs, ws => byComputing
    | [x, ..xs], [], zs, ws => byComputing
    | [x, ..xs], [y, ..ys], [], ws => byComputing
    | [x, ..xs], [y, ..ys], [z, ..zs], [] => byComputing
    | [x, ..xs], [y, ..ys], [z, ..zs], [w, ..ws] => List.lengthZipWith4Le f xs ys zs ws

--| Zipping with an empty list in a later place gives nothing.
theorem List.zipWith3NilSecond ∀ (zs: List c) (f: a → b → c → d) (xs: List a): List.zipWith3 xs [] zs f = [] :=
  match xs with
    | [] => byComputing
    | [x, ..xs] => byComputing

theorem List.zipWith3NilThird ∀ (f: a → b → c → d) (xs: List a) (ys: List b): List.zipWith3 xs ys [] f = [] :=
  match xs, ys with
    | [], ys => byComputing
    | [x, ..xs], [] => byComputing
    | [x, ..xs], [y, ..ys] => byComputing

theorem List.zipWith4NilSecond ∀ (zs: List c) (ws: List d) (f: a → b → c → d → e) (xs: List a):
    List.zipWith4 xs [] zs ws f = [] :=
  match xs with
    | [] => byComputing
    | [x, ..xs] => byComputing

theorem List.zipWith4NilThird ∀ (ws: List d) (f: a → b → c → d → e) (xs: List a) (ys: List b):
    List.zipWith4 xs ys [] ws f = [] :=
  match xs, ys with
    | [], ys => byComputing
    | [x, ..xs], [] => byComputing
    | [x, ..xs], [y, ..ys] => byComputing

theorem List.zipWith4NilFourth ∀ (f: a → b → c → d → e) (xs: List a) (ys: List b) (zs: List c):
    List.zipWith4 xs ys zs [] f = [] :=
  match xs, ys, zs with
    | [], ys, zs => byComputing
    | [x, ..xs], [], zs => byComputing
    | [x, ..xs], [y, ..ys], [] => byComputing
    | [x, ..xs], [y, ..ys], [z, ..zs] => byComputing

theorem List.distinctNil: List.Distinct ([]: List a) := Trivial

theorem List.distinctCons ∀ (x: a) (xs: List a) (h: x ∉ xs) (d: List.Distinct xs): List.Distinct [x, ..xs] := Both h d

--| An element of two lists joined is in one of them.
theorem List.memAppend ∀ (x: a) (xs ys: List a) (h1: x ∈ List.append xs ys): (x ∈ xs) ∨ (x ∈ ys) := match xs, h1 with
  | [], h => Inr h
  | [z, ..zs], Inl h => Inl (Inl h)
  | [z, ..zs], Inr h =>
    match List.memAppend x zs ys h with
      | Inl m => Inl (Inr m)
      | Inr m => Inr m

-- And back, `List.memAppendLeft` and `List.memAppendRight`, are in the core
-- (core/Finite.sw): derived `Finite` instances use them.

theorem List.memAppendExample: 3 ∈ List.append [1, 2] [3] := List.memAppendRight 3 [1, 2] [3] (Inl byComputing)

--| `f x` is in `List.map xs f` only if `x` is in `xs`, for an injective `f`.
theorem List.memMapInjective ∀ (f: a → b)
    (inj: ∀ (x y: a) => f x = f y → x = y)
    (x: a) (xs: List a)
    (h1: f x ∈ List.map xs f):
    x ∈ xs :=
  match xs, h1 with
    | [], h => h
    | [z, ..zs], Inl h => Inl (inj z x h)
    | [z, ..zs], Inr h => Inr (List.memMapInjective f inj x zs h)

--| If `x` is in `xs`, `f x` is in `List.map xs f`.
theorem List.memMap: ∀ (xs: List a) (x: a) => x ∈ xs → ∀ (f: a → b) => f x ∈ List.map xs f
  | [], x, h, f => h
  | [z, ..zs], x, Inl h, f => Inl (Eq.cong f h)
  | [z, ..zs], x, Inr h, f => Inr (List.memMap zs x h f)

--| Use "some element satisfies `p`": take that element, know it is in the
--| list, and carry on to the goal. (The library has no `Exists`.)
theorem List.anyElim ∀ (p: a → Prop) (goal: Prop):
    ∀ (xs: List a) => List.Any p xs → ∀ (cont: ∀ (x: a) => x ∈ xs → p x → goal) => goal
  | [], h, k => h.impossible
  | [z, ..zs], Inl h, k => k z (Inl byComputing) h
  | [z, ..zs], Inr h, k => List.anyElim p goal zs h (x inZs px => k x (Inr inZs) px)

--| To prove that some element satisfies `p`, give an element of the list that does. (For the
--| `Bool` `List.any`, [`List.anyOfMem`].)
theorem List.anyIntro ∀ (p: a → Prop) (x: a) (xs: List a) (h: x ∈ xs) (px: p x): List.Any p xs := match xs, h with
  | [], m => m.impossible
  | [z, ..zs], Inl e => Inl (rewrite e then px)
  | [z, ..zs], Inr m => Inr (List.anyIntro p x zs m px)

theorem List.anyIntroExample: List.Any (n => n > 2) [1, 2, 3] :=
  List.anyIntro (n => n > 2) 3 [1, 2, 3] (Inr (Inr (Inl byComputing))) byComputing

--| What is in `List.map xs f` is `f x` for some `x` in `xs` (said with
--| `List.Any`, which also says where `x` is: `Exists` wouldn't).
theorem List.memMapAny ∀ (xs: List a) (f: a → b) (y: b) (h1: y ∈ List.map xs f): List.Any (x => f x = y) xs :=
  match xs, h1 with
    | [], h => h
    | [z, ..zs], Inl h => Inl h
    | [z, ..zs], Inr h => Inr (List.memMapAny zs f y h)

--| `List.Any` gives a member that satisfies `p`.
theorem List.anyMember ∀ (p: a → Prop) (xs: List a) (none: List.Any p xs): Exists a (x => (x ∈ xs) ∧ (p x)) :=
  match xs, none with
    | [], none => none.impossible
    | [x, ..rest], Inl here => Witness x (Both (Inl byComputing) here)
    | [x, ..rest], Inr later =>
      Exists.elim (List.anyMember p rest later) (found both => Witness found (Both (Inr both.left) both.right))

--| A member of a mapped list is the image of a member.
theorem List.memMapElim ∀ (f: a → b) (y: b) (xs: List a)
    (member: y ∈ List.map xs f):
    Exists a (x => (x ∈ xs) ∧ (f x = y)) :=
  List.anyMember (x => f x = y) xs (List.memMapAny xs f y member)

--| What `(.filter p)` keeps was in the list, and passes `p`.
theorem List.memFilter ∀ (xs: List a) (p: a → Bool) [x: a] (h: x ∈ List.filter xs p): (x ∈ xs) ∧ (p x = True) :=
  match xs with
    | [y, ..ys] =>
      match e: p y with
        | True =>
          match h with
            | Inl q => Both (Inl q) (rewrite q at e)
            | Inr m =>
              match List.memFilter ys p m with
                | Both inYs px => Both (Inr inYs) px
        | False =>
          match List.memFilter ys p h with
            | Both inYs px => Both (Inr inYs) px

--| A `filter` that keeps nothing of the list is empty.
theorem List.filterNone ∀ (p: a → Bool) (xs: List a) (h: ∀ (x: a) => x ∈ xs → p x = False): List.filter xs p = [] :=
  match xs with
    | [] => byComputing
    | [x, ..xs] => rewrite h x (Inl byComputing) then List.filterNone p xs (y m => h y (Inr m))

--| A `filter` that keeps all of the list is the list.
theorem List.filterAll ∀ (p: a → Bool) (xs: List a) (h: ∀ (x: a) => x ∈ xs → p x = True): List.filter xs p = xs :=
  match xs with
    | [] => byComputing
    | [x, ..xs] => rewrite h x (Inl byComputing) then Eq.cong (Cons x) (List.filterAll p xs (y m => h y (Inr m)))

--| No successor is zero, and every one is at least 1.
theorem List.filterNoneExample ∀ (xs: List Nat): List.filter (List.map xs Succ) (n => n == 0) = [] :=
  List.filterNone (n => n == 0) (List.map xs Succ) (n m =>
    List.anyElim (x => Succ x = n) ((n == 0) = False) xs (List.memMapAny xs Succ n m) (x inXs e => rewrite <- e))

theorem List.filterAllExample ∀ (xs: List Nat): List.filter (List.map xs Succ) (n => Nat.leq 1 n) = List.map xs Succ :=
  List.filterAll (n => Nat.leq 1 n) (List.map xs Succ) (n m =>
    List.anyElim (x => Succ x = n) (Nat.leq 1 n = True) xs (List.memMapAny xs Succ n m) (x inXs e => rewrite <- e))

--| A list's `flatMap`: an element of `f x` for an `x` of the list is in it.
theorem List.memFlatMapIntro ∀ (f: a → List b) (x: a) (y: b) (xs: List a)
    (h1: x ∈ xs)
    (m: y ∈ f x):
    y ∈ List.flatMap xs f :=
  match xs, h1 with
    | [], h => h.impossible
    | [z, ..zs], Inl h => List.anyAppendLeft (w => w = y) (f z) (List.flatMap zs f) (rewrite h then m)
    | [z, ..zs], Inr h => List.anyAppendRight (w => w = y) (f z) (List.flatMap zs f) (List.memFlatMapIntro f x y zs h m)

--| `flatMap` over an appended list is the two `flatMap`s appended.
theorem List.flatMapAppend ∀ (f: a → List b) (first second: List a):
    List.flatMap (List.append first second) f = List.append (List.flatMap first f) (List.flatMap second f) :=
  match first with
    | [] => byComputing
    | [head, ..tail] =>
      calc List.flatMap (List.append [head, ..tail] second) f
        _ = List.append (f head) (List.append (List.flatMap tail f) (List.flatMap second f)) :=
          Eq.cong (back => List.append (f head) back) (List.flatMapAppend f tail second)
        _ = List.append (List.append (f head) (List.flatMap tail f)) (List.flatMap second f) :=
          (List.appendAssoc (f head) (List.flatMap tail f) (List.flatMap second f)).flipped

--| `flatMap` over a concatenation is the `flatMap` of each group's `flatMap`.
theorem List.flatMapConcat ∀ (f: a → List b) (groups: List (List a)):
    List.flatMap (List.concat groups) f = List.flatMap groups (group => List.flatMap group f) :=
  match groups with
    | [] => byComputing
    | [group, ..rest] =>
      calc List.flatMap (List.concat [group, ..rest]) f
        _ = List.append (List.flatMap group f) (List.flatMap (List.concat rest) f) :=
          List.flatMapAppend f group (List.concat rest)
        _ = List.append (List.flatMap group f) (List.flatMap rest (group => List.flatMap group f)) :=
          Eq.cong (back => List.append (List.flatMap group f) back) (List.flatMapConcat f rest)

--| What is in a `flatMap` is in `f x` for some `x` of the list.
theorem List.memFlatMapElim ∀ (f: a → List b) (y: b) (xs: List a)
    (h: y ∈ List.flatMap xs f):
    List.Any (x => y ∈ f x) xs :=
  match xs with
    | [z, ..zs] =>
      match List.memAppend y (f z) (List.flatMap zs f) h with
        | Inl m => Inl m
        | Inr m => Inr (List.memFlatMapElim f y zs m)

--| What is in a `flatMap` is in `f x` for some `x` of the list, and back:
--| [`List.memFlatMapIntro`] and [`List.memFlatMapElim`] as one statement, to
--| rewrite with.
theorem List.memFlatMap ∀ (f: a → List b) (y: b) (xs: List a): (y ∈ xs.flatMap f) ↔ (∃ (x: a) => x ∈ xs ∧ y ∈ f x) := {
  forward = h => List.anyMember (x => y ∈ f x) xs (List.memFlatMapElim f y xs h),
  backward = found => Exists.elim found (x both => List.memFlatMapIntro f x y xs both.left both.right)
}

--| [`List.memFlatMapIntro`] for the spelling `concat (map xs f)`.
theorem List.memConcatMapIntro ∀ (f: a → List b) (x: a) (y: b) (xs: List a)
    (inXs: x ∈ xs)
    (inF: y ∈ f x):
    y ∈ List.concat (List.map xs f) :=
  rewrite <- List.flatMapEqConcatMap f xs then List.memFlatMapIntro f x y xs inXs inF

--| [`List.memFlatMapElim`] for the spelling `concat (map xs f)`.
theorem List.memConcatMapElim ∀ (f: a → List b) (y: b) (xs: List a)
    (member: y ∈ List.concat (List.map xs f)):
    List.Any (x => y ∈ f x) xs :=
  List.memFlatMapElim f y xs (rewrite List.flatMapEqConcatMap f xs then member)

--| Mapping an injective function keeps a list distinct.
theorem List.distinctMap: ∀ (xs: List a) => List.Distinct xs
      → ∀ (f: a → b) (inj: ∀ (x y: a) => f x = f y → x = y) => List.Distinct (List.map xs f)
  | [], d, f, inj => Trivial
  | [x, ..xs], Both h d, f, inj => Both (m => h (List.memMapInjective f inj x xs m)) (List.distinctMap xs d f inj)

--| Mapping a function that is injective on the list's own members keeps the
--| list distinct; [`List.distinctMap`] needs it injective everywhere.
theorem List.distinctMapOn ∀ (f: a → b) (xs: List a)
    (h: List.Distinct xs)
    (injective: ∀ (x y: a) => x ∈ xs → y ∈ xs → f x = f y → x = y):
    List.Distinct (List.map xs f) :=
  match xs, h with
    | [], distinct => Trivial
    | [x, ..xs], Both fresh distinct =>
      Both
        (member =>
          match List.memMapElim f (f x) xs member with
            | Witness y (Both inRest same) =>
              fresh (rewrite injective x y (Inl byComputing) (Inr inRest) same.flipped then inRest))
        (List.distinctMapOn f xs distinct (first second inFirst inSecond same =>
          injective first second (Inr inFirst) (Inr inSecond) same))

--| Two distinct lists with no element in common, joined, are distinct.
theorem List.distinctAppend ∀ (xs ys: List a)
    (h: List.Distinct xs)
    (dy: List.Distinct ys)
    (h1: List.Disjoint xs ys):
    List.Distinct (List.append xs ys) :=
  match xs, h, h1 with
    | [], dx, dj => dy
    | [x, ..xs], Both hx dx, Both hj dj =>
      Both
        (m =>
          match List.memAppend x xs ys m with
            | Inl inXs => hx inXs
            | Inr inYs => hj inYs)
        (List.distinctAppend xs ys dx dy dj)

--| The parts of a list with no repeats have none, and nothing in common.
theorem List.distinctAppendLeft ∀ (xs ys: List a) (h: List.Distinct (List.append xs ys)): List.Distinct xs :=
  match xs, h with
    | [], d => Trivial
    | [x, ..rest], Both out d => Both (m => out (List.memAppendLeft x rest ys m)) (List.distinctAppendLeft rest ys d)

theorem List.distinctAppendRight ∀ (xs ys: List a) (h: List.Distinct (List.append xs ys)): List.Distinct ys :=
  match xs, h with
    | [], d => d
    | [x, ..rest], Both out d => List.distinctAppendRight rest ys d

theorem List.distinctAppendApart: ∀ (xs ys: List a) => List.Distinct (List.append xs ys)
      → ∀ (z: a) => z ∈ xs → z ∈ ys → Void
  | [], ys, d, z, inXs, inYs => inXs
  | [x, ..rest], ys, Both out d, z, Inl e, inYs => out (List.memAppendRight x rest ys (rewrite e then inYs))
  | [x, ..rest], ys, Both out d, z, Inr inRest, inYs => List.distinctAppendApart rest ys d z inRest inYs

--| Two lists with the same head are equal only if their tails are.
theorem List.consInjective ∀ (x: a) (ys zs: List a) (p: [x, ..ys] = [x, ..zs]): ys = zs := Eq.cong (.drop 1) p

--| Two equal non-empty lists have the same head: the complement of
--| [`List.consInjective`], which gives the tails when the heads are the same.
theorem List.consInjectiveHead ∀ (x y: a) (xs ys: List a) (p: [x, ..xs] = [y, ..ys]): x = y :=
  Eq.cong (list => (list.get 0).getOrElse x) p

--| Two non-empty lists are `==` when their heads are and their tails are.
theorem List.beqCons ∀ [auto eq: DecEq a] (x: a) (xs: List a) (y: a) (ys: List a):
    ([x, ..xs] == [y, ..ys]) = (x == y ∧ xs == ys) :=
  Bool.eqOf _ _
    (same =>
      let lists := DecEq.sound [x := [x, ..xs]] [y := [y, ..ys]] same
      rewrite List.consInjectiveHead x y xs ys lists, (Eq.cong (.drop 1) lists: xs = ys) then
        Both (DecEq.refl y) (DecEq.refl ys))
    (both =>
      let Both heads tails := both
      rewrite heads.read, tails.read then DecEq.refl [y, ..ys])

--| The empty list is never `==` to a non-empty one.
theorem List.beqNilCons ∀ [auto eq: DecEq a] (y: a) (ys: List a): (([]: List a) == [y, ..ys]) = False :=
  match e: (([]: List a) == [y, ..ys]) with | False => byComputing

--| A non-empty list is never `==` to the empty one.
theorem List.beqConsNil ∀ [auto eq: DecEq a] (x: a) (xs: List a): ([x, ..xs] == ([]: List a)) = False :=
  match e: ([x, ..xs] == ([]: List a)) with | False => byComputing

--| A list starting with x isn't among lists that all start with y, a
--| different element.
theorem List.notMemMapCons ∀ (x y: a) (ne: x ≠ y) (xs: List a) (ys: List (List a)): [x, ..xs] ∉ List.map ys (Cons y) :=
  match ys with
    | [] => m => m
    | [z, ..zs] =>
      match
        | Inl p => ne (Eq.flipped (Eq.cong (.headOr x) p))
        | Inr q => List.notMemMapCons x y ne xs zs q

--| Lists that all start with x and lists that all start with a different y
--| have none in common.
theorem List.disjointMapCons ∀ (ys: List (List a)) (x y: a)
    (ne: x ≠ y) (xs: List (List a)):
    List.Disjoint (List.map xs (Cons x)) (List.map ys (Cons y)) :=
  match xs with
    | [] => Trivial
    | [z, ..zs] => Both (List.notMemMapCons x y ne z ys) (List.disjointMapCons ys x y ne zs)

--| A run of numbers has no repeats.
theorem List.distinctRangeFrom ∀ (c s: Nat): List.Distinct (List.rangeFrom c s) := match c with
  | Zero => Trivial
  | Succ c =>
    Both
      (m =>
        match List.memRangeFrom s c (Succ s) m with
          | Both above _ => Nat.lessIrrefl s above)
      (List.distinctRangeFrom c (Succ s))

--| A range has no repeats.
theorem List.distinctRange ∀ (a b: Nat): List.Distinct (List.range a b) := List.distinctRangeFrom (b - a) a

--| Every element of the list passes, given that each element that is in it does.
theorem List.allOfMem ∀ (p: a → Prop) (xs: List a) (h: ∀ (x: a) => x ∈ xs → p x): List.All p xs := match xs with
  | [] => Trivial
  | [z, ..zs] => Both (h z (Inl byComputing)) (List.allOfMem p zs (x inZs => h x (Inr inZs)))

--| A `flatMap` of distinct lists has no repeats if the list mapped over has none
--| and the lists apart: `key` says which element of `xs` each result came from.
theorem List.distinctFlatMap ∀ (f: a → List b) (key: b → a) (xs: List a)
    (d: List.Distinct xs)
    (distinctEach: ∀ (x: a) => x ∈ xs → List.Distinct (f x))
    (keyed: ∀ (x: a) => x ∈ xs → ∀ (y: b) => y ∈ f x → key y = x):
    List.Distinct (List.flatMap xs f) :=
  match xs, d with
    | [], d => Trivial
    | [x, ..xs], Both notLater later =>
      List.distinctAppend
        (f x)
        (List.flatMap xs f)
        (distinctEach x (Inl byComputing))
        (List.distinctFlatMap f key xs later (z inXs => distinctEach z (Inr inXs)) (z inXs => keyed z (Inr inXs)))
        -- Nothing in `f x` is in a later `f z`: it would have key `x` and key `z`.
        (List.allOfMem (y => y ∉ List.flatMap xs f) (f x) (y fromX inLater =>
          List.anyElim (z => y ∈ f z) Void xs (List.memFlatMapElim f y xs inLater) (z inXs fromZ =>
            notLater
              (rewrite Eq.trans (Eq.flipped (keyed x (Inl byComputing) y fromX)) (keyed z (Inr inXs) y fromZ) then
                inXs))))

--| [`List.distinctFlatMap`] for the spelling `concat (map xs f)`.
theorem List.distinctConcatMap ∀ (f: a → List b) (key: b → a) (xs: List a)
    (distinct: List.Distinct xs)
    (distinctEach: ∀ (x: a) => x ∈ xs → List.Distinct (f x))
    (keyed: ∀ (x: a) => x ∈ xs → ∀ (y: b) => y ∈ f x → key y = x):
    List.Distinct (List.concat (List.map xs f)) :=
  rewrite <- List.flatMapEqConcatMap f xs then List.distinctFlatMap f key xs distinct distinctEach keyed

--| A member of a list splits it around that occurrence:
--| `[1, 2, 3]` is `[1] ++ [2, ..[3]]` for the 2.
theorem List.memSplit ∀ (x: a) (xs: List a)
    (member: x ∈ xs):
    ∃ (before: List a) => ∃ (after: List a) => xs = before ++ [x, ..after] :=
  match xs, member with
    | [], member => member.impossible
    | [z, ..zs], Inl same => Witness [] (Witness zs (rewrite same))
    | [z, ..zs], Inr later =>
      match List.memSplit x zs later with
        | Witness before (Witness after eq) => Witness [z, ..before] (Witness after (Eq.cong (Cons z) eq))

--| A list with no repeats whose elements are all in `ys` is no longer than
--| `ys` (`ys` itself may repeat). The pigeonhole principle for lists is
--| [`List.pigeonhole`].
theorem List.distinctLength ∀ [auto eq: DecEq a] (xs ys: List a)
    (h: List.Distinct xs)
    (drawn: ∀ (x: a) => x ∈ xs → x ∈ ys):
    List.length xs ≤ List.length ys :=
  match xs, h with
    | [], d => Nat.zeroLe (List.length ys)
    | [x, ..rest], Both out d =>
      let others := ys.filter (y => Bool.not (y == x))
      let dropped: Bool.not (x == x) = False := rewrite DecEq.refl x
      let drawnOthers: ∀ (y: a) => y ∈ rest → y ∈ others := y inRest =>
        List.memFilterIntro ys
          (y => Bool.not (y == x))
          (drawn y (Inr inRest))
          (match e: y == x with
            | True => Void.impossible (out (rewrite <- e.read then inRest))
            | False => byComputing)
      arithmetic [
        List.distinctLength rest others d drawnOthers,
        List.lengthFilterLt (y => Bool.not (y == x)) x dropped ys (drawn x (Inl byComputing))
      ]

--| The pigeonhole principle for lists: if every element of `xs` is one of
--| the elements of `ys`, and `xs` is longer than `ys`, then `xs` repeats an
--| element, that is, it is not [`List.Distinct`]. `ys` may itself have
--| repeats, so its length is an upper bound on the distinct values: a path
--| of more steps than a graph has nodes passes through one twice.
--|
--| `¬List.Distinct xs` is the form to use when the repeat only has to be
--| known to exist; [`List.repeatSplit`] turns it into the two positions,
--| for an argument that cuts the repeated stretch out or repeats it. For
--| example ([`List.pigeonholeExample`]), `[1, 2, 1]` is drawn from `[1, 2]`
--| and longer, so it repeats.
theorem List.pigeonhole ∀ [auto eq: DecEq a] (xs ys: List a)
    (drawn: ∀ (x: a) => x ∈ xs → x ∈ ys)
    (shorter: List.length ys < List.length xs):
    ¬List.Distinct xs :=
  d => arithmetic [List.distinctLength xs ys d drawn]

--| A list that is not [`List.Distinct`] has some element twice: it is
--| `before`, then the element, then `between`, then the element again, then
--| `after`, as `[1, 2, 1]` is `[] ++ [1, ..([2] ++ [1, ..[]])]`. Cutting
--| out `between` and one copy of the element, or repeating them, keeps the
--| list's neighbours the same, which a walk that revisits a node needs.
theorem List.repeatSplit ∀ [auto eq: DecEq a] (xs: List a)
    (notDistinct: ¬List.Distinct xs):
    ∃ (before: List a) => ∃ (x: a) => ∃ (between: List a) => ∃ (after: List a) => xs
      = before ++ [x, ..(between ++ [x, ..after])] :=
  match xs with
    | [] => (notDistinct Trivial).impossible
    | [y, ..rest] =>
      if found: y ∈ rest then
        match List.memSplit y rest found with
          | Witness between (Witness after eq) =>
            Witness [] (Witness y (Witness between (Witness after (Eq.cong (Cons y) eq))))
      else
        match List.repeatSplit rest (d => notDistinct (Both found d)) with
          | Witness before (Witness x (Witness between (Witness after eq))) =>
            Witness [y, ..before] (Witness x (Witness between (Witness after (Eq.cong (Cons y) eq))))

theorem List.pigeonholeExample: ¬List.Distinct [1, 2, 1] :=
  List.pigeonhole
    [1, 2, 1]
    [1, 2]
    (x m =>
      match m with
        | Inl p => Inl p
        | Inr (Inl p) => Inr (Inl p)
        | Inr (Inr (Inl p)) => Inl p
        | Inr (Inr (Inr v)) => v.impossible)
    byDecision

theorem List.distinctExample: List.Distinct [1, 2] :=
  Both
    (m =>
      match m with
        | Inl p => Nat.succNotZero 0 (Nat.succInjective p)
        | Inr v => v)
    (Both (m => m) Trivial)

theorem List.distinctMapExample: List.Distinct (List.map [1, 2] Succ) :=
  List.distinctMap [1, 2] List.distinctExample Succ (x y p => Nat.succInjective p)

theorem List.consInjectiveExample ∀ (ys zs: List Nat) (p: [1, ..ys] = [1, ..zs]): ys = zs :=
  List.consInjective 1 ys zs p

theorem List.disjointMapConsExample: List.Disjoint (List.map [[1], [2]] (Cons 0)) (List.map [[1], []] (Cons 1)) :=
  List.disjointMapCons [[1], []] 0 1 (p => Nat.succNotZero 0 p.flipped) [[1], [2]]

theorem List.distinctMapConsExample: List.Distinct (List.append (List.map [[]] (Cons 0)) (List.map [[]] (Cons 1))) :=
  List.distinctAppend
    (List.map [[]] (Cons 0))
    (List.map [[]] (Cons 1))
    (List.distinctMap [[]] (Both (m => m) Trivial) (Cons 0) (List.consInjective 0))
    (List.distinctMap [[]] (Both (m => m) Trivial) (Cons 1) (List.consInjective 1))
    (List.disjointMapCons [[]] 0 1 (p => Nat.succNotZero 0 p.flipped) [[]])

--| `x` is in `List.range a b` exactly when `a ≤ x < b`.
theorem List.memRange ∀ (x a b: Nat): x ∈ List.range a b ↔ (a ≤ x < b) :=
  { forward = List.memRangeBounds x a b, backward = List.memRangeOf x a b }

--| `List.inRange x a b` holds exactly when `x ∈ a ..< b`.
theorem List.inRangeIff ∀ (x a b: Nat): (List.inRange x a b = True) ↔ (x ∈ List.range a b) := {
  forward = h => (List.memRange x a b).backward arithmetic,
  backward = m =>
    let bounds := (List.memRange x a b).forward m
    arithmetic
}

--| Looking for `x` in a range with `contains` gives the two comparisons `x in a ..< b` is.
theorem List.containsRange ∀ (a b x: Nat): List.contains (List.range a b) x = List.inRange x a b :=
  match c: List.contains (List.range a b) x with
    | True => Eq.flipped ((List.inRangeIff x a b).backward c.read)
    | False =>
      match d: List.inRange x a b with
        | True =>
          Void.impossible
            (Bool.trueNotFalse
              (Eq.trans
                (Eq.flipped ((List.memContains (List.range a b) x).backward ((List.inRangeIff x a b).forward d)))
                c))
        | False => byComputing

theorem List.memRangeExample: 3 ∈ List.range 1 6 := (List.memRange 3 1 6).backward (Both byComputing byComputing)

theorem List.memFlatMapExample: 20 ∈ List.flatMap [1, 2] (x => [x, x * 10]) :=
  List.memFlatMapIntro (x => [x, x * 10]) 2 20 [1, 2] (Inr (Inl byComputing)) (Inr (Inl byComputing))

theorem List.memFlatMapExample2: 20 ∈ List.flatMap [1, 2] (x => [x, x * 10])
      ↔ (∃ (x: Nat) => x ∈ [1, 2] ∧ 20 ∈ [x, x * 10]) :=
  List.memFlatMap (x => [x, x * 10]) 20 [1, 2]

theorem List.distinctAppendExample: List.Distinct (List.append [1] [2]) :=
  List.distinctAppend
    [1]
    [2]
    (Both (m => m) Trivial)
    (Both (m => m) Trivial)
    (Both
      (m =>
        match m with
          | Inl p => Nat.succNotZero 0 (Nat.succInjective p)
          | Inr v => v)
      Trivial)

--| What `List.All` says of an element of the list.
theorem List.allMem ∀ (p: a → Prop) (x: a) (xs: List a) (h1: List.All p xs) (h2: x ∈ xs): p x := match xs, h1, h2 with
  | [], h, m => m.impossible
  | [z, ..zs], Both pz h, Inl e => rewrite <- e then pz
  | [z, ..zs], Both pz h, Inr m => List.allMem p x zs h m

-- `List.find` and `List.any`, and keys that are distinct (SW-363): lemmas
-- for code that finds records by an id.

--| What `List.find` finds passes the test and is in the list.
theorem List.findSome ∀ (xs: List a) (p: a → Bool) (y: a) (h: List.find xs p = Some y): (p y = True) ∧ (y ∈ xs) :=
  match xs with
    | [x, ..xs] =>
      match e: p x with
        | True => Both (Eq.trans (Eq.cong p (Option.someInjective h).flipped) e) (Inl (Option.someInjective h))
        | False =>
          match List.findSome xs p y h with
            | Both py m => Both py (Inr m)

--| `List.find` finds nothing only when no element passes.
theorem List.findNoneNotMem ∀ (xs: List a) (p: a → Bool) (x: a)
    (px: p x = True)
    (h1: x ∈ xs)
    (h: List.find xs p = None):
    Void :=
  match xs, h1 with
    | [], m => m
    | [z, ..zs], Inl e => Option.someNotNone x (rewrite e, px at h)
    | [z, ..zs], Inr m =>
      match c: p z with
        | False => List.findNoneNotMem zs p x px m h

--| Finding nothing means every element fails, as an `all`. So
--| `find xs bad = None` gives `xs.all (x => ¬(bad x))`, and a search for
--| one that isn't `good` finding nothing gives `xs.all good`.
theorem List.findNoneAll ∀ (xs: List a) (p: a → Bool) (h: List.find xs p = None): List.all xs (x => ¬(p x)) = True :=
  match xs with
    | [] => byComputing
    | [x, ..rest] =>
      match e: p x with
        | False => List.findNoneAll rest p h

theorem List.findNotNoneAll ∀ (xs: List a) (good: a → Bool)
    (h: List.find xs (x => ¬(good x)) = None):
    List.all xs good = True :=
  match xs with
    | [] => byComputing
    | [x, ..rest] =>
      match e: good x with
        | True => List.findNotNoneAll rest good h

--| Searching the elements paired with their indices (`withIndex`) by the
--| element alone finds nothing exactly when searching the list does.
theorem List.findWithIndexFromNone ∀ (p: a → Bool) (i: Nat) (xs: List a)
    (h: List.find (List.withIndexFrom i xs) (((_, x)) => p x) = None):
    List.find xs p = None :=
  match xs with
    | [] => byComputing
    | [x, ..rest] =>
      match e: p x with
        | False => List.findWithIndexFromNone p (Succ i) rest h

--| Searching the elements paired with their indices by the element alone finds
--| nothing when searching the list does ([`List.findWithIndexFromNone`] the
--| other way).
theorem List.findNoneWithIndexFrom ∀ (p: a → Bool) (i: Nat) (xs: List a)
    (h: List.find xs p = None):
    List.find (List.withIndexFrom i xs) (((_, x)) => p x) = None :=
  match xs with
    | [] => byComputing
    | [x, ..rest] =>
      match e: p x with
        | False => List.findNoneWithIndexFrom p (Succ i) rest h

--| `List.find` finds nothing when no element passes ([`List.findNoneNotMem`]
--| the other way).
theorem List.findNoneOfMem ∀ (p: a → Bool) (xs: List a)
    (fails: ∀ (x: a) => x ∈ xs → p x = False):
    List.find xs p = None :=
  match xs with
    | [] => byComputing
    | [x, ..rest] => rewrite fails x (Inl byComputing) then List.findNoneOfMem p rest (y member => fails y (Inr member))

-- `List.find` over `List.range`: what it finds is the least number that
-- passes, and when it finds nothing, no number in the range passes.

--| No number from `start` up to the one found passes.
theorem List.findRangeFirst ∀ (passes: Nat → Bool):
    ∀ (count start found: Nat) => (List.rangeFrom count start).find passes = Some found
      → ∀ (earlier: Nat) => start ≤ earlier → earlier < found → passes earlier = False
  | Zero, start, found, h, earlier, low, high => (Option.noneNotSome found h).impossible
  | Succ count, start, found, h, earlier, low, high =>
    match c: passes start with
      | True =>
        let same: start = found := Option.someInjective h
        Void.impossible
          (Nat.lessIrrefl earlier (Nat.leTrans (Succ earlier) found earlier high (rewrite <- same then low)))
      | False =>
        match e: earlier == start with
          | True => rewrite e.read then c
          | False =>
            let later: Succ start ≤ earlier := Nat.leNeSucc start earlier low (p => e.read p.flipped)
            List.findRangeFirst passes count (Succ start) found h earlier later high

--| What is found passes, is in the range, and no smaller number passes.
theorem List.findRangeSome ∀ (passes: Nat → Bool) (count found: Nat)
    (h: (List.range 0 count).find passes = Some found):
    (passes found = True) ∧ ((found < count) ∧ (∀ (earlier: Nat) => earlier < found → passes earlier = False)) :=
  match List.findSome (List.range 0 count) passes found h with
    | Both foundPasses member =>
      Both foundPasses
        (Both (And.right (List.memRangeFrom found count 0 member)) (earlier before =>
          List.findRangeFirst passes count 0 found h earlier (Nat.zeroLe earlier) before))

--| Finding nothing means no number in the range passes.
theorem List.findRangeNone ∀ (passes: Nat → Bool) (count: Nat)
    (h: (List.range 0 count).find passes = None) (n: Nat)
    (below: n < count):
    passes n = False :=
  match c: passes n with
    | True =>
      Void.impossible
        (List.findNoneNotMem (List.range 0 count) passes n c (List.memRangeFromIntro n count 0 (Nat.zeroLe n) below) h)
    | False => byComputing

test "List.findRangeSome" := List.range 0 10 |> .find (n => n * n > 20) == Some 5

-- `List.findIndex`: what the first index that passes is, in the form that
-- carries the induction, `findIndexFrom` (a cons step moves its start).

--| A step of [`List.findIndexFromSome`]: when `x` fails `p` and nothing in
--| `rest` from `start + 1` up to `index` passes, nothing in `[x, ..rest]`
--| from `start` up to `index` does.
theorem List.findIndexFromSomeBefore ∀ (p: a → Bool) (x: a) (rest: List a) (start index: Nat)
    (e: p x = False)
    (before: ∀ (earlier: Nat) => Succ start ≤ earlier
      → earlier < index
      → ∀ (y: a) => rest.get (earlier - Succ start) = Some y → p y = False):
    ∀ (earlier: Nat) => start ≤ earlier
      → earlier < index
      → ∀ (y: a) => [x, ..rest].get (earlier - start) = Some y → p y = False :=
  earlier lo2 hi y g =>
    match same: earlier == start with
      | True =>
        let zero: earlier - start = 0 := arithmetic [same]
        rewrite <- Option.someInjective (rewrite zero at g then g) then e
      | False =>
        let ne: earlier ≠ start := same.read
        let later: Succ start ≤ earlier := arithmetic
        let shift2: earlier - start = Succ (earlier - Succ start) := arithmetic
        before earlier later hi y (rewrite shift2 at g then g)

--| What `findIndexFrom` finds passes, and nothing before it does.
theorem List.findIndexFromSome ∀ (p: a → Bool) (start: Nat) (xs: List a) (index: Nat)
    (h: List.findIndexFrom start p xs = Some index):
    (start ≤ index)
      ∧ (∃ (x: a) => (xs.get (index - start) = Some x) ∧ (p x = True))
      ∧ (∀ (earlier: Nat) => start ≤ earlier
        → earlier < index
        → ∀ (y: a) => xs.get (earlier - start) = Some y → p y = False) :=
  match xs with
    | [x, ..rest] =>
      match e: p x with
        | True =>
          let isStart: start = index := Option.someInjective h
          let zero: index - start = 0 := arithmetic
          Both
            (Nat.leOfEq start index isStart)
            (Both (Witness x (rewrite zero then Both byComputing e)) (earlier lo hi y g =>
              let impossible: earlier < earlier := arithmetic
              Void.impossible (Nat.lessIrrefl earlier impossible)))
        | False =>
          let (Both lo (Both there before)) := List.findIndexFromSome p (Succ start) rest index h
          let shift: index - start = Succ (index - Succ start) := arithmetic
          let ok: start ≤ index := arithmetic
          Both ok
            (Both
              (Exists.elim there (w both => Witness w (Both (rewrite shift then both.left) both.right)))
              (List.findIndexFromSomeBefore p x rest start index e before))

--| What `findIndexFrom` does not find: no member passes.
theorem List.findIndexFromNone ∀ (p: a → Bool):
    ∀ (start: Nat) (xs: List a) => List.findIndexFrom start p xs = None → ∀ (x: a) => x ∈ xs → p x = False
  | start, [], h, x, member => member.impossible
  | start, [z, ..rest], h, x, member =>
    match e: p z with
      | False =>
        match member with
          | Inl isZ => rewrite <- isZ then e
          | Inr later => List.findIndexFromNone p (Succ start) rest h x later

--| The first index that passes is what `findIndexFrom` finds.
theorem List.findIndexFromOf ∀ (p: a → Bool) (start: Nat) (xs: List a) (index: Nat) (x: a)
    (lo: start ≤ index)
    (g: xs.get (index - start) = Some x)
    (passes: p x = True)
    (before: ∀ (earlier: Nat) => start ≤ earlier
      → earlier < index
      → ∀ (y: a) => xs.get (earlier - start) = Some y → p y = False):
    List.findIndexFrom start p xs = Some index :=
  match xs with
    | [z, ..rest] =>
      match e: p z with
        | True =>
          match same: index == start with
            | True => rewrite same.read
            | False =>
              let ne: index ≠ start := same.read
              let less: start < index := arithmetic
              let zero: start - start = 0 := arithmetic
              Void.impossible
                (Bool.falseNotTrue (Eq.trans (Eq.flipped (before start (Nat.leRefl start) less z (rewrite zero))) e))
        | False =>
          match same: index == start with
            | True =>
              let zero: index - start = 0 := arithmetic [same]
              let isZ: z = x := Option.someInjective (rewrite zero at g then g)
              Void.impossible (Bool.falseNotTrue (Eq.trans e.flipped (rewrite isZ then passes)))
            | False =>
              let ne: index ≠ start := same.read
              let later: Succ start ≤ index := arithmetic
              let shift: index - start = Succ (index - Succ start) := arithmetic
              List.findIndexFromOf p
                (Succ start)
                rest
                index
                x
                later
                (rewrite shift at g then g)
                passes
                (earlier lo2 hi y g2 =>
                  let shift2: earlier - start = Succ (earlier - Succ start) := arithmetic
                  before earlier
                    (Nat.leTrans start (Succ start) earlier (Nat.leSucc start) lo2)
                    hi
                    y
                    (rewrite shift2 then g2))

--| What `findIndex` finds passes, and nothing before it does.
theorem List.findIndexSome ∀ (xs: List a) (p: a → Bool) (index: Nat)
    (found: xs.findIndex p = Some index):
    (∃ (x: a) => (xs.get index = Some x) ∧ (p x = True))
      ∧ (∀ (earlier: Nat) => earlier < index → ∀ (y: a) => xs.get earlier = Some y → p y = False) :=
  let (Both lo (Both there before)) := List.findIndexFromSome p 0 xs index found
  let zero: index - 0 = index := arithmetic
  Both (rewrite zero at there then there) (earlier below y g =>
    let zero2: earlier - 0 = earlier := arithmetic
    before earlier (Nat.zeroLe earlier) below y (rewrite zero2 then g))

--| `findIndex` finds nothing only if no member passes.
theorem List.findIndexNone ∀ (xs: List a) (p: a → Bool)
    (found: xs.findIndex p = None) (x: a)
    (member: x ∈ xs):
    p x = False :=
  List.findIndexFromNone p 0 xs found x member

--| The first index that passes is what `findIndex` finds.
theorem List.findIndexOf ∀ (xs: List a) (p: a → Bool) (index: Nat) (x: a)
    (at: xs.get index = Some x)
    (passes: p x = True)
    (before: ∀ (earlier: Nat) => earlier < index → ∀ (y: a) => xs.get earlier = Some y → p y = False):
    xs.findIndex p = Some index :=
  let zero: index - 0 = index := arithmetic
  List.findIndexFromOf p 0 xs index x (Nat.zeroLe index) (rewrite zero then at) passes (earlier lo below y g =>
    let zero2: earlier - 0 = earlier := arithmetic
    before earlier below y (rewrite zero2 at g then g))

test "List.findIndexSome" :=
  let xs := [5, 6, 7, 8]
  xs.findIndex (x => Nat.leq 7 x) == Some 2 ∧ xs.get 2 == Some 7 ∧ xs.findIndex (x => Nat.leq 9 x) == None

-- `List.minimum`: the least of a list that holds `least` and nothing else
-- is `least`, an empty list has none, and what it finds is in the list and
-- at most each element.

--| Folding `Ord.min` from `least` over elements that are all `least`.
theorem List.foldMinAll ∀ [auto ord: Ord a] (least: a) (xs: List a)
    (all: ∀ (x: a) => x ∈ xs → x = least):
    List.foldLeft xs least Ord.min = least :=
  match xs with
    | [] => byComputing
    | [x, ..rest] =>
      rewrite all x (Inl byComputing), Ord.minSelf least then
        List.foldMinAll least rest (y member => all y (Inr member))

theorem List.minimumAllEqual ∀ [auto ord: Ord a] (least: a) (xs: List a)
    (member: least ∈ xs)
    (all: ∀ (x: a) => x ∈ xs → x = least):
    List.minimum xs = Some least :=
  match xs with
    | [x, ..rest] =>
      rewrite all x (Inl byComputing) then Eq.cong Some (List.foldMinAll least rest (y member => all y (Inr member)))

theorem List.minimumEmpty ∀ [auto ord: Ord a] (xs: List a) (none: ∀ (x: a) => x ∈ xs → Void): List.minimum xs = None :=
  match xs with
    | [] => byComputing
    | [x, ..rest] => Void.impossible (none x (Inl byComputing))

--| Folding with `Ord.min` gives at most the start and each element, and
--| gives the start or an element.
theorem List.foldMinLeStart ∀ [auto ord: Ord a] (xs: List a) (start: a): List.foldLeft xs start Ord.min <= start :=
  match xs with
    | [] => Ord.leRefl start
    | [y, ..ys] =>
      Ord.leTrans
        (List.foldLeft ys (Ord.min start y) Ord.min)
        (Ord.min start y)
        start
        (List.foldMinLeStart ys (Ord.min start y))
        (Ord.minLeLeft start y)

theorem List.foldMinLeMember ∀ [auto ord: Ord a] (xs: List a) (start x: a)
    (h: x ∈ xs):
    List.foldLeft xs start Ord.min <= x :=
  match xs, h with
    | [], member => member.impossible
    | [y, ..ys], Inl same =>
      rewrite Eq.flipped same then
        Ord.leTrans
          (List.foldLeft ys (Ord.min start y) Ord.min)
          (Ord.min start y)
          y
          (List.foldMinLeStart ys (Ord.min start y))
          (Ord.minLeRight start y)
    | [y, ..ys], Inr member => List.foldMinLeMember ys (Ord.min start y) x member

theorem List.foldMinMember ∀ [auto ord: Ord a] (xs: List a) (start: a):
    (List.foldLeft xs start Ord.min = start) ∨ (List.foldLeft xs start Ord.min ∈ xs) :=
  match xs with
    | [] => Inl byComputing
    | [y, ..ys] =>
      match List.foldMinMember ys (Ord.min start y) with
        | Inr member => Inr (Inr member)
        | Inl same =>
          match Ord.minEither start y with
            | Inl isStart => Inl (Eq.trans same isStart)
            | Inr isY => Inr (Inl (Eq.trans same isY).flipped)

--| The least element is in the list and at most every element.
theorem List.minimumSome ∀ [auto ord: Ord a] (xs: List a) (least: a)
    (found: List.minimum xs = Some least):
    (least ∈ xs) ∧ (∀ (x: a) => x ∈ xs → least <= x) :=
  match xs with
    | [y, ..ys] =>
      let same := Option.someInjective found
      Both
        (match List.foldMinMember ys y with
          | Inl isY => Inl (Eq.trans same.flipped isY).flipped
          | Inr member => Inr (rewrite same at member))
        (x member =>
          rewrite Eq.flipped same then
            match member with
              | Inl isY => rewrite Eq.flipped isY then List.foldMinLeStart ys y
              | Inr inRest => List.foldMinLeMember ys y x inRest)

--| A list with an element has a least one.
theorem List.minimumExists ∀ [auto ord: Ord a] (xs: List a) (x: a)
    (member: x ∈ xs):
    ∃ (least: a) => List.minimum xs = Some least :=
  match xs with | [y, ..ys] => Witness (List.foldLeft ys y Ord.min) byComputing

--| A list with an element has a least one: `List.minimum` isn't `None`.
theorem List.minimumNone ∀ [auto ord: Ord a] (xs: List a)
    (none: List.minimum xs = None) (x: a)
    (member: x ∈ xs):
    Void :=
  match xs with | [y, ..ys] => Option.someNotNone (List.foldLeft ys y Ord.min) none

--| Lists with the same members have the same least member.
theorem List.minimumSameMembers ∀ [auto ord: Ord a] (xs ys: List a)
    (into: ∀ (v: a) => v ∈ xs → v ∈ ys)
    (back: ∀ (v: a) => v ∈ ys → v ∈ xs):
    List.minimum xs = List.minimum ys :=
  match mx: List.minimum xs with
    | None =>
      match my: List.minimum ys with
        | None => byComputing
        | Some y => Void.impossible (List.minimumNone xs mx y (back y (List.minimumSome ys y my).left))
    | Some x =>
      match my: List.minimum ys with
        | None => Void.impossible (List.minimumNone ys my x (into x (List.minimumSome xs x mx).left))
        | Some y =>
          let (Both xIn xLeast) := List.minimumSome xs x mx
          let (Both yIn yLeast) := List.minimumSome ys y my
          Eq.cong Some (Ord.leAntisymm x y (xLeast y (back y yIn)) (yLeast x (into x xIn)))

-- `List.minBy`: the result is a member, its key is at most every member's,
-- and no member before it has a key as small (the first of the smallest wins).

--| Folding with `List.minByStep` gives a key at most the start's, and the
--| start or a member.
theorem List.foldMinByLeStart ∀ [auto ord: Ord b] (f: a → b) (xs: List a) (start: a):
    f (List.foldLeft xs start (List.minByStep f)) <= f start :=
  match xs with
    | [] => Ord.leRefl (f start)
    | [y, ..ys] =>
      match order: Ord.compare (f start) (f y) with
        | Greater =>
          let flipped: Ord.compare (f y) (f start) = Less := rewrite order at ord.flip (f start) (f y)
          Ord.leTrans
            (f (List.foldLeft ys y (List.minByStep f)))
            (f y)
            (f start)
            (List.foldMinByLeStart f ys y)
            (Ord.lessLe (f y) (f start) (ord.lessThanOf (f y) (f start) flipped))
        | Less => List.foldMinByLeStart f ys start
        | Equal => List.foldMinByLeStart f ys start

--| Folding with `List.minByStep` gives a key at most each member's.
theorem List.foldMinByLeMember ∀ [auto ord: Ord b] (f: a → b) (xs: List a) (start x: a)
    (h: x ∈ xs):
    f (List.foldLeft xs start (List.minByStep f)) <= f x :=
  match xs, h with
    | [], member => member.impossible
    | [y, ..ys], Inl same =>
      rewrite Eq.flipped same then
        match order: Ord.compare (f start) (f y) with
          | Greater => List.foldMinByLeStart f ys y
          | Less =>
            Ord.leTrans
              (f (List.foldLeft ys start (List.minByStep f)))
              (f start)
              (f y)
              (List.foldMinByLeStart f ys start)
              (ord.lessEqOf (f start) (f y) (greater => Ordering.lessNotGreater (Eq.trans order.flipped greater)))
          | Equal =>
            Ord.leTrans
              (f (List.foldLeft ys start (List.minByStep f)))
              (f start)
              (f y)
              (List.foldMinByLeStart f ys start)
              (ord.lessEqOf (f start) (f y) (greater => Ordering.equalNotGreater (Eq.trans order.flipped greater)))
    | [y, ..ys], Inr member =>
      match order: Ord.compare (f start) (f y) with
        | Greater => List.foldMinByLeMember f ys y x member
        | Less => List.foldMinByLeMember f ys start x member
        | Equal => List.foldMinByLeMember f ys start x member

--| Folding with `List.minByStep` gives the start or a member.
theorem List.foldMinByMember ∀ [auto ord: Ord b] (f: a → b) (xs: List a) (start: a):
    (List.foldLeft xs start (List.minByStep f) = start) ∨ (List.foldLeft xs start (List.minByStep f) ∈ xs) :=
  match xs with
    | [] => Inl byComputing
    | [y, ..ys] =>
      match order: Ord.compare (f start) (f y) with
        | Greater =>
          match List.foldMinByMember f ys y with
            | Inl same => Inr (Inl same.flipped)
            | Inr member => Inr (Inr member)
        | Less =>
          match List.foldMinByMember f ys start with
            | Inl same => Inl same
            | Inr member => Inr (Inr member)
        | Equal =>
          match List.foldMinByMember f ys start with
            | Inl same => Inl same
            | Inr member => Inr (Inr member)

--| The case of [`List.foldMinByFirst`] where the start is kept over `y`: given
--| the split for `start :: ys`, which leaves `y` out, `y` goes after the start.
theorem List.foldMinByFirstKeep ∀ [auto ord: Ord b] (f: a → b) (ys: List a) (start y: a)
    (kept: f start <= f y)
    (split: ∃ (before: List a) => ∃ (after: List a) => ([start, ..ys]
      = before ++ [List.foldLeft ys start (List.minByStep f), ..after])
      ∧ (∀ (z: a) => z ∈ before → f (List.foldLeft ys start (List.minByStep f)) < f z)):
    ∃ (before: List a) => ∃ (after: List a) => ([start, y, ..ys]
      = before ++ [List.foldLeft ys start (List.minByStep f), ..after])
      ∧ (∀ (z: a) => z ∈ before → f (List.foldLeft ys start (List.minByStep f)) < f z) :=
  match split with
    | Witness [] (Witness after (Both same earlier)) =>
      let isStart: start = List.foldLeft ys start (List.minByStep f) := List.consInjectiveHead start _ ys after same
      Witness [] (Witness [y, ..ys] (Both (rewrite <- isStart) (z member => member.impossible)))
    | Witness [c, ..before] (Witness after (Both same earlier)) =>
      let isStart: start = c :=
        List.consInjectiveHead start c ys (before ++ [List.foldLeft ys start (List.minByStep f), ..after]) same
      let rest: ys = before ++ [List.foldLeft ys start (List.minByStep f), ..after] := Eq.cong (.drop 1) same
      let belowStart: f (List.foldLeft ys start (List.minByStep f)) < f start :=
        rewrite <- isStart at (earlier c (Inl byComputing))
      Witness
        [start, y, ..before]
        (Witness after
          (Both (Eq.cong (t => [start, y, ..t]) rest) (z member =>
            match member with
              | Inl same => rewrite <- same then belowStart
              | Inr (Inl same) =>
                rewrite <- same then
                  Ord.lessLeTrans (f (List.foldLeft ys start (List.minByStep f))) (f start) (f y) belowStart kept
              | Inr (Inr inBefore) => earlier z (Inr inBefore))))

--| The result of folding with `List.minByStep` from `start` over `xs` is the
--| first element of `start :: xs` whose key is the smallest: the list splits
--| around it, and every element before it has a strictly larger key.
theorem List.foldMinByFirst ∀ [auto ord: Ord b] (f: a → b) (xs: List a) (start: a):
    ∃ (before: List a) => ∃ (after: List a) => ([start, ..xs]
      = before ++ [List.foldLeft xs start (List.minByStep f), ..after])
      ∧ (∀ (y: a) => y ∈ before → f (List.foldLeft xs start (List.minByStep f)) < f y) :=
  match xs with
    | [] => Witness [] (Witness [] (Both byComputing (y member => member.impossible)))
    | [y, ..ys] =>
      match order: Ord.compare (f start) (f y) with
        | Greater =>
          let flipped: Ord.compare (f y) (f start) = Less := rewrite order at ord.flip (f start) (f y)
          let startAbove: f y < f start := ord.lessThanOf (f y) (f start) flipped
          match List.foldMinByFirst f ys y with
            | Witness before (Witness after (Both split earlier)) =>
              -- Bound here, not written inline: the inline lambda is checked inside
              -- three constructor arguments, which a debug build's stack budget
              -- doesn't allow.
              let below: ∀ (z: a) => z ∈ [start, ..before] → f (List.foldLeft ys y (List.minByStep f)) < f z :=
                z member =>
                  match member with
                    | Inl same =>
                      rewrite <- same then
                        Ord.leLessTrans
                          (f (List.foldLeft ys y (List.minByStep f)))
                          (f y)
                          (f start)
                          (List.foldMinByLeStart f ys y)
                          startAbove
                    | Inr inBefore => earlier z inBefore
              Witness [start, ..before] (Witness after (Both (rewrite split) below))
        | Less =>
          List.foldMinByFirstKeep f ys start y
            (ord.lessEqOf (f start) (f y) (greater => Ordering.lessNotGreater (Eq.trans order.flipped greater)))
            (List.foldMinByFirst f ys start)
        | Equal =>
          List.foldMinByFirstKeep f ys start y
            (ord.lessEqOf (f start) (f y) (greater => Ordering.equalNotGreater (Eq.trans order.flipped greater)))
            (List.foldMinByFirst f ys start)

--| `List.minBy` finds a member, and its key is at most every member's.
theorem List.minBySome ∀ [auto ord: Ord b] (xs: List a) (f: a → b) (least: a)
    (found: List.minBy xs f = Some least):
    (least ∈ xs) ∧ (∀ (x: a) => x ∈ xs → f least <= f x) :=
  match xs with
    | [y, ..ys] =>
      let same := Option.someInjective found
      Both
        (match List.foldMinByMember f ys y with
          | Inl isY => Inl (Eq.trans same.flipped isY).flipped
          | Inr member => Inr (rewrite same at member))
        (x member =>
          rewrite Eq.flipped same then
            match member with
              | Inl isY => rewrite Eq.flipped isY then List.foldMinByLeStart f ys y
              | Inr inRest => List.foldMinByLeMember f ys y x inRest)

--| `minBy` finds nothing only in an empty list.
theorem List.minByNone ∀ [auto ord: Ord b] (xs: List a) (f: a → b) (found: List.minBy xs f = None): xs = [] :=
  match xs with | [] => byComputing

--| `List.minBy` finds the FIRST element with the smallest key: the list
--| splits around the result, and every element before it has a strictly
--| larger key.
theorem List.minByFirst ∀ [auto ord: Ord b] (xs: List a) (f: a → b) (least: a)
    (found: List.minBy xs f = Some least):
    ∃ (before: List a) => ∃ (after: List a) => (xs = before ++ [least, ..after])
      ∧ (∀ (x: a) => x ∈ before → f least < f x) :=
  match xs with | [y, ..ys] => rewrite <- Option.someInjective found then List.foldMinByFirst f ys y

-- `List.maximum`, as for `List.minimum` above: the greatest of a list that
-- holds `most` and nothing else is `most`, an empty list has none, and what
-- it finds is in the list and at least each element. (`List.foldMaxGe`,
-- `List.leFoldMax` and `List.foldMaxMem` below are about folds of
-- `Nat.max`; these are about `Ord.max`, which `List.maximum` folds.)

--| Folding `Ord.max` from `most` over elements that are all `most`.
theorem List.foldMaxAll ∀ [auto ord: Ord a] (most: a) (xs: List a)
    (all: ∀ (x: a) => x ∈ xs → x = most):
    List.foldLeft xs most Ord.max = most :=
  match xs with
    | [] => byComputing
    | [x, ..rest] =>
      rewrite all x (Inl byComputing), Ord.maxSelf most then List.foldMaxAll most rest (y member => all y (Inr member))

theorem List.maximumAllEqual ∀ [auto ord: Ord a] (most: a) (xs: List a)
    (member: most ∈ xs)
    (all: ∀ (x: a) => x ∈ xs → x = most):
    List.maximum xs = Some most :=
  match xs with
    | [x, ..rest] =>
      rewrite all x (Inl byComputing) then Eq.cong Some (List.foldMaxAll most rest (y member => all y (Inr member)))

theorem List.maximumEmpty ∀ [auto ord: Ord a] (xs: List a) (none: ∀ (x: a) => x ∈ xs → Void): List.maximum xs = None :=
  match xs with
    | [] => byComputing
    | [x, ..rest] => Void.impossible (none x (Inl byComputing))

--| Folding with `Ord.max` gives at least the start and each element, and
--| gives the start or an element.
theorem List.foldMaxGeStart ∀ [auto ord: Ord a] (xs: List a) (start: a): start <= List.foldLeft xs start Ord.max :=
  match xs with
    | [] => Ord.leRefl start
    | [y, ..ys] =>
      Ord.leTrans start
        (Ord.max start y)
        (List.foldLeft ys (Ord.max start y) Ord.max)
        (Ord.leMaxLeft start y)
        (List.foldMaxGeStart ys (Ord.max start y))

theorem List.foldMaxGeMember ∀ [auto ord: Ord a] (xs: List a) (start x: a)
    (h: x ∈ xs):
    x <= List.foldLeft xs start Ord.max :=
  match xs, h with
    | [], member => member.impossible
    | [y, ..ys], Inl same =>
      rewrite Eq.flipped same then
        Ord.leTrans y
          (Ord.max start y)
          (List.foldLeft ys (Ord.max start y) Ord.max)
          (Ord.leMaxRight start y)
          (List.foldMaxGeStart ys (Ord.max start y))
    | [y, ..ys], Inr member => List.foldMaxGeMember ys (Ord.max start y) x member

theorem List.foldMaxMember ∀ [auto ord: Ord a] (xs: List a) (start: a):
    (List.foldLeft xs start Ord.max = start) ∨ (List.foldLeft xs start Ord.max ∈ xs) :=
  match xs with
    | [] => Inl byComputing
    | [y, ..ys] =>
      match List.foldMaxMember ys (Ord.max start y) with
        | Inr member => Inr (Inr member)
        | Inl same =>
          match Ord.maxEither start y with
            | Inl isStart => Inl (Eq.trans same isStart)
            | Inr isY => Inr (Inl (Eq.trans same isY).flipped)

--| The greatest element is in the list and at least every element.
theorem List.maximumSome ∀ [auto ord: Ord a] (xs: List a) (most: a)
    (found: List.maximum xs = Some most):
    (most ∈ xs) ∧ (∀ (x: a) => x ∈ xs → x <= most) :=
  match xs with
    | [y, ..ys] =>
      let same := Option.someInjective found
      Both
        (match List.foldMaxMember ys y with
          | Inl isY => Inl (Eq.trans same.flipped isY).flipped
          | Inr member => Inr (rewrite same at member))
        (x member =>
          rewrite Eq.flipped same then
            match member with
              | Inl isY => rewrite Eq.flipped isY then List.foldMaxGeStart ys y
              | Inr inRest => List.foldMaxGeMember ys y x inRest)

--| A list with an element has a greatest one: it isn't `None`.
theorem List.maximumExists ∀ [auto ord: Ord a] (xs: List a) (x: a)
    (member: x ∈ xs):
    ∃ (most: a) => List.maximum xs = Some most :=
  match xs with | [y, ..ys] => Witness (List.foldLeft ys y Ord.max) byComputing

theorem List.maximumNone ∀ [auto ord: Ord a] (xs: List a)
    (none: List.maximum xs = None) (x: a)
    (member: x ∈ xs):
    Void :=
  match xs with | [y, ..ys] => Option.someNotNone (List.foldLeft ys y Ord.max) none

--| Lists with the same members have the same greatest member.
theorem List.maximumSameMembers ∀ [auto ord: Ord a] (xs ys: List a)
    (into: ∀ (v: a) => v ∈ xs → v ∈ ys)
    (back: ∀ (v: a) => v ∈ ys → v ∈ xs):
    List.maximum xs = List.maximum ys :=
  match mx: List.maximum xs with
    | None =>
      match my: List.maximum ys with
        | None => byComputing
        | Some y => Void.impossible (List.maximumNone xs mx y (back y (List.maximumSome ys y my).left))
    | Some x =>
      match my: List.maximum ys with
        | None => Void.impossible (List.maximumNone ys my x (into x (List.maximumSome xs x mx).left))
        | Some y =>
          let (Both xIn xMost) := List.maximumSome xs x mx
          let (Both yIn yMost) := List.maximumSome ys y my
          Eq.cong Some (Ord.leAntisymm x y (yMost x (into x xIn)) (xMost y (back y yIn)))

test "List.maximum and List.minimum" :=
  List.maximum [3, 9, 2] == Some 9 ∧ List.minimum [3, 9, 2] == Some 2 ∧ List.maximum ([]: List Nat) == None

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
        | True =>
          rewrite List.occurrencesFilter xs keep p then
            match p x with
              | True => byComputing
              | False => byComputing
        | False =>
          rewrite List.occurrencesFilter xs keep p then
            match p x with
              | True => byComputing
              | False => byComputing

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

--| Running results: one more than the elements, the start first.
theorem List.lengthScanLeft ∀ (xs: List a) (start: b) (f: b → a → b):
    List.length (List.scanLeft xs start f) = Succ (List.length xs) :=
  match xs with
    | [] => byComputing
    | [x, ..xs] => Eq.cong Succ (List.lengthScanLeft xs (f start x) f)

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

--| What passes the test is kept.
theorem List.memFilterIntro ∀ (xs: List a) (p: a → Bool) [v: a] (h1: v ∈ xs) (h: p v = True): v ∈ List.filter xs p :=
  match xs, h1 with
    | [], m => m
    | [x, ..xs], Inl e => rewrite <- e at h then (rewrite h then Inl e)
    | [x, ..xs], Inr m =>
      match e: p x with
        | True => Inr (List.memFilterIntro xs p m h)
        | False => List.memFilterIntro xs p m h

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
  | [] => byComputing
  | [y] => byComputing
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
      | None => arithmetic
      | Some y => arithmetic

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

--| The first step, for induction, of running accumulations beside the elements, by computation.
--| `List.zipWith xs (List.scanLeft xs z f) g` is `g` of each element and the fold of the
--| elements before it ([`List.getOrZipWithScanLeft`], std/List/Index.sw). It
--| lays items end to end from `z`, say, with `f` adding an item's size and
--| `g` placing it.
theorem List.zipWithScanLeftCons ∀ (x: a) (xs: List a) (z: b) (f: b → a → b) (g: a → b → c):
    List.zipWith [x, ..xs] (List.scanLeft [x, ..xs] z f) g
      = [g x z, ..List.zipWith xs (List.scanLeft xs (f z x) f) g] :=
  byComputing

theorem List.zipWithScanLeftExample: List.zipWith
      [2, 3, 4]
      (List.scanLeft [2, 3, 4] 10 (offset width => offset + width))
      (width offset => (offset, width))
      = [(10, 2), (12, 3), (15, 4)] :=
  byComputing

--| Running accumulations beside the elements have one for each element.
theorem List.lengthZipWithScanLeft ∀ (f: b → a → b) (g: a → b → c) (xs: List a) (z: b):
    List.length (List.zipWith xs (List.scanLeft xs z f) g) = List.length xs :=
  match xs with
    | [] => byComputing
    | [x, ..xs] => Eq.cong Succ (List.lengthZipWithScanLeft f g xs (f z x))

--| What `g` keeps of an element (`h`, an id say) doesn't depend on the other
--| list, so mapping it over the zip is mapping over the first list.
theorem List.mapZipWithLeft ∀ (h: c → d) (k: a → d) (g: a → b → c)
    (same: ∀ (x: a) (y: b) => h (g x y) = k x)
    (xs: List a) (ys: List b)
    (le: List.length xs ≤ List.length ys):
    List.map (List.zipWith xs ys g) h = List.map xs k :=
  match xs, ys with
    | [], ys => byComputing
    | [x, ..xs], [y, ..ys] => rewrite same x y, List.mapZipWithLeft h k g same xs ys le

theorem List.mapZipWithScanLeft ∀ (h: c → d) (k: a → d) (g: a → b → c)
    (same: ∀ (x: a) (y: b) => h (g x y) = k x)
    (xs: List a) (z: b) (f: b → a → b):
    List.map (List.zipWith xs (List.scanLeft xs z f) g) h = List.map xs k :=
  List.mapZipWithLeft h k g same xs
    (List.scanLeft xs z f)
    (rewrite List.lengthScanLeft xs z f then Nat.leSucc (List.length xs))

--| `mapAccumLeft` is a fold for its final state, and for its list the zip of
--| the elements with the running states.
theorem List.mapAccumLeftGoSpec ∀ (f: s → a → Pair s b) (xs: List a) (state: s) (done: List b):
    List.mapAccumLeftGo f state done xs
      = MkPair
        (List.foldLeft xs state (st x => Pair.fst (f st x)))
        (List.reverseOnto done
          (List.zipWith xs (List.scanLeft xs state (st x => Pair.fst (f st x))) (x st => Pair.snd (f st x)))) :=
  match xs with
    | [] => byComputing
    | [x, ..xs] => List.mapAccumLeftGoSpec f xs (Pair.fst (f state x)) [Pair.snd (f state x), ..done]

theorem List.mapAccumLeftState ∀ (xs: List a) (initial: s) (f: s → a → Pair s b):
    Pair.fst (List.mapAccumLeft xs initial f) = List.foldLeft xs initial (st x => Pair.fst (f st x)) :=
  Eq.cong Pair.fst (List.mapAccumLeftGoSpec f xs initial [])

theorem List.mapAccumLeftList ∀ (xs: List a) (initial: s) (f: s → a → Pair s b):
    Pair.snd (List.mapAccumLeft xs initial f)
      = List.zipWith xs (List.scanLeft xs initial (st x => Pair.fst (f st x))) (x st => Pair.snd (f st x)) :=
  Eq.cong Pair.snd (List.mapAccumLeftGoSpec f xs initial [])

theorem List.lengthMapAccumLeft ∀ (xs: List a) (initial: s) (f: s → a → Pair s b):
    List.length (Pair.snd (List.mapAccumLeft xs initial f)) = List.length xs :=
  rewrite List.mapAccumLeftList xs initial f then
    List.lengthZipWithScanLeft (st x => Pair.fst (f st x)) (x st => Pair.snd (f st x)) xs initial

theorem List.mapAccumLeftExample: List.mapAccumLeft [1, 2, 3] 0 (sum x => MkPair (sum + x) sum) = MkPair 6 [0, 1, 3] :=
  byComputing

-- `List.get`, the element at an index if there is one: it is `Some` exactly
-- within the list, what it finds is an element, and it goes through `map`,
-- `zipWith`, `append` and `take`. (`List.getOrGet`, std/List/Index.sw, is
-- `List.getOr` from it.)

--| `get` finds something exactly when the index is within the list.
theorem List.isSomeGet ∀ (xs: List a) (k: Nat): Option.isSome (List.get xs k) = Nat.leq (Succ k) (List.length xs) :=
  match xs, k with
    | [], k => byComputing
    | [x, ..xs], Zero => byComputing
    | [x, ..xs], Succ k => List.isSomeGet xs k

theorem List.getInRange ∀ (xs: List a) (k: Nat): k < List.length xs ↔ Option.isSome (List.get xs k) = True :=
  { forward = h => Eq.trans (List.isSomeGet xs k) h, backward = h => Eq.trans (List.isSomeGet xs k).flipped h }

--| Past the end, `get` finds nothing.
theorem List.getPast ∀ (xs: List a) (k: Nat) (h: List.length xs ≤ k): List.get xs k = None := match xs, k with
  | [], k => byComputing
  | [x, ..xs], Succ k => List.getPast xs k h

--| An index where `get` finds something is inside the list; the converse is
--| [`List.getInRange`].
theorem List.getSomeLt ∀ (xs: List a) (i: Nat) (x: a) (found: List.get xs i = Some x): i < List.length xs :=
  match xs, i, x with
    | [x, ..xs], Zero, y => arithmetic
    | [x, ..xs], Succ i, y => arithmetic [List.getSomeLt xs i y found]

--| What `get` finds is an element of the list.
theorem List.memOfGet ∀ (xs: List a) (k: Nat) (v: a) (h: List.get xs k = Some v): v ∈ xs := match xs, k with
  | [x, ..xs], Zero => Inl (Option.someInjective h)
  | [x, ..xs], Succ k => Inr (List.memOfGet xs k v h)

--| Setting an element keeps the length, whether or not the index is inside.
theorem List.lengthSet ∀ (xs: List a) (i: Nat) (v: a): List.length (List.set xs i v) = List.length xs :=
  match xs, i with
    | [], i => byComputing
    | [x, ..xs], Zero => byComputing
    | [x, ..xs], Succ i => Eq.cong Succ (List.lengthSet xs i v)

--| Inside the list, `get` after a `set` finds the new value.
theorem List.getSet ∀ (xs: List a) (i: Nat) (v: a) (below: i < List.length xs): List.get (List.set xs i v) i = Some v :=
  match xs, i with
    | [x, ..xs], Zero => byComputing
    | [x, ..xs], Succ i => List.getSet xs i v (arithmetic)

--| At another index, `set` changes nothing `get` finds there; past the end
--| both finds nothing.
theorem List.getSetOther ∀ (xs: List a) (i: Nat) (v: a) (j: Nat)
    (differ: j ≠ i):
    List.get (List.set xs i v) j = List.get xs j :=
  match xs, i, j with
    | [], i, j => byComputing
    | [x, ..xs], Zero, Zero => (differ byComputing).impossible
    | [x, ..xs], Zero, Succ j => byComputing
    | [x, ..xs], Succ i, Zero => byComputing
    | [x, ..xs], Succ i, Succ j => List.getSetOther xs i v j (same => differ (Eq.cong Succ same))

theorem List.getMap ∀ (xs: List a) (f: a → b) (k: Nat): List.get (List.map xs f) k = Option.map (List.get xs k) f :=
  match xs, k with
    | [], k => byComputing
    | [x, ..xs], Zero => byComputing
    | [x, ..xs], Succ k => List.getMap xs f k

--| `withIndexFrom` is as long as the list; element k is the
--| list's element k with k (counted from `start`).
theorem List.lengthWithIndexFrom ∀ (start: Nat) (xs: List a):
    List.length (List.withIndexFrom start xs) = List.length xs :=
  match xs with
    | [] => byComputing
    | [x, ..xs] => Eq.cong Succ (List.lengthWithIndexFrom (Succ start) xs)

theorem List.lengthWithIndex ∀ (xs: List a): List.length (List.withIndex xs) = List.length xs :=
  List.lengthWithIndexFrom 0 xs

theorem List.getWithIndexFrom ∀ (start: Nat) (xs: List a) (k: Nat):
    List.get (List.withIndexFrom start xs) k = Option.map (List.get xs k) (x => MkPair (start + k) x) :=
  match xs, k with
    | [], k => byComputing
    | [x, ..xs], Zero => rewrite Nat.addZero start
    | [x, ..xs], Succ k => rewrite Nat.addSucc start k then List.getWithIndexFrom (Succ start) xs k

theorem List.getWithIndex ∀ (xs: List a) (k: Nat):
    List.get (List.withIndex xs) k = Option.map (List.get xs k) (x => MkPair k x) :=
  List.getWithIndexFrom 0 xs k

--| `mapWithIndex` keeps the length, and element k is `f k` of the list's
--| element k.
theorem List.lengthMapWithIndex ∀ (xs: List a) (f: Nat → a → b):
    List.length (List.mapWithIndex xs f) = List.length xs :=
  Eq.trans (List.lengthMap (List.withIndex xs) (pair => f pair.fst pair.snd)) (List.lengthWithIndex xs)

theorem List.getMapWithIndex ∀ (xs: List a) (f: Nat → a → b) (k: Nat):
    List.get (List.mapWithIndex xs f) k = Option.map (List.get xs k) (f k) :=
  let mapped: List.get (List.mapWithIndex xs f) k
    = Option.map (Option.map (List.get xs k) (x => MkPair k x)) (pair => f pair.fst pair.snd) :=
    rewrite <- List.getWithIndex xs k then List.getMap (List.withIndex xs) (pair => f pair.fst pair.snd) k
  rewrite mapped then
    match List.get xs k with
      | None => byComputing
      | Some x => byComputing

--| `zipWith` has `f x y` where both lists have an element, `x` and `y`.
theorem List.getZipWith ∀ (f: a → b → c) (xs: List a) (ys: List b) (k: Nat):
    List.get (List.zipWith xs ys f) k = Option.flatMap (List.get xs k) (x => Option.map (List.get ys k) (f x)) :=
  match xs, ys, k with
    | [], ys, k => byComputing
    | [x, ..xs], [], Zero => byComputing
    | [x, ..xs], [], Succ k =>
      match c: List.get xs k with
        | None => byComputing
        | Some u => byComputing
    | [x, ..xs], [y, ..ys], Zero => byComputing
    | [x, ..xs], [y, ..ys], Succ k => List.getZipWith f xs ys k

--| `zip`, `zipWith3` and `zipWith4` have the combined elements where every
--| list has one.
theorem List.getZip ∀ (xs: List a) (ys: List b) (k: Nat):
    List.get (List.zip xs ys) k = Option.map2 MkPair (List.get xs k) (List.get ys k) :=
  match xs, ys, k with
    | [], ys, k => byComputing
    | [x, ..xs], [], k => (Option.map2None MkPair _).flipped
    | [x, ..xs], [y, ..ys], Zero => byComputing
    | [x, ..xs], [y, ..ys], Succ k => List.getZip xs ys k

theorem List.getZipWith3 ∀ (f: a → b → c → d) (xs: List a) (ys: List b) (zs: List c) (k: Nat):
    List.get (List.zipWith3 xs ys zs f) k = Option.map3 f (List.get xs k) (List.get ys k) (List.get zs k) :=
  match xs, ys, zs, k with
    | [], ys, zs, k => byComputing
    | [x, ..xs], [], zs, k => (Option.map3None2 f _ _).flipped
    | [x, ..xs], [y, ..ys], [], k => (Option.map3None3 f _ _).flipped
    | [x, ..xs], [y, ..ys], [z, ..zs], Zero => byComputing
    | [x, ..xs], [y, ..ys], [z, ..zs], Succ k => List.getZipWith3 f xs ys zs k

theorem List.getZipWith4 ∀ (f: a → b → c → d → e) (xs: List a) (ys: List b) (zs: List c) (ws: List d) (k: Nat):
    List.get (List.zipWith4 xs ys zs ws f) k
      = Option.map4 f (List.get xs k) (List.get ys k) (List.get zs k) (List.get ws k) :=
  match xs, ys, zs, ws, k with
    | [], ys, zs, ws, k => byComputing
    | [x, ..xs], [], zs, ws, k => (Option.map4None2 f _ _ _).flipped
    | [x, ..xs], [y, ..ys], [], ws, k => (Option.map4None3 f _ _ _).flipped
    | [x, ..xs], [y, ..ys], [z, ..zs], [], k => (Option.map4None4 f _ _ _).flipped
    | [x, ..xs], [y, ..ys], [z, ..zs], [w, ..ws], Zero => byComputing
    | [x, ..xs], [y, ..ys], [z, ..zs], [w, ..ws], Succ k => List.getZipWith4 f xs ys zs ws k

theorem List.getZipWith3Example: List.get (List.zipWith3 [1, 2] [10, 20, 30] [100, 200] (x y z => x + y + z)) 1
      = Some 222 :=
  byComputing

--| `append`: the first list's element, else the second's, counting on from
--| the end of the first.
theorem List.getAppend ∀ (xs ys: List a) (k: Nat):
    List.get (List.append xs ys) k = Option.orElse (List.get xs k) (List.get ys (k - List.length xs)) :=
  match xs, k with
    | [], k => byComputing
    | [x, ..xs], Zero => byComputing
    | [x, ..xs], Succ k => List.getAppend xs ys k

theorem List.getAppendLeft ∀ (xs ys: List a) (k: Nat)
    (h: k < List.length xs):
    List.get (List.append xs ys) k = List.get xs k :=
  match xs, k with
    | [x, ..xs], Zero => byComputing
    | [x, ..xs], Succ k => List.getAppendLeft xs ys k h

theorem List.getAppendRight ∀ (xs ys: List a) (k: Nat)
    (h: List.length xs ≤ k):
    List.get (List.append xs ys) k = List.get ys (k - List.length xs) :=
  match xs, k with
    | [], k => byComputing
    | [x, ..xs], Succ k => List.getAppendRight xs ys k h

--| `take n` keeps the elements before `n`, and nothing from `n` on.
theorem List.getTake ∀ (xs: List a) (n k: Nat) (h: k < n): List.get (List.take xs n) k = List.get xs k :=
  match xs, n, k with
    | [], Succ n, k => byComputing
    | [x, ..xs], Succ n, Zero => byComputing
    | [x, ..xs], Succ n, Succ k => List.getTake xs n k h

theorem List.getTakePast ∀ (xs: List a) (n k: Nat) (h: n ≤ k): List.get (List.take xs n) k = None := match xs, n, k with
  | xs, Zero, k => byComputing
  | [], Succ n, k => byComputing
  | [x, ..xs], Succ n, Succ k => List.getTakePast xs n k h

--| Index j after dropping k is index k + j before.
theorem List.getDrop ∀ (xs: List a) (k j: Nat): List.get (List.drop xs k) j = List.get xs (k + j) := match xs, k with
  | xs, Zero => byComputing
  | [], Succ k => byComputing
  | [x, ..xs], Succ k => List.getDrop xs k j

--| What `List.transposeN`'s columns are: column i holds element i of every
--| row that has one. From column `p` on, for the rows with their first `p`
--| elements dropped (`transposeN`'s own loop):
theorem List.transposeNColumnsFrom ∀ (rows: List (List a)) (k p: Nat):
    List.transposeN k (List.map rows (row => List.drop row p))
      = List.map (List.rangeFrom k p) (i => List.filterMap rows (row => List.get row i)) :=
  match k with
    | Zero => byComputing
    | Succ k =>
      rewrite List.filterMapMap rows (x => List.get x 0) (row => List.drop row p),
          List.mapMap rows (x => List.drop x 1) (row => List.drop row p),
          List.getDrop _ p 0,
          Nat.addZero p,
          <- List.dropAdd p 1 then
        Eq.cong
          (later => [List.filterMap rows (row => List.get row p), ..later])
          (List.transposeNColumnsFrom rows k (p + 1))

--| `transposeN k` gives column i, for each i below k, as element i of every row that has one.
theorem List.transposeNColumns ∀ (rows: List (List a)) (k: Nat):
    List.transposeN k rows = List.map (List.range 0 k) (i => List.filterMap rows (row => List.get row i)) :=
  Eq.trans (Eq.cong (rows => List.transposeN k rows) (List.mapId rows).flipped) (List.transposeNColumnsFrom rows k 0)

--| Column i of `List.transpose` holds element i of every row that has one,
--| for each i below the first row's length.
theorem List.transposeColumns ∀ (rows: List (List a)):
    List.transpose rows
      = List.map (List.range 0 (List.length (List.headOr rows []))) (i =>
        List.filterMap rows (row => List.get row i)) :=
  List.transposeNColumns rows (List.length (List.headOr rows []))

--| Entry k of the running accumulations is the fold of the first k
--| elements ([`List.getOrScanLeft`], std/List/Index.sw, with a fallback).
theorem List.getScanLeft ∀ (f: b → a → b) (xs: List a) (z: b) (k: Nat)
    (h: k ≤ List.length xs):
    List.get (List.scanLeft xs z f) k = Some (List.foldLeft (List.take xs k) z f) :=
  match xs, k with
    | [], Zero => byComputing
    | [x, ..xs], Zero => byComputing
    | [x, ..xs], Succ k => List.getScanLeft f xs (f z x) k h

--| Element k of each element beside the running accumulations is `g` of
--| element k and the fold of the elements before it, and nothing past the end.
theorem List.getZipWithScanLeft ∀ (f: b → a → b) (g: a → b → c) (xs: List a) (z: b) (k: Nat):
    List.get (List.zipWith xs (List.scanLeft xs z f) g) k
      = Option.map (List.get xs k) (x => g x (List.foldLeft (List.take xs k) z f)) :=
  match xs, k with
    | [], k => byComputing
    | [x, ..xs], Zero => byComputing
    | [x, ..xs], Succ k => List.getZipWithScanLeft f g xs (f z x) k

theorem List.getExample: List.get (List.append [1, 2] (List.map [3, 4] Succ)) 3 = Some 5 := byComputing

--| For any list of successors, what `get` finds is not zero.
theorem List.getMapExample ∀ (xs: List Nat) (k v: Nat) (h: List.get (List.map xs Succ) k = Some v): v ≠ 0 :=
  Option.mapEqSome (List.get xs k) Succ v (Eq.trans (List.getMap xs Succ k).flipped h) (u found e =>
    rewrite <- e then Nat.succNotZero u)

--| `List.All2 r xs ys`: the lists are as long, and `r` holds of each pair of
--| elements at the same place (Coq's `Forall2`, Lean's `List.Forall₂`). What
--| [`Parse.eachLineReads`] says of the lines and the values read from them.
@[noReceiver]
def List.All2 (r: a → b → Prop): (xs: List a) → (ys: List b) → Prop
  | [], [] => Unit
  | [x, ..xs], [y, ..ys] => r x y ∧ List.All2 r xs ys
  | [], [y, ..ys] => Void
  | [x, ..xs], [] => Void

theorem List.all2Weaken ∀ [r s: a → b → Prop] (implies: ∀ (x: a) (y: b) => r x y → s x y) (xs: List a) (ys: List b)
    (all: List.All2 r xs ys):
    List.All2 s xs ys :=
  match xs, ys with
    | [], [] => Trivial
    | [x, ..xs], [y, ..ys] => Both (implies x y all.left) (List.all2Weaken implies xs ys all.right)

--| [`List.all2Weaken`] where the implication may use that the second element
--| is in `ys`: a fact about all of `ys` (a grid's rows are all as long as its
--| width) joins the relation.
theorem List.all2WeakenMem ∀ [r s: a → b → Prop] (xs: List a)
    (ys: List b) (implies: ∀ (x: a) (y: b) => y ∈ ys → r x y → s x y)
    (all: List.All2 r xs ys):
    List.All2 s xs ys :=
  match xs, ys with
    | [], [] => Trivial
    | [x, ..xs], [y, ..ys] =>
      Both
        (implies x y (Inl byComputing) all.left)
        (List.all2WeakenMem xs ys (x2 y2 member => implies x2 y2 (Inr member)) all.right)

--| Where each element is `f` of its partner, the list is the partners mapped.
theorem List.all2Map ∀ [f: b → a] (xs: List a) (ys: List b) (all: List.All2 (x y => x = f y) xs ys): xs = ys.map f :=
  match xs, ys with
    | [], [] => byComputing
    | [x, ..xs], [y, ..ys] => rewrite And.left all, List.all2Map xs ys all.right

theorem List.all2MapLeft ∀ (f: a → c) (r: c → b → Prop) (xs: List a) (ys: List b)
    (all: List.All2 (x y => r (f x) y) xs ys):
    List.All2 r (xs.map f) ys :=
  match xs, ys with
    | [], [] => Trivial
    | [x, ..xs], [y, ..ys] => Both all.left (List.all2MapLeft f r xs ys all.right)

--| The converse of [`List.all2MapLeft`]: a relation between the mapped list
--| and the values holds of each element's image.
theorem List.all2OfMapLeft ∀ (f: a → c) (r: c → b → Prop) (xs: List a) (ys: List b)
    (all: List.All2 r (xs.map f) ys):
    List.All2 (x y => r (f x) y) xs ys :=
  match xs, ys with
    | [], [] => Trivial
    | [x, ..xs], [y, ..ys] => Both all.left (List.all2OfMapLeft f r xs ys all.right)

--| The right-hand counterpart of [`List.all2OfMapLeft`]: a relation between
--| the left list and the mapped right list holds of each element's image.
theorem List.all2OfMapRight ∀ (g: b → c) (r: a → c → Prop) (xs: List a) (ys: List b)
    (all: List.All2 r xs (ys.map g)):
    List.All2 (x y => r x (g y)) xs ys :=
  match xs, ys with
    | [], [] => Trivial
    | [x, ..xs], [y, ..ys] => Both all.left (List.all2OfMapRight g r xs ys all.right)

--| Mapping two functions over one list gives lists related pointwise, when
--| the related values are `f x` and `g x` for each member `x`.
theorem List.all2MapBoth ∀ (r: b → c → Prop) (f: a → b) (g: a → c)
    (xs: List a) (pointwise: ∀ (x: a) => x ∈ xs → r (f x) (g x)):
    List.All2 r (xs.map f) (xs.map g) :=
  match xs with
    | [] => Trivial
    | [x, ..xs] =>
      Both (pointwise x (Inl byComputing)) (List.all2MapBoth r f g xs (y member => pointwise y (Inr member)))

--| Related lists are as long: the length half of `List.All2`.
theorem List.all2Length ∀ (r: a → b → Prop) (xs: List a) (ys: List b) (all: List.All2 r xs ys): xs.length = ys.length :=
  match xs, ys with
    | [], [] => byComputing
    | [x, ..xs], [y, ..ys] => Eq.cong Succ (List.all2Length r xs ys all.right)

--| Related lists joined are related: `xs ++ more` and `ys ++ moreTwin`.
theorem List.all2Append ∀ [r: a → b → Prop] (xs: List a) (ys: List b) (more: List a) (moreTwin: List b)
    (first: List.All2 r xs ys)
    (second: List.All2 r more moreTwin):
    List.All2 r (xs ++ more) (ys ++ moreTwin) :=
  match xs, ys with
    | [], [] => second
    | [x, ..xs], [y, ..ys] => Both first.left (List.all2Append xs ys more moreTwin first.right second)

--| Related lists reversed are related.
theorem List.all2Reverse ∀ [r: a → b → Prop] (xs: List a) (ys: List b)
    (all: List.All2 r xs ys):
    List.All2 r xs.reverse ys.reverse :=
  match xs, ys with
    | [], [] => Trivial
    | [x, ..xs], [y, ..ys] =>
      rewrite List.reverseCons x xs, List.reverseCons y ys then
        List.all2Append xs.reverse ys.reverse [x] [y] (List.all2Reverse xs ys all.right) (Both all.left Trivial)

--| Numbering the left list changes nothing a relation of the elements sees.
theorem List.all2WithIndex ∀ (r: a → b → Prop) (start: Nat) (xs: List a) (ys: List b)
    (all: List.All2 (entry y => r entry.snd y) (List.withIndexFrom start xs) ys):
    List.All2 r xs ys :=
  match xs, ys with
    | [], [] => Trivial
    | [x, ..xs], [y, ..ys] => Both all.left (List.all2WithIndex r (Succ start) xs ys all.right)

--| The converse of [`List.all2WithIndex`]: a relation of the elements holds
--| of the numbered list too, ignoring the numbers.
theorem List.all2OfWithIndex ∀ (r: a → b → Prop) (start: Nat) (xs: List a) (ys: List b)
    (all: List.All2 r xs ys):
    List.All2 (entry y => r entry.snd y) (List.withIndexFrom start xs) ys :=
  match xs, ys with
    | [], [] => Trivial
    | [x, ..xs], [y, ..ys] => Both all.left (List.all2OfWithIndex r (Succ start) xs ys all.right)

--| Zipped lists are as long as the shorter of the two.
theorem List.lengthZipWith ∀ (f: a → b → c) (xs: List a) (ys: List b):
    List.length (List.zipWith xs ys f) = Nat.min (List.length xs) (List.length ys) :=
  match xs, ys with
    | [], ys => byComputing
    | [x, ..xs], [] => byComputing
    | [x, ..xs], [y, ..ys] => rewrite List.lengthZipWith f xs ys, Nat.minSucc (List.length xs) (List.length ys)

--| Zipping appended lists, when the first parts have the same length, is
--| appending what the parts zip to.
theorem List.zipWithAppend ∀ (f: a → b → c) (xs2: List a) (ys2: List b) (xs: List a) (ys: List b)
    (same: List.length xs = List.length ys):
    List.zipWith (xs ++ xs2) (ys ++ ys2) f = List.zipWith xs ys f ++ List.zipWith xs2 ys2 f :=
  match xs, ys with
    | [], [] => byComputing
    | [x, ..xs], [y, ..ys] => rewrite List.zipWithAppend f xs2 ys2 xs ys (Nat.succInjective same)
    | [], [y, ..ys] => Void.impossible arithmetic
    | [x, ..xs], [] => Void.impossible arithmetic

--| Zipping two lists of the same length, each with one more element on the
--| end, adds `f` of the two to the end.
theorem List.zipWithSnoc ∀ (f: a → b → c) (x: a) (y: b) (xs: List a) (ys: List b)
    (same: List.length xs = List.length ys):
    List.zipWith (xs ++ [x]) (ys ++ [y]) f = List.zipWith xs ys f ++ [f x y] :=
  rewrite List.zipWithAppend f [x] [y] xs ys same

--| Mapping the first list before zipping is zipping with `f` composed with
--| the map.
theorem List.zipWithMapLeft ∀ (f: b → c → d) (g: a → b) (xs: List a) (ys: List c):
    List.zipWith (List.map xs g) ys f = List.zipWith xs ys (x y => f (g x) y) :=
  match xs, ys with
    | [], ys => byComputing
    | [x, ..xs], [] => byComputing
    | [x, ..xs], [y, ..ys] => rewrite List.zipWithMapLeft f g xs ys

--| Mapping the second list before zipping is zipping with `f` composed with
--| the map.
theorem List.zipWithMapRight ∀ (f: a → c → d) (g: b → c) (xs: List a) (ys: List b):
    List.zipWith xs (List.map ys g) f = List.zipWith xs ys (x y => f x (g y)) :=
  match xs, ys with
    | [], ys => byComputing
    | [x, ..xs], [] => byComputing
    | [x, ..xs], [y, ..ys] => rewrite List.zipWithMapRight f g xs ys

--| Mapping over zipped lists is zipping with `f` followed by the map.
theorem List.mapZipWith ∀ (f: a → b → c) (g: c → d) (xs: List a) (ys: List b):
    List.map (List.zipWith xs ys f) g = List.zipWith xs ys (x y => g (f x y)) :=
  match xs, ys with
    | [], ys => byComputing
    | [x, ..xs], [] => byComputing
    | [x, ..xs], [y, ..ys] => rewrite List.mapZipWith f g xs ys

--| Zipping with the arguments to `f` swapped is zipping the lists the other
--| way round.
theorem List.zipWithSwap ∀ (f: a → b → c) (xs: List a) (ys: List b):
    List.zipWith ys xs (y x => f x y) = List.zipWith xs ys f :=
  match xs, ys with
    | [], [] => byComputing
    | [], [y, ..ys] => byComputing
    | [x, ..xs], [] => byComputing
    | [x, ..xs], [y, ..ys] => rewrite List.zipWithSwap f xs ys

--| Chaining two `All2` facts through the middle list: if each `x`, `y`, `z`
--| at the same place with `r x y` and `s y z` have `t x z`, then `r` from
--| `xs` to `ys` and `s` from `ys` to `zs` give `t` from `xs` to `zs`.
theorem List.all2Compose ∀ [r: a → b → Prop] [s: b → c → Prop] [t: a → c → Prop]
    (link: ∀ (x: a) (y: b) (z: c) => r x y → s y z → t x z) (xs: List a) (ys: List b) (zs: List c)
    (first: List.All2 r xs ys)
    (second: List.All2 s ys zs):
    List.All2 t xs zs :=
  match xs, ys, zs with
    | [], [], [] => Trivial
    | [x, ..xs], [y, ..ys], [z, ..zs] =>
      Both (link x y z first.left second.left) (List.all2Compose link xs ys zs first.right second.right)

--| A list is related to itself, place by place, by any relation that holds
--| of every element and itself.
theorem List.all2Refl ∀ (r: a → a → Prop) (refl: ∀ (x: a) => r x x) (xs: List a): List.All2 r xs xs := match xs with
  | [] => Trivial
  | [x, ..xs] => Both (refl x) (List.all2Refl r refl xs)

--| Against a list of `n` copies of `y`, every element of `xs` is related to
--| `y`. The converse is [`List.all2ReplicateOf`].
theorem List.all2Replicate ∀ [r: a → b → Prop] (y: b):
    ∀ (xs: List a) (n: Nat) => List.All2 r xs (List.replicate n y) → ∀ (x: a) => x ∈ xs → r x y
  | [], n, all, x, member => member.impossible
  | [z, ..zs], Zero, all, x, member => all.impossible
  | [z, ..zs], Succ n, all, x, Inl same => rewrite <- same then And.left all
  | [z, ..zs], Succ n, all, x, Inr later => List.all2Replicate y zs n all.right x later

--| A list of `n` elements, each related to `y`, is related place by place to
--| `n` copies of `y`. The converse is [`List.all2Replicate`].
theorem List.all2ReplicateOf ∀ [r: a → b → Prop] (y: b) (xs: List a) (n: Nat)
    (same: xs.length = n) (related: ∀ (x: a) => x ∈ xs → r x y):
    List.All2 r xs (List.replicate n y) :=
  match xs, n with
    | [], Zero => Trivial
    | [], Succ n => (Nat.zeroNotSucc _ same).impossible
    | [x, ..xs], Succ n =>
      Both
        (related x (Inl byComputing))
        (List.all2ReplicateOf y xs n (Nat.succInjective same) (z member => related z (Inr member)))

--| Zipping two lists of the same length gives a list of that length (unlike
--| [`List.lengthZipWith`], which gives the shorter of the two).
theorem List.lengthZipWithEq ∀ (f: a → b → c) (xs: List a) (ys: List b)
    (same: xs.length = ys.length):
    (List.zipWith xs ys f).length = xs.length :=
  match xs, ys with
    | [], [] => byComputing
    | [], [y, ..ys] => (Nat.zeroNotSucc _ same).impossible
    | [x, ..xs], [] => (Nat.succNotZero _ same).impossible
    | [x, ..xs], [y, ..ys] => Eq.cong Succ (List.lengthZipWithEq f xs ys (Nat.succInjective same))

--| Where `r` holds of every result of `f` and its first argument, the zip of
--| two lists of the same length is related, place by place, to the first.
theorem List.all2ZipWithLeft ∀ (f: a → b → c) (r: c → a → Prop) (pointwise: ∀ (x: a) (y: b) => r (f x y) x)
    (xs: List a) (ys: List b)
    (same: xs.length = ys.length):
    List.All2 r (List.zipWith xs ys f) xs :=
  match xs, ys with
    | [], [] => Trivial
    | [], [y, ..ys] => (Nat.zeroNotSucc _ same).impossible
    | [x, ..xs], [] => (Nat.succNotZero _ same).impossible
    | [x, ..xs], [y, ..ys] => Both (pointwise x y) (List.all2ZipWithLeft f r pointwise xs ys (Nat.succInjective same))

--| Where `r` holds of every result of `f` and its second argument, the zip of
--| two lists of the same length is related, place by place, to the second.
theorem List.all2ZipWithRight ∀ (f: a → b → c) (r: c → b → Prop) (pointwise: ∀ (x: a) (y: b) => r (f x y) y)
    (xs: List a) (ys: List b)
    (same: xs.length = ys.length):
    List.All2 r (List.zipWith xs ys f) ys :=
  match xs, ys with
    | [], [] => Trivial
    | [], [y, ..ys] => (Nat.zeroNotSucc _ same).impossible
    | [x, ..xs], [] => (Nat.succNotZero _ same).impossible
    | [x, ..xs], [y, ..ys] => Both (pointwise x y) (List.all2ZipWithRight f r pointwise xs ys (Nat.succInjective same))

--| A list with no element equal to `x` counts none: `xs.contains x` is
--| `False` exactly when `x` is not among `xs`.
theorem List.countZeroOfNotContains ∀ [auto eq: DecEq a] (xs: List a) (x: a)
    (absent: xs.contains x = False):
    xs.count (y => y == x) = 0 :=
  List.countNone xs (y => y == x) (y member =>
    match same: y == x with
      | True => Void.impossible (Bool.falseNotTrue (Eq.trans absent.flipped (rewrite <- same.read then member)))
      | False => byComputing)

--| If every value occurs in `xs` at most once (counted with `==`), `xs` has
--| no repeats. Unlike [`List.distinctOfOccurrences`] this needs no key, and
--| it holds of a list being built up, where each step changes one count.
theorem List.distinctOfCounts ∀ [auto eq: DecEq a] (xs: List a)
    (counts: ∀ (x: a) => xs.count (y => y == x) ≤ 1):
    xs.Distinct :=
  match xs with
    | [] => Trivial
    | [x, ..xs] =>
      Both
        (member =>
          let here := counts x
          let positive := List.countPositive xs (y => y == x) x member (DecEq.refl x)
          let split := List.countCons xs x (y => y == x)
          let self := DecEq.refl x
          rewrite split, self at here then arithmetic)
        (List.distinctOfCounts xs (other =>
          let here := counts other
          let split := List.countCons xs x (y => y == other)
          rewrite split at here then arithmetic))

test "List.zipWith lemmas" :=
  List.zipWith ([1, 2] ++ [3]) ([10, 20] ++ [30, 40]) (x y => x + y) == [11, 22, 33]
    ∧ List.length (List.zipWith [1, 2, 3] [4, 5] (x y => x + y)) == 2

--| Equal non-empty lists have equal tails; [`List.consInjectiveHead`] gives the heads.
theorem List.consTailEq ∀ (x y: a) (xs ys: List a) (same: [x, ..xs] = [y, ..ys]): xs = ys :=
  Eq.cong (list => list.drop 1) same

--| Consing equal heads onto equal tails gives equal lists.
theorem List.consCong ∀ (x y: a) (xs ys: List a) (head: x = y) (tail: xs = ys): [x, ..xs] = [y, ..ys] :=
  rewrite head, tail

--| Two joined lists that are equal, with equal first parts in length, have equal first parts and equal second parts.
theorem List.appendCancel ∀ (a c b d: List x) (joined: a ++ b = c ++ d) (lengths: a.length = c.length): a = c ∧ b = d :=
  match a, c with
    | [], [] => (byComputing, joined)
    | [], [q, ..qs] => Void.impossible (Nat.zeroNotSucc qs.length lengths)
    | [p, ..ps], [] => Void.impossible (Nat.succNotZero ps.length lengths)
    | [p, ..ps], [q, ..qs] =>
      let headSame: p = q := Eq.cong (all => all.headOr p) joined
      let (restSame, tailSame) :=
        List.appendCancel ps qs b d (Eq.cong (all => all.drop 1) joined) (Eq.cong (n => n - 1) lengths)
      (List.consCong p q ps qs headSame restSame, tailSame)

--| The head of a join with a non-empty front is the front's head.
theorem List.headAppend ∀ (front back: List a) (filled: front ≠ []): (front ++ back).head = front.head :=
  match front, filled with
    | [], never => (never byComputing).impossible
    | [first, ..rest], _ => byComputing

--| The head of a three-part join with a non-empty front is the front's head.
theorem List.headAppendMiddle ∀ (front middle back: List a)
    (nonEmpty: front ≠ []):
    ((front ++ middle) ++ back).head = front.head :=
  match front, nonEmpty with
    | [], nonEmpty => (nonEmpty byComputing).impossible
    | [first, ..more], nonEmpty => byComputing

--| `reverseOnto` a non-empty accumulator is non-empty.
theorem List.reverseOntoNonEmpty ∀ (xs acc: List a)
    (filled: acc.isEmpty = False):
    (xs.reverseOnto acc).isEmpty = False :=
  match xs with
    | [] => filled
    | [x, ..rest] => List.reverseOntoNonEmpty rest [x, ..acc] byComputing

--| `reverseOnto` is empty exactly when both the list and the accumulator are.
theorem List.isEmptyReverseOnto ∀ (xs acc: List a): (xs.reverseOnto acc).isEmpty = (xs.isEmpty && acc.isEmpty) :=
  match xs with
    | [] => byComputing
    | [x, ..rest] => rewrite List.isEmptyReverseOnto rest [x, ..acc] then cases

--| A test over a join holds of both parts: `all` over `++` is the `&&` of the two `all`s.
theorem List.allAppendAnd ∀ (xs ys: List a) (p: a → Bool): (xs ++ ys).all p = (xs.all p && ys.all p) := match xs with
  | [] => byComputing
  | [x, ..rest] =>
    match p x with
      | True => List.allAppendAnd rest ys p
      | False => byComputing

--| A test that holds of both of two lists holds of their join.
theorem List.allAppendTrue ∀ (xs ys: List a) (p: a → Bool)
    (first: xs.all p = True)
    (second: ys.all p = True):
    (xs ++ ys).all p = True :=
  match xs with
    | [] => second
    | [x, ..rest] => Bool.andIntro (Bool.andLeft first) (List.allAppendTrue rest ys p (Bool.andRight first) second)

--| A test that holds of a list and of an accumulator holds of the list reversed onto the accumulator.
theorem List.allReverseOntoTrue ∀ (p: a → Bool) (xs acc: List a)
    (all: xs.all p = True)
    (allAcc: acc.all p = True):
    (xs.reverseOnto acc).all p = True :=
  match xs with
    | [] => allAcc
    | [x, ..more] =>
      List.allReverseOntoTrue p more [x, ..acc] (Bool.andRight all) (Bool.andIntro (Bool.andLeft all) allAcc)

--| `all` over a list reversed onto an accumulator is the `&&` of the `all`s of the two.
theorem List.allReverseOntoAnd ∀ (xs acc: List a) (p: a → Bool): (xs.reverseOnto acc).all p = (xs.all p && acc.all p) :=
  match xs with
    | [] => byComputing
    | [x, ..rest] =>
      calc (rest.reverseOnto [x, ..acc]).all p
        _ = (rest.all p && [x, ..acc].all p) := List.allReverseOntoAnd rest [x, ..acc] p
        _ = ([x, ..rest].all p && acc.all p) := cases

--| A test that holds of a list holds of its reverse.
theorem List.allReverseTrue ∀ (p: a → Bool) (xs: List a) (all: xs.all p = True): xs.reverse.all p = True :=
  List.allReverseOntoTrue p xs [] all byComputing

--| A test that holds of a join holds of its second part.
theorem List.allAppendRightTrue ∀ (p: a → Bool) (xs ys: List a) (all: (xs ++ ys).all p = True): ys.all p = True :=
  match xs with
    | [] => all
    | [x, ..more] => List.allAppendRightTrue p more ys (Bool.andRight all)

--| A test that holds of a non-empty list holds of its head and of its tail.
theorem List.allConsElim ∀ (x: a) (xs: List a) (p: a → Bool)
    (all: [x, ..xs].all p = True):
    p x = True ∧ xs.all p = True :=
  match holds: p x, all with
    | True, all => (byComputing, all)
    | False, never => (Bool.falseNotTrue never).impossible

--| A list that `isEmpty` is `[]`.
theorem List.eqNilOfIsEmpty ∀ (xs: List a) (empty: xs.isEmpty = True): xs = [] := match xs with | [] => byComputing

--| A list with an element after the front is not empty.
theorem List.isEmptyAppendCons ∀ (xs: List a) (y: a) (ys: List a): (xs ++ [y, ..ys]).isEmpty = False := match xs with
  | [] => byComputing
  | [_, .._] => byComputing

--| Dropping the length of the first part off a join leaves the second part.
theorem List.dropAppendOf ∀ (whole read later: List t)
    (starts: whole = read ++ later):
    whole.drop read.length = later :=
  rewrite starts then List.dropAppend read later

--| `takeWhile` keeps the whole of a list whose elements all pass.
theorem List.takeWhileOfAll ∀ (passes: a → Bool) (chars: List a)
    (all: chars.all passes = True):
    chars.takeWhile passes = chars :=
  match chars with
    | [] => byComputing
    | [char, ..rest] => rewrite Bool.andLeft all, List.takeWhileOfAll passes rest (Bool.andRight all)

--| `takeWhile` over a join of a list that all passes and one that stops at once keeps the first part.
theorem List.takeWhileAppendThenStops ∀ (passes: a → Bool) (front back: List a)
    (all: front.all passes = True)
    (stops: back.takeWhile passes = []):
    (front ++ back).takeWhile passes = front :=
  match front, all with
    | [], all => stops
    | [char, ..more], all =>
      rewrite Bool.andLeft all, List.takeWhileAppendThenStops passes more back (Bool.andRight all) stops

--| Lists with the same head stop `takeWhile` together at once.
theorem List.takeWhileSameHead ∀ (passes: a → Bool) (before after: List a)
    (same: before.head = after.head)
    (stops: before.takeWhile passes = []):
    after.takeWhile passes = [] :=
  match before, after, same with
    | [], [], same => stops
    | [first, ..more], [other, ..others], same =>
      rewrite <- Option.someInjective same then
        match passes first with
          | False => byComputing

--| `takeWhile` takes nothing from a list whose head fails the test.
theorem List.takeWhileHeadFails ∀ (passes: a → Bool) (chars: List a) (first: a)
    (head: chars.head = Some first)
    (fails: passes first = False):
    chars.takeWhile passes = [] :=
  match chars, head with
    | [], head => cases
    | [other, ..more], head => rewrite Option.someInjective head, fails

--| If `takeWhile` takes nothing from a join, it takes nothing from its front.
theorem List.takeWhileNilPrefix ∀ (passes: a → Bool) (front back: List a)
    (stops: (front ++ back).takeWhile passes = []):
    front.takeWhile passes = [] :=
  match front with
    | [] => byComputing
    | [first, ..more] =>
      match pass: passes first with
        | False => byComputing

--| `takeWhile` of a list whose head passes keeps the head and goes on with the tail.
theorem List.takeWhileConsOf ∀ (passes: a → Bool) (rest: List a) (c: a) (more: List a)
    (here: rest = [c, ..more])
    (first: passes c = True):
    rest.takeWhile passes = [c, ..more.takeWhile passes] :=
  rewrite here, first

--| `dropWhile` over a join where the second part starts with an element that fails drops only from the first part.
theorem List.dropWhileAppendStop ∀ (p: a → Bool) (xs: List a) (stop: a) (more: List a)
    (stops: p stop = False):
    (xs ++ [stop, ..more]).dropWhile p = xs.dropWhile p ++ [stop, ..more] :=
  match xs with
    | [] => rewrite stops
    | [x, ..rest] =>
      match p x with
        | True => List.dropWhileAppendStop p rest stop more stops
        | False => byComputing

--| A reversed cons appended to a list is the reversed tail followed by the head and the list.
theorem List.reverseConsAppend ∀ (first: a) (rest after: List a):
    [first, ..rest].reverse ++ after = rest.reverse ++ [first, ..after] :=
  rewrite List.reverseCons first rest then List.appendAssoc rest.reverse [first] after

--| Lists related element by element are empty together.
theorem List.all2IsEmpty ∀ [r: a → b → Prop] (xs: List a) (ys: List b)
    (alike: List.All2 r xs ys):
    xs.isEmpty = ys.isEmpty :=
  match xs, ys with
    | [], [] => byComputing
    | [x, ..xs], [y, ..ys] => byComputing

--| What holds of every element of a list of lists' concatenation holds of every element of every list.
theorem List.allOfConcat ∀ (p: a → Prop) (lists: List (List a))
    (all: List.All p lists.concat):
    List.All (part => List.All p part) lists :=
  match lists with
    | [] => Trivial
    | [first, ..rest] =>
      let split: List.All p (first ++ rest.concat) := all
      (
        List.allAppendLeft p first rest.concat split,
        List.allOfConcat p rest (List.allAppendRight p first rest.concat split)
      )

--| A property of a head and of a list holds of the whole list reversed, which is at least as long as the tail.
theorem List.allConsReverse ∀ (holds: a → Prop) (current: a) (found: List a) (currentHolds: holds current)
    (foundHolds: List.All holds found):
    List.All holds [current, ..found].reverse ∧ found.length + 1 <= [current, ..found].reverse.length :=
  (
    List.allReverse holds [current, ..found] (currentHolds, foundHolds),
    arithmetic [List.lengthReverse [current, ..found]]
  )

--| A test that implies another test on every element makes the second hold of whatever the first holds of.
theorem List.allImpliesBool ∀ (chars: List a) (passes follows: a → Bool)
    (implied: ∀ (char: a) => passes char = True → follows char = True)
    (all: chars.all passes = True):
    chars.all follows = True :=
  match chars, all with
    | [], all => byComputing
    | [first, ..more], all =>
      Bool.andIntro
        (implied first (Bool.andLeft all))
        (List.allImpliesBool more passes follows implied (Bool.andRight all))

--| A list with an element added at the end is not empty.
theorem List.snocNotNil ∀ (docs: List a) (last: a): docs ++ [last] ≠ [] := match docs with
  | [] => List.consNotNil last []
  | [doc, ..rest] => List.consNotNil doc (rest ++ [last])

--| Dropping fewer than all the elements leaves some.
theorem List.dropNotNil ∀ (docs: List a) (count: Nat)
    (short: count ≤ docs.length)
    (differs: (count == docs.length) = False):
    docs.drop count ≠ [] :=
  match docs, count with
    | [], Zero => cases
    | [doc, ..rest], Zero => List.consNotNil doc rest
    | [doc, ..rest], Succ more => List.dropNotNil rest more (arithmetic [short]) differs

--| Taking a positive number of elements from a non-empty list leaves some.
theorem List.takeConsNotNil ∀ (doc: a) (rest: List a) (count: Nat)
    (positive: count ≠ 0):
    [doc, ..rest].take count ≠ [] :=
  match count with
    | Zero => (positive byComputing).impossible
    | Succ more => List.consNotNil doc (rest.take more)

--| A join with two elements at the start of its second part has at least two elements.
theorem List.twoLeLengthAppend ∀ (front: List a) (first second: a) (more: List a):
    2 ≤ (front ++ [first, second, ..more]).length :=
  rewrite List.lengthAppend front [first, second, ..more] then arithmetic

--| Items related element by element to two joined lists split where the lists join.
theorem List.all2AppendSplit ∀ (r: a → b → Prop) (read: List a) (front back: List b)
    (all: List.All2 r read (front ++ back)):
    ∃ (first second: List a) => read = first ++ second ∧ List.All2 r first front ∧ List.All2 r second back :=
  match front, read, all with
    | [], read, all => ([], read, byComputing, Trivial, all)
    | [y, ..ys], [x, ..xs], (head, rest) =>
      let (first, second, isRead, firstAll, secondAll) := List.all2AppendSplit r xs ys back rest
      ([x, ..first], second, (rewrite isRead), (head, firstAll), secondAll)

--| The head of a list that starts with an element that differs from `other` is not `Some other`.
theorem List.headNeOfBeqFalse ∀ (char: Char) (more: List Char) (other: Char)
    (differs: (char == other) = False):
    [char, ..more].head ≠ Some other :=
  same => DecEq.soundFalse char other differs (Option.someInjective same)

--| The first element of a list whose head is not `Some char` is not `char`.
theorem List.beqFalseOfHeadNe ∀ (next: Char) (more: List Char) (char: Char)
    (different: [next, ..more].head ≠ Some char):
    (next == char) = False :=
  let ne: next ≠ char := same => different (rewrite same)
  DecEq.falseOfNe ne

--| The head of a list that is `Some first` is not `Some other` when `first` and `other` differ.
theorem List.headNeOfHead ∀ (rest: List Char) (first other: Char)
    (head: rest.head = Some first)
    (differs: first ≠ other):
    rest.head ≠ Some other :=
  same => differs (Option.someInjective (Eq.trans head.flipped same))
