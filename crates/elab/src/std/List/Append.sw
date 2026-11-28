--| Lemmas about lengths, appending, folds and sums, ranges, partitioning,
--| replication, padding, transposing, `head`/`init`, and the `All`/`Any`
--| lemmas about them, with the examples and tests that use them.

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
  | [] | [_] => byComputing
  | [x, next, ..rest] => rewrite List.lengthZipWithNext [next, ..rest]

--| The list zipped with its own tail.
theorem List.zipWithNextZip ∀ (xs: List a): List.zipWithNext xs = List.zip xs (List.tailOf xs) := match xs with
  | [] | [_] => byComputing
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
    | [] | [_] => byComputing
    | [x, next, ..rest] => rewrite List.chainZipWithNext [next, ..rest] holds

--| Without the first element, it still holds.
theorem List.chainTail ∀ (xs: List a) (holds: a → a → Bool)
    (chained: List.chain xs holds = True):
    List.chain (List.tailOf xs) holds = True :=
  match xs with
    | [] | [_] => byComputing
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
    | [] | [_] => byComputing
    | [next, after, ..more] =>
      let Both first rest := chained
      Both first (List.chainInitCons next [after, ..more] holds rest)

--| A `chain` of two tests together holds when the chain of each one does.
theorem List.chainAnd ∀ (xs: List a) (holds1 holds2: a → a → Bool):
    List.chain xs (x y => holds1 x y ∧ holds2 x y) = (List.chain xs holds1 ∧ List.chain xs holds2) :=
  match xs with
    | [] | [_] => byComputing
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

--| `List.rangeFrom n s` has `n` elements.
theorem List.lengthRangeFrom ∀ (n s: Nat): List.length (List.rangeFrom n s) = n := match n with
  | Zero => byComputing
  | Succ n => rewrite List.lengthRangeFrom n (Succ s)

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

--| A list whose elements are all `x` is `replicate` of its length.
theorem List.replicateLengthOfAll ∀ [auto eq: DecEq a] (x: a) (xs: List a)
    (all: xs.all (y => y == x) = True):
    List.replicate xs.length x = xs :=
  match xs with
    | [] => byComputing
    | [y, ..rest] =>
      let same: y = x := DecEq.sound (Bool.andLeft all)
      rewrite same then Eq.cong (later => [x, ..later]) (List.replicateLengthOfAll x rest (Bool.andRight all))

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
    | [x, ..xs], _ => byFacts [List.allAppendLeft]

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
        | True | False => rewrite List.filterAppend rest ys p

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
