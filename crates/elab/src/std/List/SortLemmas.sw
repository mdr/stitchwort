--| Lemmas about the sorting functions of List/Sort.sw (sorted, a permutation,
--| the same length, sorting what is already sorted), with the Nat and List
--| lemmas around them: sums of lists, Gauss, counting occurrences, keys,
--| subsequences and splitting runs of positions, and `drop` past the end and
--| sliding windows (`List.windows`).

--| `<=` is total: if `m <= n` is false, then `n <= m`.
theorem Nat.leqTotal ∀ (m n: Nat) (h: Nat.leq m n = False): Nat.leq n m = True := Nat.lessLe n m h.read

--| Sums of lists: one element at a time, sums of intervals (Gauss), and
--| rewriting under `map`, `filter` and `foldLeft`.
theorem Nat.addSwap ∀ (a b c d: Nat): (a + b) + (c + d) = (a + c) + (b + d) := ring

--| Sums from a starting total, one element at a time and of two lists, for
--| any `Add`. At `Nat` they state the facts about `Nat` sums, by computation.
-- (docs/proposals/interfaces.md §7.7)
theorem List.sumFrom ∀ [auto add: Add a] (xs: List a) (z: a): List.foldLeft xs z Add.add = z + List.sum xs :=
  match xs with
    | [] => Eq.sym (Add.addZero z)
    | [x, ..xs] =>
      calc List.foldLeft xs (z + x) Add.add
        _ = (z + x) + List.sum xs := List.sumFrom xs (z + x)
        _ = z + (x + List.sum xs) := add.assoc z x (List.sum xs)
        _ = z + List.foldLeft xs x Add.add := Eq.cong (t => z + t) (Eq.sym (List.sumFrom xs x))
        _ = z + List.sum [x, ..xs] := Eq.cong (t => z + List.foldLeft xs t Add.add) (Eq.sym (add.zeroAdd x))

theorem List.sumCons ∀ [auto add: Add a] (x: a) (xs: List a): List.sum [x, ..xs] = x + List.sum xs :=
  Eq.trans (Eq.cong (t => List.foldLeft xs t Add.add) (add.zeroAdd x)) (List.sumFrom xs x)

theorem List.sumAppend ∀ [auto add: Add a] (xs ys: List a): List.sum (List.append xs ys) = List.sum xs + List.sum ys :=
  match xs with
    | [] => Eq.sym (add.zeroAdd (List.sum ys))
    | [x, ..xs] =>
      Eq.trans
        (List.sumCons x (List.append xs ys))
        (Eq.trans
          (Eq.cong (t => x + t) (List.sumAppend xs ys))
          (Eq.trans
            (Eq.sym (add.assoc x (List.sum xs) (List.sum ys)))
            (Eq.cong (t => t + List.sum ys) (Eq.sym (List.sumCons x xs)))))

theorem List.sumByMulLeft ∀ (xs: List a) (c: Nat) (f: a → Nat): List.sumBy xs (x => c * f x) = c * List.sumBy xs f :=
  match xs with
    | [] => ring
    | [x, ..xs] => rewrite List.sumByCons xs x (y => c * f y), List.sumByCons xs x f, List.sumByMulLeft xs c f in ring

theorem List.sumByRangeShift ∀ (f: Nat → Nat) (n s: Nat):
    List.sumBy (List.rangeFrom n (Succ s)) f = List.sumBy (List.rangeFrom n s) (i => f (Succ i)) :=
  match n with
    | Zero => rfl
    | Succ n =>
      Eq.trans
        (List.sumByCons (List.rangeFrom n (Succ (Succ s))) (Succ s) f)
        (Eq.trans
          (Eq.cong (t => f (Succ s) + t) (List.sumByRangeShift f n (Succ s)))
          (Eq.sym (List.sumByCons (List.rangeFrom n (Succ s)) s (i => f (Succ i)))))

--| A sum over `s, s + 1, ..., s + n - 1`, as one over `0, 1, ..., n - 1`.
theorem List.sumByRangeOffset ∀ (f: Nat → Nat) (s n: Nat):
    List.sumBy (List.rangeFrom n s) f = List.sumBy (List.range 0 n) (i => f (s + i)) :=
  match s with
    | Zero => List.sumByCong (List.range 0 n) f (i => f (0 + i)) (i => rfl)
    | Succ s => Eq.trans (List.sumByRangeShift f n s) (List.sumByRangeOffset (i => f (Succ i)) s n)

theorem List.sumByRangeOffsetExample: List.sumBy (List.rangeFrom 3 10) (i => i)
      = List.sumBy (List.range 0 3) (i => 10 + i) :=
  rfl

--| Gauss: twice the sum of `x, x + 1, ..., x + d` is `(d + 1) * (x + (x + d))`.
theorem List.gaussSum ∀ (d x: Nat):
    List.sum (List.rangeFrom (Succ d) x) + List.sum (List.rangeFrom (Succ d) x) = Succ d * (x + (x + d)) :=
  match d with
    | Zero => ring
    | Succ d => rewrite List.sumCons x (List.rangeFrom (Succ d) (Succ x)) in ring [List.gaussSum d (Succ x)]

--| The sum of `count` consecutive numbers from `start`, closed form:
--| `(List.rangeFrom 4 10).sum` is `4 * 10 + 4 * 3 / 2`, 46. Gauss's rule
--| ([`List.gaussSum`]) with the product `count * (count - 1)` always even.
theorem List.sumRangeFrom ∀ (count start: Nat):
    List.sum (List.rangeFrom count start) = count * start + count * (count - 1) / 2 :=
  match count with
    | Zero => rfl
    | Succ d =>
      let gauss := List.gaussSum d start
      let expand: d * (start + (start + d)) = 2 * (d * start) + d * d := ring
      let shape: Succ d * start = start + d * start := ring
      omega [gauss, expand, shape]

theorem Nat.spanEmpty ∀ (x y: Nat) (h: y ≤ x): Nat.span x y = 0 :=
  Eq.cong (t => List.sum (List.rangeFrom t x)) (Nat.subEqZero y x h)

theorem Nat.spanStep ∀ (s y: Nat) (h: Succ s ≤ y): Nat.span s y = s + Nat.span (Succ s) y :=
  Eq.trans
    (Eq.cong (t => List.sum (List.rangeFrom t s)) (Nat.subSuccRight s y h))
    (List.sumCons s (List.rangeFrom (y - Succ s) (Succ s)))

--| The closed form is the sum of `lo..hi`.
theorem Nat.gaussSpan ∀ (d lo hi: Nat) (h: lo ≤ hi): d * ((lo + hi) * (hi - lo + 1) / 2) = d * Nat.span lo (Succ hi) :=
  Eq.trans
    (Eq.cong
      (t => d * (t / 2))
      (Eq.trans
        (Eq.cong (t => (lo + t) * (hi - lo + 1)) (Eq.sym (Nat.addSubCancel lo hi h)))
        (Eq.trans
          (Eq.cong (t => (lo + (lo + (hi - lo))) * t) (Nat.addOne (hi - lo)))
          (Eq.trans (Nat.mulComm (lo + (lo + (hi - lo))) (Succ (hi - lo))) (Eq.sym (List.gaussSum (hi - lo) lo))))))
    (Eq.trans
      (Eq.cong (t => d * t) (Nat.halfDouble (List.sum (List.rangeFrom (Succ (hi - lo)) lo))))
      (Eq.sym (Eq.cong (t => d * List.sum (List.rangeFrom t lo)) (Nat.subSuccRight lo (Succ hi) h))))

--| Gauss's formula is the sum of the numbers from first to last, for any bounds.
theorem Nat.sumBetweenCorrect ∀ (first last: Nat): Nat.sumBetween first last = (List.range first (last + 1)).sum :=
  match h: Nat.leq first last with
    | True =>
      calc Nat.sumBetween first last
        _ = (first + last) * (last - first + 1) / 2 := rewrite Nat.addOneSub last first h
        _ = 1 * ((first + last) * (last - first + 1) / 2) := ring
        _ = 1 * Nat.span first (Succ last) := Nat.gaussSpan 1 first last h
        _ = Nat.span first (Succ last) := ring
        _ = (List.range first (last + 1)).sum :=
          Eq.cong (t => List.sum (List.rangeFrom (t - first) first)) (Eq.sym (Nat.addOne last))
    | False =>
      calc Nat.sumBetween first last
        _ = (first + last) * 0 / 2 := rewrite Nat.addOneSubEqZero last first h
        _ = 0 := rewrite Nat.mulZero (first + last)
        _ = (List.range first (last + 1)).sum := rewrite Nat.addOneSubEqZero last first h

--| How many pairs `List.pairs` makes: n(n - 1)/2. One step of the count:
--| `x` is paired with the n others, and p is the number of pairs among those.
theorem List.pairsStep ∀ (n p: Nat) (h: p + p + n = n * n): (n + p) + (n + p) + Succ n = Succ n * Succ n := ring [h]

--| Twice the number of pairs, and the number of elements, make n * n.
theorem List.lengthPairsDouble ∀ (xs: List a):
    List.length (List.pairs xs) + List.length (List.pairs xs) + List.length xs = List.length xs * List.length xs :=
  match xs with
    | [] => rfl
    | [x, ..xs] =>
      rewrite List.lengthAppend (List.map xs (y => MkPair x y)) (List.pairs xs), List.lengthMap xs (y => MkPair x y) in
        List.pairsStep (List.length xs) (List.length (List.pairs xs)) (List.lengthPairsDouble xs)

theorem List.pairsDoubleSub ∀ (n p: Nat) (h: p + p + n = n * n): p + p = n * (n - 1) := match n with
  | Zero => ring [h]
  | Succ m => ring [h]

--| Twice the number of pairs is n * (n - 1).
theorem List.lengthPairsDoubled ∀ (xs: List a):
    List.length (List.pairs xs) + List.length (List.pairs xs) = List.length xs * (List.length xs - 1) :=
  List.pairsDoubleSub (List.length xs) (List.length (List.pairs xs)) (List.lengthPairsDouble xs)

--| n(n - 1)/2 pairs.
theorem List.lengthPairs ∀ (xs: List a): List.length (List.pairs xs) = List.length xs * (List.length xs - 1) / 2 :=
  rewrite Eq.sym (List.lengthPairsDoubled xs), Nat.halfDouble (List.length (List.pairs xs)) in rfl

--| `p` written n times: n times as long, and one more copy goes on the end.
theorem List.lengthConcatReplicate ∀ (p: List a) (n: Nat):
    List.length (List.concat (List.replicate n p)) = n * List.length p :=
  match n with
    | Zero => rfl
    | Succ n =>
      Eq.trans
        (List.lengthAppend p (List.concat (List.replicate n p)))
        (Eq.cong (t => List.length p + t) (List.lengthConcatReplicate p n))

theorem List.concatReplicateSnoc ∀ (p: List a) (n: Nat):
    List.concat (List.replicate (Succ n) p) = List.append (List.concat (List.replicate n p)) p :=
  match n with
    | Zero => List.appendNil p
    | Succ n =>
      calc List.append p (List.concat (List.replicate (Succ n) p))
        _ = List.append p (List.append (List.concat (List.replicate n p)) p) :=
          Eq.cong (List.append p) (List.concatReplicateSnoc p n)
        _ = List.append (List.append p (List.concat (List.replicate n p))) p :=
          Eq.sym (List.appendAssoc p (List.concat (List.replicate n p)) p)

theorem List.lengthTake ∀ (xs: List a) (k: Nat) (h: k ≤ List.length xs): List.length (List.take xs k) = k :=
  match xs, k with
    | xs, Zero => rfl
    | [x, ..xs], Succ k => Eq.cong Succ (List.lengthTake xs k h)

theorem List.takeAll ∀ (xs: List a) (k: Nat) (h: List.length xs ≤ k): List.take xs k = xs := match xs, k with
  | [], Zero => rfl
  | [], Succ k => rfl
  | [x, ..xs], Succ k => Eq.cong (Cons x) (List.takeAll xs k h)

--| Dropping at least the whole length leaves nothing.
theorem List.dropPast ∀ (xs: List a) (k: Nat) (h: List.length xs ≤ k): List.drop xs k = [] := match xs, k with
  | [], k => List.dropNil k
  | [x, ..xs], Succ k => List.dropPast xs k h

-- Sliding windows (`List.windows`): how many there are, how long each is,
-- one step at a time, and the same as the suffixes cut to `size`, keeping
-- the whole ones.

theorem List.lengthWindowsCount ∀ (size count: Nat) (xs: List a):
    List.length (List.windowsCount size count xs) = count :=
  match count with
    | Zero => rfl
    | Succ count => Eq.cong Succ (List.lengthWindowsCount size count (List.drop xs 1))

--| A list of length n has n + 1 - size windows.
theorem List.lengthWindows ∀ (xs: List a) (size: Nat): List.length (List.windows xs size) = List.length xs + 1 - size :=
  List.lengthWindowsCount size (List.length xs + 1 - size) xs

theorem List.lengthOfMemWindowsCount ∀ (size: Nat):
    ∀ (count: Nat) (xs: List a) => count ≤ List.length xs + 1 - size
      → ∀ (w: List a) => w ∈ List.windowsCount size count xs → List.length w = size
  | Zero, xs, h, w, m => Void.exfalso m
  | Succ count, [], h, w, Inl e => Eq.trans (Eq.cong List.length (Eq.sym e)) (List.lengthTake [] size (omega [h]))
  | Succ count, [], h, w, Inr m => List.lengthOfMemWindowsCount size count [] (omega [h]) w m
  | Succ count, [x, ..rest], h, w, Inl e =>
    Eq.trans (Eq.cong List.length (Eq.sym e)) (List.lengthTake [x, ..rest] size (omega [h]))
  | Succ count, [x, ..rest], h, w, Inr m => List.lengthOfMemWindowsCount size count rest (omega [h]) w m

--| Every window of `List.windows xs size` has `size` elements.
theorem List.lengthOfMemWindows ∀ (xs: List a) (size: Nat) (w: List a)
    (m: w ∈ List.windows xs size):
    List.length w = size :=
  List.lengthOfMemWindowsCount size (List.length xs + 1 - size) xs (Nat.leRefl (List.length xs + 1 - size)) w m

--| A list with a whole window at its start: that window, then the windows of
--| the rest.
theorem List.windowsCons ∀ (x: a) (rest: List a) (size: Nat)
    (h: size ≤ List.length [x, ..rest]):
    List.windows [x, ..rest] size = [List.take [x, ..rest] size, ..List.windows rest size] :=
  Eq.cong
    (count => List.windowsCount size count [x, ..rest])
    (omega [h]: List.length [x, ..rest] + 1 - size = Succ (List.length rest + 1 - size))

--| A list shorter than a window has none.
theorem List.windowsShort ∀ (xs: List a) (size: Nat) (h: List.length xs < size): List.windows xs size = [] :=
  Eq.cong (count => List.windowsCount size count xs) (omega [h]: List.length xs + 1 - size = 0)

--| The windows are the suffixes cut to `size`, keeping those that are whole.
theorem List.windowsTails ∀ (xs: List a) (size: Nat):
    List.windows xs size = List.filter (List.map (List.tails xs) (.take size)) (window => window.length == size) :=
  match xs, size with
    | [], Zero => rfl
    | [], Succ size => List.windowsShort [] (Succ size) rfl
    | [x, ..rest], size =>
      if h: size ≤ List.length [x, ..rest] then
        calc List.windows [x, ..rest] size
          _ = [List.take [x, ..rest] size, ..List.windows rest size] := List.windowsCons x rest size h
          _ = [
              List.take [x, ..rest] size,
              ..List.filter (List.map (List.tails rest) (.take size)) (window => window.length == size)
            ] := Eq.cong (Cons (List.take [x, ..rest] size)) (List.windowsTails rest size)
          _ = List.filter (List.map (List.tails [x, ..rest]) (.take size)) (window => window.length == size) :=
            Eq.sym (List.filterKeep _ _ _ (rewrite List.lengthTake [x, ..rest] size h in DecEq.refl size))
      else
        calc List.windows [x, ..rest] size
          _ = [] := List.windowsShort [x, ..rest] size (omega [h])
          _ = List.windows rest size := Eq.sym (List.windowsShort rest size (omega [h]))
          _ = List.filter (List.map (List.tails rest) (.take size)) (window => window.length == size) :=
            List.windowsTails rest size
          _ = List.filter (List.map (List.tails [x, ..rest]) (.take size)) (window => window.length == size) :=
            Eq.sym
              (List.filterSkip
                (List.map (List.tails rest) (.take size))
                (window => window.length == size)
                (List.take [x, ..rest] size)
                (rewrite List.takeAll [x, ..rest] size (omega [h]) in
                  Decidable.toBoolOfNot _ (same => omega [same, h])))

theorem List.windowsExample: List.windows [1, 2, 3, 4] 3 = [[1, 2, 3], [2, 3, 4]] := rfl

--| Dropping n elements of a list at least n long leaves the rest.
theorem List.lengthDrop ∀ (xs: List a) (n: Nat)
    (h: n ≤ List.length xs):
    n + List.length (List.drop xs n) = List.length xs :=
  match xs, n with
    | xs, Zero => rfl
    | [x, ..xs], Succ n => Eq.cong Succ (List.lengthDrop xs n h)

theorem List.lengthDropExample: List.length (List.drop [1, 2, 3, 4, 5] 2) = 3 := rfl

theorem List.takeAppend ∀ (xs ys: List a): List.take (List.append xs ys) (List.length xs) = xs := match xs with
  | [] => rfl
  | [x, ..xs] => Eq.cong (Cons x) (List.takeAppend xs ys)

--| [`List.takeAppend`] and [`List.dropAppend`] at a count known to be the
--| first list's length.
theorem List.takeAppendLength ∀ (xs ys: List a) (k: Nat)
    (h: List.length xs = k):
    List.take (List.append xs ys) k = xs :=
  rewrite <- h in List.takeAppend xs ys

theorem List.dropAppendLength ∀ (xs ys: List a) (k: Nat)
    (h: List.length xs = k):
    List.drop (List.append xs ys) k = ys :=
  rewrite <- h in List.dropAppend xs ys

theorem List.headTake ∀ (xs: List a) (d: a) (k: Nat) (h: 1 ≤ k): List.headOr (List.take xs k) d = List.headOr xs d :=
  match xs, k with
    | [], Succ k => rfl
    | [x, ..xs], Succ k => rfl

--| `if b then x else 0` is `keepIf x b`.
theorem Nat.ifKeep ∀ (x: Nat) (b: Bool): (if b then x else 0) = Nat.keepIf x b := match b with
  | True => rfl
  | False => rfl

theorem List.sumByZero ∀ [auto add: Add c] (xs: List a): List.sumBy xs (x => Add.zero) = (Add.zero: c) := match xs with
  | [] => rfl
  | [x, ..xs] =>
    Eq.trans
      (List.sumByCons xs x (x => Add.zero))
      (Eq.trans (add.zeroAdd (List.sumBy xs (x => Add.zero))) (List.sumByZero xs))

theorem Nat.keepIfZero ∀ (b: Bool): Nat.keepIf 0 b = 0 := match b with
  | True => rfl
  | False => rfl

theorem Nat.keepIfOne ∀ (b: Bool): Nat.keepIf 1 b = Bool.toNat b := match b with
  | True => rfl
  | False => rfl

--| Keeping a sum is keeping each term.
theorem Nat.keepIfSumBy ∀ [g: a → Nat] [xs: List a] (b: Bool):
    Nat.keepIf (List.sumBy xs g) b = List.sumBy xs (x => Nat.keepIf (g x) b) :=
  match b with
    | True => rfl
    | False => Eq.sym (List.sumByZero [add := Nat.instAdd] xs)

--| `keepIf` as multiplying by 1 or 0.
theorem Nat.mulToNat ∀ (x: Nat) (a: Bool): x * Bool.toNat a = Nat.keepIf x a := match a with
  | True => ring
  | False => ring

theorem Nat.keepIfKeepIf ∀ (x: Nat) (a b: Bool): Nat.keepIf (Nat.keepIf x a) b = x * Bool.toNat (a ∧ b) :=
  match a, b with
    | True, True => ring
    | True, False => ring
    | False, True => ring
    | False, False => ring

theorem List.sumByAdd ∀ [auto add: Add c] (xs: List a) (f g: a → c):
    List.sumBy xs (x => f x + g x) = List.sumBy xs f + List.sumBy xs g :=
  match xs with
    | [] => Eq.sym (add.zeroAdd Add.zero)
    | [x, ..xs] =>
      Eq.trans
        (List.sumByCons xs x (y => f y + g y))
        (Eq.trans
          (Eq.cong (t => (f x + g x) + t) (List.sumByAdd xs f g))
          (Eq.trans
            (Add.addSwap (f x) (g x) (List.sumBy xs f) (List.sumBy xs g))
            (Eq.sym
              (Eq.trans
                (Eq.cong (t => t + List.sumBy [x, ..xs] g) (List.sumByCons xs x f))
                (Eq.cong (t => (f x + List.sumBy xs f) + t) (List.sumByCons xs x g))))))

--| A double sum of two terms is two double sums.
theorem List.sumByNestedAdd ∀ (xs: List a) (ys: List b) (f g: a → b → Nat):
    List.sumBy xs (x => List.sumBy ys (y => f x y + g x y))
      = List.sumBy xs (x => List.sumBy ys (y => f x y)) + List.sumBy xs (x => List.sumBy ys (y => g x y)) :=
  Eq.trans
    (List.sumByCong xs _ _ (x => List.sumByAdd ys (y => f x y) (y => g x y)))
    (List.sumByAdd xs (x => List.sumBy ys (y => f x y)) (x => List.sumBy ys (y => g x y)))

theorem List.sumBySwap ∀ [auto add: Add c] (ys: List b) (xs: List a) (h: a → b → c):
    List.sumBy xs (x => List.sumBy ys (y => h x y)) = List.sumBy ys (y => List.sumBy xs (x => h x y)) :=
  match xs with
    | [] => Eq.sym (List.sumByZero ys)
    | [x, ..xs] =>
      Eq.trans
        (List.sumByCons xs x (x => List.sumBy ys (y => h x y)))
        (Eq.trans
          (Eq.cong (t => List.sumBy ys (y => h x y) + t) (List.sumBySwap ys xs h))
          (Eq.trans
            (Eq.sym (List.sumByAdd ys (y => h x y) (y => List.sumBy xs (x => h x y))))
            (List.sumByCong ys (y => h x y + List.sumBy xs (x => h x y)) (y => List.sumBy [x, ..xs] (x => h x y)) (y =>
              Eq.sym (List.sumByCons xs x (x => h x y))))))

theorem List.sumByMap ∀ [auto add: Add c] (xs: List a) (g: b → c) (f: a → b):
    List.sumBy (List.map xs f) g = List.sumBy xs (x => g (f x)) :=
  match xs with
    | [] => rfl
    | [x, ..xs] =>
      Eq.trans
        (List.sumByCons (List.map xs f) (f x) g)
        (Eq.trans (Eq.cong (t => g (f x) + t) (List.sumByMap xs g f)) (Eq.sym (List.sumByCons xs x (x => g (f x)))))

--| Summing over a `flatMap` is summing the sums.
theorem List.sumByFlatMap ∀ [auto add: Add c] (xs: List a) (f: b → c) (g: a → List b):
    List.sumBy (List.flatMap xs g) f = List.sumBy xs (x => List.sumBy (g x) f) :=
  match xs with
    | [] => rfl
    | [x, ..xs] =>
      Eq.trans
        (List.sumByAppend (g x) (List.flatMap xs g) f)
        (Eq.trans
          (Eq.cong (t => List.sumBy (g x) f + t) (List.sumByFlatMap xs f g))
          (Eq.sym (List.sumByCons xs x (x => List.sumBy (g x) f))))

--| Summing over a `filter` is summing the terms that pass, the rest counting 0.
theorem List.sumByFilter ∀ [auto add: Add c] (xs: List a) (f: a → c) (p: a → Bool):
    List.sumBy (List.filter xs p) f = List.sumBy xs (x => if p x then f x else Add.zero) :=
  match xs with
    | [] => rfl
    | [x, ..xs] =>
      Bool.inspect
        (p x)
        (b => List.sumBy (List.filter [x, ..xs] p) f = List.sumBy [x, ..xs] (x => if p x then f x else Add.zero))
        (h =>
          calc List.sumBy (List.filter [x, ..xs] p) f
            _ = List.sumBy [x, ..List.filter xs p] f := Eq.cong (.sumBy f) (List.filterKeep xs p x h)
            _ = f x + List.sumBy (List.filter xs p) f := List.sumByCons (List.filter xs p) x f
            _ = f x + List.sumBy xs (x => if p x then f x else Add.zero) :=
              Eq.cong (t => f x + t) (List.sumByFilter xs f p)
            _ = (if p x then f x else Add.zero) + List.sumBy xs (x => if p x then f x else Add.zero) := rewrite h
            _ = List.sumBy [x, ..xs] (x => if p x then f x else Add.zero) :=
              Eq.sym (List.sumByCons xs x (x => if p x then f x else Add.zero)))
        (h =>
          calc List.sumBy (List.filter [x, ..xs] p) f
            _ = List.sumBy (List.filter xs p) f := Eq.cong (.sumBy f) (List.filterSkip xs p x h)
            _ = List.sumBy xs (x => if p x then f x else Add.zero) := List.sumByFilter xs f p
            _ = Add.zero + List.sumBy xs (x => if p x then f x else Add.zero) :=
              Eq.sym (add.zeroAdd (List.sumBy xs (x => if p x then f x else Add.zero)))
            _ = (if p x then f x else Add.zero) + List.sumBy xs (x => if p x then f x else Add.zero) := rewrite h
            _ = List.sumBy [x, ..xs] (x => if p x then f x else Add.zero) :=
              Eq.sym (List.sumByCons xs x (x => if p x then f x else Add.zero)))

theorem List.sumFilter ∀ (xs: List Nat) (p: Nat → Bool):
    List.sum (List.filter xs p) = List.sumBy xs (x => Nat.keepIf x (p x)) :=
  match xs with
    | [] => rfl
    | [x, ..xs] =>
      Bool.inspect
        (p x)
        (c => List.sum (List.filter [x, ..xs] p) = List.sumBy [x, ..xs] (x => Nat.keepIf x (p x)))
        (h =>
          Eq.trans
            (Eq.cong List.sum (List.filterKeep xs p x h))
            (Eq.trans
              (List.sumCons x (List.filter xs p))
              (Eq.trans
                (Eq.cong (t => Nat.keepIf x t + List.sum (List.filter xs p)) (Eq.sym h))
                (Eq.trans
                  (Eq.cong (t => Nat.keepIf x (p x) + t) (List.sumFilter xs p))
                  (Eq.sym (List.sumByCons xs x (x => Nat.keepIf x (p x))))))))
        (h =>
          Eq.trans
            (Eq.cong List.sum (List.filterSkip xs p x h))
            (Eq.trans
              (Eq.cong (t => Nat.keepIf x t + List.sum (List.filter xs p)) (Eq.sym h))
              (Eq.trans
                (Eq.cong (t => Nat.keepIf x (p x) + t) (List.sumFilter xs p))
                (Eq.sym (List.sumByCons xs x (x => Nat.keepIf x (p x)))))))

--| Sums over a run of numbers that pick nothing, or pick one.
theorem List.sumRangeFromNone ∀ (q: Nat → Bool) (g: Nat → Nat) (c s: Nat)
    (h: ∀ (b: Nat) => s ≤ b → b < s + c → q b = False):
    List.sumBy (List.rangeFrom c s) (b => Nat.keepIf (g b) (q b)) = 0 :=
  match c with
    | Zero => rfl
    | Succ c =>
      Eq.trans
        (List.sumByCons (List.rangeFrom c (Succ s)) s (b => Nat.keepIf (g b) (q b)))
        (Eq.trans
          (Eq.cong
            (t => Nat.keepIf (g s) t + List.sumBy (List.rangeFrom c (Succ s)) (b => Nat.keepIf (g b) (q b)))
            (h s (Nat.leRefl s) (Nat.ltAddSuccSelf s c)))
          (List.sumRangeFromNone q g c (Succ s) (b hb1 hb2 =>
            h b (Nat.leTrans s (Succ s) b (Nat.leSucc s) hb1) (Nat.ltAddSucc s c b hb2))))

--| Past the one number `q` picks, `q` picks nothing.
theorem List.sumRangeFromOneApart ∀ (q: Nat → Bool) (v: Nat)
    (uniq: ∀ (b: Nat) => q b = True → b = v) (s: Nat)
    (hs: q s = True) (b: Nat)
    (hb: Succ s ≤ b):
    q b = False :=
  Bool.inspect
    (q b)
    (u => u = False)
    (t => Void.exfalso (Nat.lessIrrefl s (Nat.leCongRight (Succ s) b s (Eq.trans (uniq b t) (Eq.sym (uniq s hs))) hb)))
    (f => rfl)

theorem List.sumRangeFromOne ∀ (q: Nat → Bool) (g: Nat → Nat) (v: Nat)
    (hv: q v = True)
    (uniq: ∀ (b: Nat) => q b = True → b = v) (c s: Nat)
    (h1: s ≤ v)
    (h2: v < s + c):
    List.sumBy (List.rangeFrom c s) (b => Nat.keepIf (g b) (q b)) = g v :=
  match c with
    | Zero => Void.exfalso (Nat.lessIrrefl v (Nat.leTrans (Succ v) s v (Nat.ltCongRight v (s + 0) s ring h2) h1))
    | Succ c =>
      Bool.inspect
        (q s)
        (u => List.sumBy (List.rangeFrom (Succ c) s) (b => Nat.keepIf (g b) (q b)) = g v)
        (hs =>
          calc List.sumBy (List.rangeFrom (Succ c) s) (b => Nat.keepIf (g b) (q b))
            _ = Nat.keepIf (g s) (q s) + List.sumBy (List.rangeFrom c (Succ s)) (b => Nat.keepIf (g b) (q b)) :=
              List.sumByCons (List.rangeFrom c (Succ s)) s (b => Nat.keepIf (g b) (q b))
            _ = g s + List.sumBy (List.rangeFrom c (Succ s)) (b => Nat.keepIf (g b) (q b)) := rewrite hs
            _ = g s + 0 :=
              Eq.cong
                (t => g s + t)
                (List.sumRangeFromNone q g c (Succ s) (b hb1 hb2 => List.sumRangeFromOneApart q v uniq s hs b hb1))
            _ = g s := Nat.addZero (g s)
            _ = g v := Eq.cong g (uniq s hs))
        (hs =>
          calc List.sumBy (List.rangeFrom (Succ c) s) (b => Nat.keepIf (g b) (q b))
            _ = Nat.keepIf (g s) (q s) + List.sumBy (List.rangeFrom c (Succ s)) (b => Nat.keepIf (g b) (q b)) :=
              List.sumByCons (List.rangeFrom c (Succ s)) s (b => Nat.keepIf (g b) (q b))
            _ = List.sumBy (List.rangeFrom c (Succ s)) (b => Nat.keepIf (g b) (q b)) := rewrite hs
            _ = g v :=
              List.sumRangeFromOne q g v hv uniq c
                (Succ s)
                (Nat.leNeSucc s v h1 (e =>
                  Bool.trueNotFalse (Eq.trans (Eq.sym hv) (Eq.trans (Eq.cong q (Eq.sym e)) hs))))
                (Nat.ltSuccAdd s c v h2))

--| A sum over a run of numbers that is 0 has every term 0.
theorem List.sumRangeFromZero ∀ (f: Nat → Nat):
    ∀ (c s: Nat) => List.sumBy (List.rangeFrom c s) f = 0 → ∀ (x: Nat) => s ≤ x → x < s + c → f x = 0
  | Zero, s, h, x, h1, h2 =>
    Void.exfalso (Nat.lessIrrefl x (Nat.leTrans (Succ x) s x (Nat.ltCongRight x (s + 0) s ring h2) h1))
  | Succ c, s, h, x, h1, h2 =>
    let parts :=
      Nat.addEqZero
        (f s)
        (List.sumBy (List.rangeFrom c (Succ s)) f)
        (Eq.trans (Eq.sym (List.sumByCons (List.rangeFrom c (Succ s)) s f)) h)
    match e: Nat.equal s x with
      | True => rewrite <- e.read in And.left parts
      | False =>
        List.sumRangeFromZero f c
          (Succ s)
          (And.right parts)
          x
          (Nat.leNeSucc s x h1 (Nat.equalFalse s x e))
          (Nat.ltSuccAdd s c x h2)

--| Sums over the ids of a run that pick out `y`.
theorem List.sumRangeFromEq ∀ (y c s: Nat)
    (h1: s ≤ y)
    (h2: y < s + c):
    List.sumBy (List.rangeFrom c s) (x => Nat.keepIf x (y == x)) = y :=
  List.sumRangeFromOne (x => y == x) (x => x) y ((Nat.decEq y y).complete rfl) (b h => Eq.sym h.read) c s h1 h2

theorem List.sumRangeFromEqNone ∀ (y c s: Nat)
    (h: ∀ (x: Nat) => s ≤ x → x < s + c → y ≠ x):
    List.sumBy (List.rangeFrom c s) (x => Nat.keepIf x (y == x)) = 0 :=
  List.sumRangeFromNone (x => y == x) (x => x) c s (b h1 h2 => Decidable.toBoolOfNot (Nat.decEq y b) (h b h1 h2))

--| A sum over 0, 1, …, n - 1 that picks out `v`: `g v`, which must be 0
--| when `v` is past the end.
theorem List.sumRangePick ∀ (g: Nat → Nat) (n v: Nat)
    (hz: n ≤ v → g v = 0):
    List.sumBy (List.range 0 n) (x => Nat.keepIf (g x) (Nat.equal v x)) = g v :=
  match e: Nat.leq (Succ v) n with
    | True =>
      List.sumRangeFromOne (x => Nat.equal v x) g v (Nat.equalRefl v) (b h => Eq.sym h.read) n 0 (Nat.zeroLe v) e
    | False =>
      rewrite hz e.read in
        List.sumRangeFromNone (x => Nat.equal v x) g n 0 (b h1 h2 =>
          Nat.equalOfLess b v (Nat.leTrans (Succ b) n v h2 e.read))

--| Sums over a range that pick nothing, or pick one.
theorem List.sumRangeNone ∀ (q: Nat → Bool) (g: Nat → Nat) (from until: Nat)
    (h: ∀ (x: Nat) => from ≤ x → x < until → q x = False):
    List.sumBy (List.range from until) (x => Nat.keepIf (g x) (q x)) = 0 :=
  List.sumRangeFromNone q g (until - from) from (x low high => h x low (omega))

theorem List.sumRangeOne ∀ (q: Nat → Bool) (g: Nat → Nat) (v: Nat)
    (hv: q v = True)
    (uniq: ∀ (x: Nat) => q x = True → x = v) (from until: Nat)
    (low: from ≤ v)
    (high: v < until):
    List.sumBy (List.range from until) (x => Nat.keepIf (g x) (q x)) = g v :=
  List.sumRangeFromOne q g v hv uniq (until - from) from low (omega)

--| A sum over a range that is 0 has every term 0.
theorem List.sumRangeZero ∀ (f: Nat → Nat) (from until: Nat)
    (h: List.sumBy (List.range from until) f = 0) (x: Nat)
    (low: from ≤ x)
    (high: x < until):
    f x = 0 :=
  List.sumRangeFromZero f (until - from) from h x low (omega)

--| Sums over a range that pick out `y`.
theorem List.sumRangeEq ∀ (y from until: Nat)
    (low: from ≤ y)
    (high: y < until):
    List.sumBy (List.range from until) (x => Nat.keepIf x (y == x)) = y :=
  List.sumRangeFromEq y (until - from) from low (omega)

theorem List.sumRangeEqNone ∀ (y from until: Nat)
    (h: ∀ (x: Nat) => from ≤ x → x < until → y ≠ x):
    List.sumBy (List.range from until) (x => Nat.keepIf x (y == x)) = 0 :=
  List.sumRangeFromEqNone y (until - from) from (x low high => h x low (omega))

--| The numbers of `List.rangeFrom c s` are in order.
theorem List.sortedRangeFrom ∀ (c s: Nat): List.Sorted Nat.leq (List.rangeFrom c s) := match c with
  | Zero => Trivial
  | Succ Zero => Both Trivial Trivial
  | Succ (Succ c) => Both (Nat.leSucc s) (List.sortedRangeFrom (Succ c) (Succ s))

--| A range is in order.
theorem List.sortedRange ∀ (from until: Nat): List.Sorted Nat.leq (List.range from until) :=
  List.sortedRangeFrom (until - from) from

--| `any` over a run of numbers: a witness out, a witness in.
theorem List.anyRangeElim ∀ (q: Nat → Bool) (goal: Prop):
    ∀ (c s: Nat) => List.any (List.rangeFrom c s) q = True
      → ∀ (cont: ∀ (k: Nat) => s ≤ k → k < s + c → q k = True → goal) => goal
  | Zero, s, h, k => cases
  | Succ c, s, h, k => Bool.inspect (q s) (u => goal) (t => k s (Nat.leRefl s) (Nat.ltAddSuccSelf s c) t) (f =>
    List.anyRangeElim q goal c
      (Succ s)
      (Eq.trans
        (Eq.cong (b => Bool.ifThenElse b (u => True) (u => List.any (List.rangeFrom c (Succ s)) q)) (Eq.sym f))
        h)
      (j h1 h2 hj => k j (Nat.leTrans s (Succ s) j (Nat.leSucc s) h1) (Nat.ltAddSucc s c j h2) hj))

theorem List.anyRangeIntro ∀ (q: Nat → Bool) (c s k: Nat)
    (h1: s ≤ k)
    (h2: k < s + c)
    (hk: q k = True):
    List.any (List.rangeFrom c s) q = True :=
  match c with
    | Zero => Void.exfalso (Nat.lessIrrefl k (Nat.leTrans (Succ k) s k (Nat.ltCongRight k (s + 0) s ring h2) h1))
    | Succ c =>
      Bool.inspect
        (q s)
        (u => List.any (List.rangeFrom (Succ c) s) q = True)
        (t => Eq.cong (b => Bool.ifThenElse b (u => True) (u => List.any (List.rangeFrom c (Succ s)) q)) t)
        (f =>
          Eq.trans
            (Eq.cong (b => Bool.ifThenElse b (u => True) (u => List.any (List.rangeFrom c (Succ s)) q)) f)
            (List.anyRangeIntro q c
              (Succ s)
              k
              (Nat.leNeSucc s k h1 (e => Bool.trueNotFalse (Eq.trans (Eq.sym hk) (Eq.trans (Eq.cong q (Eq.sym e)) f))))
              (Nat.ltSuccAdd s c k h2)
              hk))

--| `all` over a run of numbers: each element passes, and back. With a check
--| that computes to `True`, the first turns a finite computation into a fact
--| about every number of the run.
theorem List.allRangeElim ∀ (q: Nat → Bool):
    ∀ (c s: Nat) => List.all (List.rangeFrom c s) q = True → ∀ (k: Nat) => s ≤ k → k < s + c → q k = True
  | Zero, s, h, k, h1, h2 =>
    Void.exfalso (Nat.lessIrrefl k (Nat.leTrans (Succ k) s k (Nat.ltCongRight k (s + 0) s ring h2) h1))
  | Succ c, s, h, k, h1, h2 =>
    Bool.inspect
      (q s)
      (u => q k = True)
      (t =>
        Bool.inspect (k == s) (u => q k = True) (e => rewrite <- e.read at t) (ne =>
          List.allRangeElim q c
            (Succ s)
            (Eq.trans
              (Eq.cong (b => Bool.ifThenElse b (u => List.all (List.rangeFrom c (Succ s)) q) (u => False)) (Eq.sym t))
              h)
            k
            (Nat.leNeSucc s k h1 (e => Bool.trueNotFalse (Eq.trans (Eq.sym ((Nat.decEq k s).complete (Eq.sym e))) ne)))
            (Nat.ltSuccAdd s c k h2)))
      (f => cases)

theorem List.allRangeIntro ∀ (q: Nat → Bool) (c s: Nat)
    (h: ∀ (k: Nat) => s ≤ k → k < s + c → q k = True):
    List.all (List.rangeFrom c s) q = True :=
  match c with
    | Zero => rfl
    | Succ c =>
      Eq.trans
        (Eq.cong
          (b => Bool.ifThenElse b (u => List.all (List.rangeFrom c (Succ s)) q) (u => False))
          (h s (Nat.leRefl s) (Nat.ltAddSuccSelf s c)))
        (List.allRangeIntro q c (Succ s) (k h1 h2 =>
          h k (Nat.leTrans s (Succ s) k (Nat.leSucc s) h1) (Nat.ltAddSucc s c k h2)))

theorem List.allRangeExample: List.all (List.rangeFrom 100 0) (k => k * k ≠ 2) = True := rfl

theorem Nat.firstFromExample: Nat.firstFrom (k => Nat.leq 11 (k * k)) 9 1 = 4 := rfl

theorem Nat.firstFromStop ∀ (q: Nat → Bool) (c s: Nat) (h: q s = True): Nat.firstFrom q (Succ c) s = s :=
  Eq.cong (b => Bool.ifThenElse b (u => s) (u => Nat.firstFrom q c (Succ s))) h

theorem Nat.firstFromSkip ∀ (q: Nat → Bool) (c s: Nat)
    (h: q s = False):
    Nat.firstFrom q (Succ c) s = Nat.firstFrom q c (Succ s) :=
  Eq.cong (b => Bool.ifThenElse b (u => s) (u => Nat.firstFrom q c (Succ s))) h

theorem Nat.firstFromAtLeast ∀ (q: Nat → Bool) (c s: Nat): s ≤ Nat.firstFrom q c s := match c with
  | Zero => Nat.leRefl s
  | Succ c =>
    Bool.inspect
      (q s)
      (u => s ≤ Nat.firstFrom q (Succ c) s)
      (t => J (z p => s ≤ z) (Nat.leRefl s) (Eq.sym (Nat.firstFromStop q c s t)))
      (f =>
        rewrite <- Nat.firstFromSkip q c s f at Nat.leTrans s
          (Succ s)
          (Nat.firstFrom q c (Succ s))
          (Nat.leSucc s)
          (Nat.firstFromAtLeast q c (Succ s)))

theorem Nat.firstFromBefore ∀ (q: Nat → Bool) (c s j: Nat) (h1: s ≤ j) (h2: j < Nat.firstFrom q c s): q j = False :=
  match c with
    | Zero => Void.exfalso (Nat.lessIrrefl j (Nat.leTrans (Succ j) s j h2 h1))
    | Succ c =>
      Bool.inspect
        (q s)
        (u => q j = False)
        (t =>
          Void.exfalso
            (Nat.lessIrrefl j
              (Nat.leTrans
                (Succ j)
                s
                j
                (Nat.ltCongRight j (Nat.firstFrom q (Succ c) s) s (Nat.firstFromStop q c s t) h2)
                h1)))
        (f =>
          Bool.inspect (j == s) (u => q j = False) (e => rewrite <- e.read at f) (ne =>
            Nat.firstFromBefore q c
              (Succ s)
              j
              (Nat.leNeSucc s j h1 (e =>
                Bool.trueNotFalse (Eq.trans (Eq.sym ((Nat.decEq j s).complete (Eq.sym e))) ne)))
              (Nat.ltCongRight j
                (Nat.firstFrom q (Succ c) s)
                (Nat.firstFrom q c (Succ s))
                (Nat.firstFromSkip q c s f)
                h2)))

theorem Nat.firstFromFound ∀ (q: Nat → Bool) (c s k: Nat)
    (h1: s ≤ k)
    (h2: k < s + c)
    (hk: q k = True):
    q (Nat.firstFrom q c s) = True :=
  match c with
    | Zero => Void.exfalso (Nat.lessIrrefl k (Nat.leTrans (Succ k) s k (Nat.ltCongRight k (s + 0) s ring h2) h1))
    | Succ c =>
      Bool.inspect
        (q s)
        (u => q (Nat.firstFrom q (Succ c) s) = True)
        (t => rewrite <- Nat.firstFromStop q c s t at t)
        (f =>
          rewrite <- Nat.firstFromSkip q c s f at Nat.firstFromFound q c
            (Succ s)
            k
            (Nat.leNeSucc s k h1 (e => Bool.trueNotFalse (Eq.trans (Eq.sym hk) (Eq.trans (Eq.cong q (Eq.sym e)) f))))
            (Nat.ltSuccAdd s c k h2)
            hk)

theorem Nat.firstFromLe ∀ (q: Nat → Bool) (c s k: Nat) (h1: s ≤ k) (hk: q k = True): Nat.firstFrom q c s ≤ k :=
  match e: Nat.leq (Nat.firstFrom q c s) k with
    | True => rfl
    | False => Void.exfalso (Bool.trueNotFalse (Eq.trans (Eq.sym hk) (Nat.firstFromBefore q c s k h1 e.read)))

--| Sums that agree on the elements passing a check `all` says they all pass.
theorem List.sumByCongAll ∀ (p: a → Bool) (f g: a → Nat)
    (h: ∀ (x: a) => p x = True → f x = g x) (xs: List a)
    (ok: List.all xs p = True):
    List.sumBy xs f = List.sumBy xs g :=
  match xs with
    | [] => rfl
    | [x, ..xs] =>
      Eq.trans
        (List.sumByCons xs x f)
        (Eq.trans
          (Eq.cong (t => t + List.sumBy xs f) (h x ok.left))
          (Eq.trans (Eq.cong (t => g x + t) (List.sumByCongAll p f g h xs ok.right)) (Eq.sym (List.sumByCons xs x g))))

theorem Ordering.isLessEqIf ∀ (d: Bool): Ordering.isLessEq (if d then Less else Greater) = d := match d with
  | True => rfl
  | False => rfl

--| `Nat.compare` agrees with `<=`, so `List.sortBy` with it is total.
theorem Nat.compareLeq ∀ (m n: Nat): Ordering.isLessEq (Nat.compare m n) = Nat.leq m n :=
  Bool.inspect
    (Nat.equal m n)
    (c => Ordering.isLessEq (if c then Equal else (if Nat.leq m n then Less else Greater)) = Nat.leq m n)
    (e => Eq.sym (Nat.leCongRight m m n e.read (Nat.leRefl m)))
    (e => Ordering.isLessEqIf (Nat.leq m n))

theorem Nat.compareTotal ∀ (m n: Nat)
    (h: Ordering.isLessEq (Nat.compare m n) = False):
    Ordering.isLessEq (Nat.compare n m) = True :=
  Eq.trans (Nat.compareLeq n m) (Nat.leqTotal m n (Eq.trans (Eq.sym (Nat.compareLeq m n)) h))

--| The correctness proofs need only that `le` is total: `tot` below.
theorem List.mergeLeHead ∀ (le: a → a → Bool) (z: a) (xs ys: List a)
    (hx: List.LeHead le z xs)
    (hy: List.LeHead le z ys):
    List.LeHead le z (List.merge le xs ys) :=
  match xs, ys with
    | [], ys => hy
    | [x, ..xs], [] => hx
    | [x, ..xs], [y, ..ys] =>
      Bool.inspect
        (le x y)
        (c => List.LeHead le z (if c then [x, ..List.merge le xs [y, ..ys]] else [y, ..List.merge le [x, ..xs] ys]))
        (e => hx)
        (e => hy)

theorem List.mergeSorted ∀ (le: a → a → Bool)
    (tot: ∀ (x y: a) => le x y = False → le y x = True) (xs ys: List a)
    (sx: List.Sorted le xs)
    (sy: List.Sorted le ys):
    List.Sorted le (List.merge le xs ys) :=
  match xs, ys, sx, sy with
    | [], ys, sx, sy => sy
    | [x, ..xs], [], sx, sy => sx
    | [x, ..xs], [y, ..ys], Both hx sxs, Both hy sys =>
      Bool.inspect
        (le x y)
        (c => List.Sorted le (if c then [x, ..List.merge le xs [y, ..ys]] else [y, ..List.merge le [x, ..xs] ys]))
        (e => Both (List.mergeLeHead le x xs [y, ..ys] hx e) (List.mergeSorted le tot xs [y, ..ys] sxs (Both hy sys)))
        (e =>
          Both
            (List.mergeLeHead le y [x, ..xs] ys (tot x y e) hy)
            (List.mergeSorted le tot [x, ..xs] ys (Both hx sxs) sys))

--| Every run in the counter is sorted.
@[noReceiver]
def List.RunsSorted (le: a → a → Bool): (runs: List (Option (List a))) → Prop
  | [] => Unit
  | [None, ..rest] => List.RunsSorted le rest
  | [Some r, ..rest] => (List.Sorted le r) ∧ (List.RunsSorted le rest)

theorem List.pushRunSorted ∀ (le: a → a → Bool)
    (tot: ∀ (x y: a) => le x y = False → le y x = True)
    (run: List a) (c: List (Option (List a)))
    (s: List.Sorted le run)
    (h1: List.RunsSorted le c):
    List.RunsSorted le (List.pushRun le run c) :=
  match c, h1 with
    | [], h => Both s Trivial
    | [None, ..rest], h => Both s h
    | [Some r, ..rest], Both sr h =>
      List.pushRunSorted le tot (List.merge le r run) rest (List.mergeSorted le tot r run sr s) h

theorem List.buildRunsSorted ∀ (le: a → a → Bool)
    (tot: ∀ (x y: a) => le x y = False → le y x = True)
    (c: List (Option (List a))) (xs: List a)
    (h: List.RunsSorted le c):
    List.RunsSorted le (List.buildRuns le c xs) :=
  match xs with
    | [] => h
    | [x, ..xs] =>
      List.buildRunsSorted le tot (List.pushRun le [x] c) xs (List.pushRunSorted le tot [x] c (Both Trivial Trivial) h)

theorem List.mergeRunsSorted ∀ (le: a → a → Bool)
    (tot: ∀ (x y: a) => le x y = False → le y x = True)
    (acc: List a) (c: List (Option (List a)))
    (s: List.Sorted le acc)
    (h1: List.RunsSorted le c):
    List.Sorted le (List.mergeRuns le acc c) :=
  match c, h1 with
    | [], h => s
    | [None, ..rest], h => List.mergeRunsSorted le tot acc rest s h
    | [Some r, ..rest], Both sr h =>
      List.mergeRunsSorted le tot (List.merge le r acc) rest (List.mergeSorted le tot r acc sr s) h

theorem List.sortWithSorted ∀ (le: a → a → Bool)
    (tot: ∀ (x y: a) => le x y = False → le y x = True) (xs: List a):
    List.Sorted le (List.sortWith xs le) :=
  List.mergeRunsSorted le tot [] (List.buildRuns le [] xs) Trivial (List.buildRunsSorted le tot [] xs Trivial)

theorem List.sortBySorted ∀ (cmp: a → a → Ordering)
    (tot: ∀ (x y: a) => Ordering.isLessEq (cmp x y) = False → Ordering.isLessEq (cmp y x) = True) (xs: List a):
    List.Sorted (x y => Ordering.isLessEq (cmp x y)) (List.sortBy xs cmp) :=
  List.sortWithSorted (x y => Ordering.isLessEq (cmp x y)) tot xs

--| If `o` isn't `Less` or `Equal`, its opposite is.
theorem Ordering.flipNotLessEq ∀ (o: Ordering)
    (h: Ordering.isLessEq o = False):
    Ordering.isLessEq (Ordering.flip o) = True :=
  match o with | Greater => rfl

--| An `Ord`'s comparison is total, by its `flip` law.
-- (§7.6)
theorem Ord.leTotal ∀ [auto ord: Ord a] (x y: a)
    (h: Ordering.isLessEq (Ord.compare x y) = False):
    Ordering.isLessEq (Ord.compare y x) = True :=
  rewrite ord.flip x y in Ordering.flipNotLessEq (Ord.compare x y) h

theorem List.sortSorted ∀ [auto ord: Ord a] (xs: List a):
    List.Sorted (x y => Ordering.isLessEq (Ord.compare x y)) (List.sort xs) :=
  List.sortBySorted Ord.compare Ord.leTotal xs

--| `isLessEq` is "not `Greater`".
theorem Ordering.notGreaterOfIsLessEq ∀ (c: Ordering) (h: Ordering.isLessEq c = True): c ≠ Greater := e =>
  Bool.falseNotTrue (rewrite e at h)

theorem Ordering.isLessEqOfNotGreater ∀ (c: Ordering) (n: c ≠ Greater): Ordering.isLessEq c = True := match c with
  | Less => rfl
  | Equal => rfl
  | Greater => Void.exfalso (n rfl)

--| The test `List.sort` sorts by is transitive, and holds both ways round
--| only for equal values, by the `Ord`'s laws.
theorem Ord.isLessEqTrans ∀ [auto ord: Ord a] (x y z: a)
    (h1: Ordering.isLessEq (Ord.compare x y) = True)
    (h2: Ordering.isLessEq (Ord.compare y z) = True):
    Ordering.isLessEq (Ord.compare x z) = True :=
  Ordering.isLessEqOfNotGreater
    (Ord.compare x z)
    (Ordering.notGreaterTrans
      (Ord.compare x y)
      (Ord.compare y z)
      (Ord.compare x z)
      (ord.trans x y z)
      (e => Eq.cong (w => Ord.compare w z) (ord.equal x y e))
      (e => Eq.sym (Eq.cong (w => Ord.compare x w) (ord.equal y z e)))
      (Ordering.notGreaterOfIsLessEq (Ord.compare x y) h1)
      (Ordering.notGreaterOfIsLessEq (Ord.compare y z) h2))

theorem Ord.isLessEqAntisymm ∀ [auto ord: Ord a] (x y: a)
    (h1: Ordering.isLessEq (Ord.compare x y) = True)
    (h2: Ordering.isLessEq (Ord.compare y x) = True):
    x = y :=
  match e: Ord.compare x y with
    | Equal => ord.equal x y e
    | Less => Void.exfalso (Bool.falseNotTrue (rewrite ord.flip x y, e at h2))

--| Sorted by one test is sorted by another that agrees with it.
theorem List.leHeadCong ∀ (le1 le2: a → a → Bool)
    (h: ∀ (x y: a) => le1 x y = le2 x y)
    (z: a) (xs: List a)
    (p: List.LeHead le1 z xs):
    List.LeHead le2 z xs :=
  match xs with
    | [] => p
    | [y, ..ys] => Eq.trans (Eq.sym (h z y)) p

theorem List.sortedCong ∀ (le1 le2: a → a → Bool)
    (h: ∀ (x y: a) => le1 x y = le2 x y) (xs: List a)
    (h1: List.Sorted le1 xs):
    List.Sorted le2 xs :=
  match xs, h1 with
    | [], p => p
    | [x, ..xs], Both p q => Both (List.leHeadCong le1 le2 h x xs p) (List.sortedCong le1 le2 h xs q)

--| `Sorted le xs` is `xs.chain le = True`, both ways.
theorem List.sortedOfChain ∀ (le: a → a → Bool) (xs: List a) (chained: List.chain xs le = True): List.Sorted le xs :=
  match xs with
    | [] => Trivial
    | [x] => Both Trivial Trivial
    | [x, next, ..rest] =>
      let Both first more := chained
      Both first (List.sortedOfChain le [next, ..rest] more)

theorem List.chainOfSorted ∀ (le: a → a → Bool) (xs: List a) (h: List.Sorted le xs): List.chain xs le = True :=
  match xs, h with
    | [], sorted => rfl
    | [x], sorted => rfl
    | [x, next, ..rest], Both first sorted => Both first (List.chainOfSorted le [next, ..rest] sorted)

--| For numbers, that's `Nat.leq`.
theorem List.sortSortedNat ∀ (xs: List Nat): List.Sorted Nat.leq (List.sort xs) :=
  List.sortedCong
    (x y => Ordering.isLessEq (Nat.compare x y))
    Nat.leq
    Nat.compareLeq
    (List.sort [ord := Nat.instOrd] xs)
    (List.sortSorted [ord := Nat.instOrd] xs)

--| The front and the back of a sorted list are sorted.
-- (SW-363)
theorem List.sortedPrefix ∀ (le: a → a → Bool) (xs ys: List a)
    (h: List.Sorted le (List.append xs ys)):
    List.Sorted le xs :=
  match xs, h with
    | [], s => Trivial
    | [x], s => Both Trivial Trivial
    | [x, y, ..zs], Both hx s => Both hx (List.sortedPrefix le [y, ..zs] ys s)

theorem List.sortedSuffix ∀ (le: a → a → Bool) (xs ys: List a)
    (h: List.Sorted le (List.append xs ys)):
    List.Sorted le ys :=
  match xs, h with
    | [], s => s
    | [x, ..xs], Both hx s => List.sortedSuffix le xs ys s

--| For a transitive `le`, the first element of a sorted list may come before
--| every later one.
theorem List.sortedHeadLe ∀ (le: a → a → Bool)
    (trans: ∀ (x y z: a) => le x y = True → le y z = True → le x z = True)
    (x z: a) (rest: List a)
    (h: List.Sorted le [x, ..rest])
    (h1: List.Mem z rest):
    le x z = True :=
  match rest, h, h1 with
    | [], s, m => Void.exfalso m
    | [y, ..ys], Both hxy s, Inl e => rewrite <- e in hxy
    | [y, ..ys], Both hxy s, Inr m => trans x y z hxy (List.sortedHeadLe le trans y z ys s m)

--| For a transitive `le`, sorted is pairwise.
theorem List.pairwiseOfSorted ∀ (le: a → a → Bool)
    (trans: ∀ (x y z: a) => le x y = True → le y z = True → le x z = True) (xs: List a)
    (h: List.Sorted le xs):
    List.Pairwise (x y => le x y = True) xs :=
  match xs, h with
    | [], s => Trivial
    | [x, ..rest], Both hx s =>
      Both
        (List.allOfMem (y => le x y = True) rest (z m => List.sortedHeadLe le trans x z rest (Both hx s) m))
        (List.pairwiseOfSorted le trans rest s)

--| Merging keeps a property every element of both lists has.
-- Sorting a list whose elements all pass `p` needs `le` total only on the
-- values that pass `p`, not on every value: doubles other than the NaN under
-- `Float.ieeeLe`, say (`examples/accept/sort-on-subset.sw`).
-- Merging and the sort's runs keep every element passing, so every
-- comparison the sort makes is between two of them.
theorem List.mergeAll ∀ (le: a → a → Bool) (p: a → Prop) (xs ys: List a)
    (h: List.All p xs)
    (h1: List.All p ys):
    List.All p (List.merge le xs ys) :=
  match xs, ys, h, h1 with
    | [], ys, ax, ay => ay
    | [x, ..xs], [], ax, ay => ax
    | [x, ..xs], [y, ..ys], Both px ax, Both py ay =>
      Bool.inspect
        (le x y)
        (c => List.All p (if c then [x, ..List.merge le xs [y, ..ys]] else [y, ..List.merge le [x, ..xs] ys]))
        (e => Both px (List.mergeAll le p xs [y, ..ys] ax (Both py ay)))
        (e => Both py (List.mergeAll le p [x, ..xs] ys (Both px ax) ay))

theorem List.mergeSortedOn ∀ (le: a → a → Bool) (p: a → Prop)
    (tot: ∀ (x y: a) => p x → p y → le x y = False → le y x = True) (xs ys: List a)
    (h: List.All p xs)
    (h1: List.All p ys)
    (sx: List.Sorted le xs)
    (sy: List.Sorted le ys):
    List.Sorted le (List.merge le xs ys) :=
  match xs, ys, h, h1, sx, sy with
    | [], ys, ax, ay, sx, sy => sy
    | [x, ..xs], [], ax, ay, sx, sy => sx
    | [x, ..xs], [y, ..ys], Both px ax, Both py ay, Both hx sxs, Both hy sys =>
      Bool.inspect
        (le x y)
        (c => List.Sorted le (if c then [x, ..List.merge le xs [y, ..ys]] else [y, ..List.merge le [x, ..xs] ys]))
        (e =>
          Both
            (List.mergeLeHead le x xs [y, ..ys] hx e)
            (List.mergeSortedOn le p tot xs [y, ..ys] ax (Both py ay) sxs (Both hy sys)))
        (e =>
          Both
            (List.mergeLeHead le y [x, ..xs] ys (tot x y px py e) hy)
            (List.mergeSortedOn le p tot [x, ..xs] ys (Both px ax) ay (Both hx sxs) sys))

--| Every run in the counter passes `p`.
@[noReceiver]
def List.RunsAll (p: a → Prop): (runs: List (Option (List a))) → Prop
  | [] => Unit
  | [None, ..rest] => List.RunsAll p rest
  | [Some r, ..rest] => (List.All p r) ∧ (List.RunsAll p rest)

theorem List.pushRunAll ∀ (le: a → a → Bool) (p: a → Prop) (run: List a) (c: List (Option (List a)))
    (allRun: List.All p run)
    (h: List.RunsAll p c):
    List.RunsAll p (List.pushRun le run c) :=
  match c, h with
    | [], h => Both allRun Trivial
    | [None, ..rest], h => Both allRun h
    | [Some r, ..rest], Both ar h =>
      List.pushRunAll le p (List.merge le r run) rest (List.mergeAll le p r run ar allRun) h

theorem List.buildRunsAll ∀ (le: a → a → Bool) (p: a → Prop) (c: List (Option (List a))) (xs: List a)
    (h1: List.All p xs)
    (h: List.RunsAll p c):
    List.RunsAll p (List.buildRuns le c xs) :=
  match xs, h1 with
    | [], a => h
    | [x, ..xs], Both px a =>
      List.buildRunsAll le p (List.pushRun le [x] c) xs a (List.pushRunAll le p [x] c (Both px Trivial) h)

theorem List.mergeRunsAll ∀ (le: a → a → Bool) (p: a → Prop) (acc: List a) (c: List (Option (List a)))
    (allAcc: List.All p acc)
    (h: List.RunsAll p c):
    List.All p (List.mergeRuns le acc c) :=
  match c, h with
    | [], h => allAcc
    | [None, ..rest], h => List.mergeRunsAll le p acc rest allAcc h
    | [Some r, ..rest], Both ar h =>
      List.mergeRunsAll le p (List.merge le r acc) rest (List.mergeAll le p r acc ar allAcc) h

--| What every element passes, every element of the sorted list passes.
theorem List.allSortWith ∀ (le: a → a → Bool) (p: a → Prop) (xs: List a)
    (a: List.All p xs):
    List.All p (List.sortWith xs le) :=
  List.mergeRunsAll le p [] (List.buildRuns le [] xs) Trivial (List.buildRunsAll le p [] xs a Trivial)

theorem List.pushRunSortedOn ∀ (le: a → a → Bool) (p: a → Prop)
    (tot: ∀ (x y: a) => p x → p y → le x y = False → le y x = True)
    (run: List a) (c: List (Option (List a)))
    (allRun: List.All p run)
    (ha: List.RunsAll p c)
    (s: List.Sorted le run)
    (h: List.RunsSorted le c):
    List.RunsSorted le (List.pushRun le run c) :=
  match c, ha, h with
    | [], ha, h => Both s Trivial
    | [None, ..rest], ha, h => Both s h
    | [Some r, ..rest], Both ar ha, Both sr h =>
      List.pushRunSortedOn le p tot
        (List.merge le r run)
        rest
        (List.mergeAll le p r run ar allRun)
        ha
        (List.mergeSortedOn le p tot r run ar allRun sr s)
        h

theorem List.buildRunsSortedOn ∀ (le: a → a → Bool) (p: a → Prop)
    (tot: ∀ (x y: a) => p x → p y → le x y = False → le y x = True)
    (c: List (Option (List a))) (xs: List a)
    (h1: List.All p xs)
    (ha: List.RunsAll p c)
    (h: List.RunsSorted le c):
    List.RunsSorted le (List.buildRuns le c xs) :=
  match xs, h1 with
    | [], a => h
    | [x, ..xs], Both px a =>
      List.buildRunsSortedOn le p tot
        (List.pushRun le [x] c)
        xs
        a
        (List.pushRunAll le p [x] c (Both px Trivial) ha)
        (List.pushRunSortedOn le p tot [x] c (Both px Trivial) ha (Both Trivial Trivial) h)

theorem List.mergeRunsSortedOn ∀ (le: a → a → Bool) (p: a → Prop)
    (tot: ∀ (x y: a) => p x → p y → le x y = False → le y x = True)
    (acc: List a) (c: List (Option (List a)))
    (allAcc: List.All p acc)
    (ha: List.RunsAll p c)
    (s: List.Sorted le acc)
    (h: List.RunsSorted le c):
    List.Sorted le (List.mergeRuns le acc c) :=
  match c, ha, h with
    | [], ha, h => s
    | [None, ..rest], ha, h => List.mergeRunsSortedOn le p tot acc rest allAcc ha s h
    | [Some r, ..rest], Both ar ha, Both sr h =>
      List.mergeRunsSortedOn le p tot
        (List.merge le r acc)
        rest
        (List.mergeAll le p r acc ar allAcc)
        ha
        (List.mergeSortedOn le p tot r acc ar allAcc sr s)
        h

--| [`List.sortWithSorted`] for a `le` total only on the values passing `p`.
theorem List.sortWithSortedOn ∀ (le: a → a → Bool) (p: a → Prop)
    (tot: ∀ (x y: a) => p x → p y → le x y = False → le y x = True) (xs: List a)
    (a: List.All p xs):
    List.Sorted le (List.sortWith xs le) :=
  List.mergeRunsSortedOn le p tot []
    (List.buildRuns le [] xs)
    Trivial
    (List.buildRunsAll le p [] xs a Trivial)
    Trivial
    (List.buildRunsSortedOn le p tot [] xs a Trivial Trivial)

--| [`List.sortedHeadLe`] and [`List.pairwiseOfSorted`] for a `le` transitive only
--| on the values passing `p`.
theorem List.sortedHeadLeOn ∀ (le: a → a → Bool) (p: a → Prop)
    (trans: ∀ (x y z: a) => p x → p y → p z → le x y = True → le y z = True → le x z = True)
    (x z: a) (px: p x) (rest: List a)
    (h: List.All p rest)
    (h1: List.Sorted le [x, ..rest])
    (h2: List.Mem z rest):
    le x z = True :=
  match rest, h, h1, h2 with
    | [], a, s, m => Void.exfalso m
    | [y, ..ys], Both py a, Both hxy s, Inl e => rewrite <- e in hxy
    | [y, ..ys], Both py a, Both hxy s, Inr m =>
      trans x y z px py (List.allMem p z ys a m) hxy (List.sortedHeadLeOn le p trans y z py ys a s m)

theorem List.pairwiseOfSortedOn ∀ (le: a → a → Bool) (p: a → Prop)
    (trans: ∀ (x y z: a) => p x → p y → p z → le x y = True → le y z = True → le x z = True) (xs: List a)
    (h: List.All p xs)
    (h1: List.Sorted le xs):
    List.Pairwise (x y => le x y = True) xs :=
  match xs, h, h1 with
    | [], a, s => Trivial
    | [x, ..rest], Both px a, Both hx s =>
      Both
        (List.allOfMem (y => le x y = True) rest (z m => List.sortedHeadLeOn le p trans x z px rest a (Both hx s) m))
        (List.pairwiseOfSortedOn le p trans rest a s)

--| `Nat.leq` restricted to even numbers is still total there.
theorem List.sortWithSortedOnExample: List.Sorted Nat.leq (List.sortWith [4, 2, 6] Nat.leq) :=
  List.sortWithSortedOn Nat.leq
    (n => n % 2 = 0)
    (x y px py h => Nat.leqTotal x y h)
    [4, 2, 6]
    (Both rfl (Both rfl (Both rfl Trivial)))

theorem List.pairwiseAppendLeft ∀ (rel: a → a → Prop) (xs ys: List a)
    (h1: List.Pairwise rel (List.append xs ys)):
    List.Pairwise rel xs :=
  match xs, h1 with
    | [], h => Trivial
    | [x, ..xs], Both a h => Both (List.allAppendLeft (y => rel x y) xs ys a) (List.pairwiseAppendLeft rel xs ys h)

--| In a `Pairwise` join, each element of the front is related to each of the back.
theorem List.pairwiseAppendAcross ∀ (rel: a → a → Prop):
    ∀ (xs ys: List a) => List.Pairwise rel (List.append xs ys)
      → ∀ (x: a) => List.Mem x xs → ∀ (y: a) => List.Mem y ys → rel x y
  | [], ys, h, x, mx, y, my => Void.exfalso mx
  | [z, ..zs], ys, Both a h, x, Inl e, y, my =>
    rewrite <- e in List.allMem (w => rel z w) y ys (List.allAppendRight (w => rel z w) zs ys a) my
  | [z, ..zs], ys, Both a h, x, Inr mx, y, my => List.pairwiseAppendAcross rel zs ys h x mx y my

--| Merging, when everything in the first list may come before everything in
--| the second, joins the lists.
theorem List.mergeAppend ∀ (le: a → a → Bool) (xs ys: List a)
    (h: ∀ (x: a) => List.Mem x xs → ∀ (y: a) => List.Mem y ys → le x y = True):
    List.merge le xs ys = List.append xs ys :=
  match xs, ys with
    | [], ys => rfl
    | [x, ..xs], [] => Eq.sym (List.appendNil [x, ..xs])
    | [x, ..xs], [y, ..ys] =>
      rewrite h x (Inl rfl) y (Inl rfl), List.mergeAppend le xs [y, ..ys] (z m => h z (Inr m)) in rfl

--| The runs of `List.sortWith`'s counter, oldest first, joined.
def List.runsJoined: (runs: List (Option (List a))) → List a
  | [] => []
  | [None, ..rest] => List.runsJoined rest
  | [Some run, ..rest] => List.append (List.runsJoined rest) run

--| When the runs joined are in order, merging two neighbours joins them.
theorem List.pairwiseRunsMerge ∀ (le: a → a → Bool) (front older newer: List a)
    (h: List.Pairwise (x y => le x y = True) (List.append (List.append front older) newer)):
    List.merge le older newer = List.append older newer :=
  List.mergeAppend le older newer (x mx y my =>
    List.pairwiseAppendAcross
      (x y => le x y = True)
      (List.append front older)
      newer
      h
      x
      (List.anyAppendRight (w => w = x) front older mx)
      y
      my)

theorem List.pushRunJoined ∀ (le: a → a → Bool) (run: List a) (c: List (Option (List a)))
    (h: List.Pairwise (x y => le x y = True) (List.append (List.runsJoined c) run)):
    List.runsJoined (List.pushRun le run c) = List.append (List.runsJoined c) run :=
  match c with
    | [] => rfl
    | [None, ..rest] => rfl
    | [Some older, ..rest] =>
      Eq.trans
        (Eq.cong
          (r => List.runsJoined (List.pushRun le r rest))
          (List.pairwiseRunsMerge le (List.runsJoined rest) older run h))
        (Eq.trans
          (List.pushRunJoined le
            (List.append older run)
            rest
            (rewrite List.appendAssoc (List.runsJoined rest) older run at h))
          (Eq.sym (List.appendAssoc (List.runsJoined rest) older run)))

theorem List.buildRunsJoined ∀ (le: a → a → Bool) (c: List (Option (List a))) (xs: List a)
    (h: List.Pairwise (x y => le x y = True) (List.append (List.runsJoined c) xs)):
    List.runsJoined (List.buildRuns le c xs) = List.append (List.runsJoined c) xs :=
  match xs with
    | [] => Eq.sym (List.appendNil (List.runsJoined c))
    | [x, ..xs] =>
      Eq.trans
        (List.buildRunsJoined le
          (List.pushRun le [x] c)
          xs
          (rewrite <- List.pushRunJoined le
            [x]
            c
            (List.pairwiseAppendLeft
              (x y => le x y = True)
              (List.append (List.runsJoined c) [x])
              xs
              (rewrite <- List.appendAssoc (List.runsJoined c) [x] xs at h)) at (rewrite <- List.appendAssoc
            (List.runsJoined c)
            [x]
            xs at h)))
        (Eq.trans
          (Eq.cong
            (r => List.append r xs)
            (List.pushRunJoined le
              [x]
              c
              (List.pairwiseAppendLeft
                (x y => le x y = True)
                (List.append (List.runsJoined c) [x])
                xs
                (rewrite <- List.appendAssoc (List.runsJoined c) [x] xs at h))))
          (List.appendAssoc (List.runsJoined c) [x] xs))

theorem List.mergeRunsJoined ∀ (le: a → a → Bool) (acc: List a) (c: List (Option (List a)))
    (h: List.Pairwise (x y => le x y = True) (List.append (List.runsJoined c) acc)):
    List.mergeRuns le acc c = List.append (List.runsJoined c) acc :=
  match c with
    | [] => rfl
    | [None, ..rest] => List.mergeRunsJoined le acc rest h
    | [Some older, ..rest] =>
      Eq.trans
        (Eq.cong (r => List.mergeRuns le r rest) (List.pairwiseRunsMerge le (List.runsJoined rest) older acc h))
        (Eq.trans
          (List.mergeRunsJoined le
            (List.append older acc)
            rest
            (rewrite List.appendAssoc (List.runsJoined rest) older acc at h))
          (Eq.sym (List.appendAssoc (List.runsJoined rest) older acc)))

--| Sorting a list that is already sorted gives it back, for a transitive `le`.
--| No totality is needed: every merge takes the older run whole.
-- (D725)
theorem List.sortWithOfSorted ∀ (le: a → a → Bool)
    (trans: ∀ (x y z: a) => le x y = True → le y z = True → le x z = True) (xs: List a)
    (s: List.Sorted le xs):
    List.sortWith xs le = xs :=
  Eq.trans
    (List.mergeRunsJoined le []
      (List.buildRuns le [] xs)
      (rewrite <- List.appendNil xs, <- List.buildRunsJoined le [] xs
        (List.pairwiseOfSorted le trans xs s) at List.pairwiseOfSorted le trans xs s))
    (Eq.trans
      (List.appendNil (List.runsJoined (List.buildRuns le [] xs)))
      (List.buildRunsJoined le [] xs (List.pairwiseOfSorted le trans xs s)))

theorem List.sortWithOfSortedExample ∀ (xs: List Nat) (s: List.Sorted Nat.leq xs): List.sortWith xs Nat.leq = xs :=
  List.sortWithOfSorted Nat.leq Nat.leTrans xs s

-- Finding by key, and keys that stay distinct when the list is rearranged
-- (SW-363). Here rather than with `List.find` and `List.Distinct` in the
-- toolkit because they decide equality with `DecEq`.

--| Finding by key: what is found has the key, and when some element has the
--| key, something is found.
theorem List.findKey ∀ [auto eq: DecEq k] (xs: List a) (key: a → k) (kk: k) (y: a)
    (h: List.find xs (x => key x == kk) = Some y):
    key y = kk :=
  match List.findSome xs (x => key x == kk) y h with | Both py m => py.read

theorem List.findKeySome ∀ [auto eq: DecEq k] (xs: List a) (key: a → k) (kk: k)
    (m: List.Mem kk (List.map xs key)):
    List.find xs (x => key x == kk) ≠ None :=
  h =>
    List.anyElim (x => key x = kk) Void xs (List.memMapAny xs key kk m) (x inXs e =>
      List.findNoneNotMem xs (z => key z == kk) x ((DecEq.decide (key x) kk).complete e) inXs h)

--| Permutations have the same elements.
theorem List.memPerm ∀ [auto eq: DecEq a] (xs ys: List a)
    (h: List.Perm xs ys) (x: a)
    (m: List.Mem x xs):
    List.Mem x ys :=
  let inXs: xs.any (y => y == x) := Witness x (Both m (DecEq.refl x))
  let found: ys.any (y => y == x) := Eq.trans (Eq.sym (List.anyPerm xs ys h (y => y == x))) inXs
  let Witness y (Both inYs e) := found
  rewrite <- e.read in inYs

--| Counting with a test the first element passes.
theorem List.occurrencesConsTrue ∀ (xs: List a) (p: a → Bool) (x: a)
    (px: p x = True):
    List.occurrences [x, ..xs] p = Succ (List.occurrences xs p) :=
  rewrite px in rfl

theorem Bool.toNatAddLeOne ∀ (b: Bool) (n: Nat) (h: Bool.toNat b + n ≤ 1): n ≤ 1 := match b, n with
  | False, n => h
  | True, Zero => rfl

--| No element of the rest has the key of the head that has `kk`, if the head's key isn't among theirs.
theorem List.occurrencesKeyAbsent ∀ [auto eq: DecEq k] (xs: List a) (key: a → k) (x: a) (kk: k)
    (notMem: ¬(List.Mem (key x) (List.map xs key)))
    (t: (key x == kk) = True):
    List.occurrences xs (y => key y == kk) = 0 :=
  match n: List.occurrences xs (y => key y == kk) with
    | Zero => rfl
    | Succ m =>
      let found: xs.any (y => key y == kk) := rewrite List.anyOccurrences xs (y => key y == kk), n in rfl
      let Witness y (Both inXs py) := found
      Void.exfalso
        (notMem
          (Eq.subst (z => List.Mem z (List.map xs key)) (Eq.trans py.read (Eq.sym t.read)) (List.memMap xs y inXs key)))

--| Distinct keys: at most one element has any key.
theorem List.occurrencesKeyDistinct ∀ [auto eq: DecEq k] (xs: List a) (key: a → k) (kk: k)
    (h: List.Distinct (List.map xs key)):
    List.occurrences xs (x => key x == kk) ≤ 1 :=
  match xs, h with
    | [], d => rfl
    | [x, ..xs], Both notMem d =>
      Bool.inspect
        (key x == kk)
        (c => Bool.toNat c + List.occurrences xs (y => key y == kk) ≤ 1)
        (t => rewrite List.occurrencesKeyAbsent xs key x kk notMem t in rfl)
        (f => List.occurrencesKeyDistinct xs key kk d)

--| If the head's key is the only one of its kind, it isn't among the keys of the rest.
theorem List.memMapOfOccurrences ∀ [auto eq: DecEq k] (xs: List a) (key: a → k) (x: a)
    (h: List.occurrences [x, ..xs] (z => key z == key x) ≤ 1):
    ¬(List.Mem (key x) (List.map xs key)) :=
  m =>
    List.anyElim (y => key y = key x) Void xs (List.memMapAny xs key (key x) m) (y inXs e =>
      match n: List.occurrences xs (z => key z == key x) with
        | Zero =>
          let none: xs.any (z => key z == key x) = False := rewrite n at List.anyOccurrences xs (z => key z == key x)
          (none.read y inXs).read e
        | Succ c =>
          let one: Nat.leq (Succ (List.occurrences xs (z => key z == key x))) 1 = True :=
            Eq.trans
              (Eq.sym
                (Eq.cong
                  (t => Nat.leq t 1)
                  (List.occurrencesConsTrue xs (z => key z == key x) x ((DecEq.decide (key x) (key x)).complete rfl))))
              h
          Bool.falseNotTrue
            (Eq.trans (rfl: False = Nat.leq (Succ (Succ c)) 1) (Eq.subst (m => Nat.leq (Succ m) 1 = True) n one)))

--| When at most one element has any key, the keys are distinct.
theorem List.distinctOfOccurrences ∀ [auto eq: DecEq k] (xs: List a) (key: a → k)
    (h: ∀ (kk: k) => List.occurrences xs (x => key x == kk) ≤ 1):
    List.Distinct (List.map xs key) :=
  match xs with
    | [] => Trivial
    | [x, ..xs] =>
      Both
        (List.memMapOfOccurrences xs key x (h (key x)))
        (List.distinctOfOccurrences xs key (kk =>
          Bool.toNatAddLeOne (key x == kk) (List.occurrences xs (z => key z == kk)) (h kk)))

--| Rearranging a list keeps its keys distinct.
theorem List.distinctMapPerm ∀ [auto eq: DecEq k] (xs: List a) (key: a → k) (ys: List a)
    (h: List.Perm xs ys)
    (d: List.Distinct (List.map ys key)):
    List.Distinct (List.map xs key) :=
  List.distinctOfOccurrences xs key (kk =>
    Eq.trans (Eq.cong (n => Nat.leq n 1) (h (x => key x == kk))) (List.occurrencesKeyDistinct ys key kk d))

--| Rearranging a list keeps it free of repeats.
theorem List.distinctPerm ∀ [auto eq: DecEq a] (xs ys: List a)
    (same: List.Perm xs ys)
    (distinct: List.Distinct ys):
    List.Distinct xs :=
  rewrite <- List.mapId xs in List.distinctMapPerm xs (x => x) ys same (rewrite List.mapId ys in distinct)

--| Counting `p`, apart from `v` and at `v`.
theorem List.occurrencesSplit ∀ [auto eq: DecEq a] (xs: List a) (v: a) (p: a → Bool):
    List.occurrences xs p = List.occurrences xs (x => p x ∧ ¬(x == v)) + List.occurrences xs (x => p x ∧ (x == v)) :=
  match xs with
    | [] => rfl
    | [x, ..xs] =>
      let one: Bool.toNat (p x) = Bool.toNat (p x ∧ ¬(x == v)) + Bool.toNat (p x ∧ (x == v)) := match p x, x == v with
        | True, True => rfl
        | True, False => rfl
        | False, True => rfl
        | False, False => rfl
      Eq.trans
        (Eq.cong (t => t + List.occurrences xs p) one)
        (Eq.trans
          (Eq.cong
            (t => (Bool.toNat (p x ∧ ¬(x == v)) + Bool.toNat (p x ∧ (x == v))) + t)
            (List.occurrencesSplit xs v p))
          (Nat.addSwap
            (Bool.toNat (p x ∧ ¬(x == v)))
            (Bool.toNat (p x ∧ (x == v)))
            (List.occurrences xs (y => p y ∧ ¬(y == v)))
            (List.occurrences xs (y => p y ∧ (y == v)))))

--| Counting at `x` in a list without `x` finds nothing.
theorem List.occurrencesAbsent ∀ [auto eq: DecEq a] (xs: List a) (x: a) (p: a → Bool)
    (n: ¬(List.Mem x xs)):
    List.occurrences xs (y => p y ∧ (y == x)) = 0 :=
  match xs with
    | [] => rfl
    | [y, ..ys] =>
      match e: y == x with
        | True => Void.exfalso (n (Inl e.read))
        | False => rewrite Bool.andFalse (p y), List.occurrencesAbsent ys x p (m => n (Inr m)) in rfl

--| Counting at `x` in a list with `x` once finds `x` if it passes `p`.
theorem List.occurrencesOnce ∀ [auto eq: DecEq a] (xs: List a) (x: a) (p: a → Bool)
    (h: List.Distinct xs)
    (h1: List.Mem x xs):
    List.occurrences xs (y => p y ∧ (y == x)) = Bool.toNat (p x) :=
  match xs, h, h1 with
    | [], d, m => Void.exfalso m
    | [y, ..ys], Both notMem d, Inl e =>
      rewrite e, DecEq.refl x, Bool.andTrue (p x), List.occurrencesAbsent ys x p (rewrite e at notMem) in
        Nat.addZero (Bool.toNat (p x))
    | [y, ..ys], Both notMem d, Inr m =>
      match e: y == x with
        | True => Void.exfalso (notMem (rewrite e.read in m))
        | False => rewrite Bool.andFalse (p y), List.occurrencesOnce ys x p d m in rfl

--| Two lists without repeats and with the same members are the same elements
--| in another order.
theorem List.permOfSameMembers ∀ [auto eq: DecEq a] (xs ys: List a)
    (dx: List.Distinct xs)
    (dy: List.Distinct ys)
    (there: ∀ (x: a) => List.Mem x xs → List.Mem x ys)
    (back: ∀ (y: a) => List.Mem y ys → List.Mem y xs):
    List.Perm xs ys :=
  match xs, ys, dx with
    | [], [], dx => p => rfl
    | [], [y, ..ys], dx => p => Void.exfalso (back y (Inl rfl))
    | [x, ..xs], ys, Both notMem dx => p =>
      let others := List.filter ys (z => ¬(z == x))
      let rest: List.occurrences xs p = List.occurrences others p :=
        List.permOfSameMembers xs others dx
          (List.distinctFilter ys (z => ¬(z == x)) dy)
          (z m =>
            List.memFilterIntro ys
              (z => ¬(z == x))
              (there z (Inr m))
              (match e: z == x with
                | True => Void.exfalso (notMem (rewrite <- e.read in m))
                | False => rfl))
          (z m =>
            match List.memFilter ys (z => ¬(z == x)) m with
              | Both inYs notX =>
                match back z inYs with
                  | Inl e => Void.exfalso (Bool.falseNotTrue (rewrite e, DecEq.refl z at notX))
                  | Inr inXs => inXs)
          p
      rewrite List.occurrencesSplit ys x p,
          List.occurrencesOnce ys x p dy (there x (Inl rfl)),
          <- List.occurrencesFilter ys (z => ¬(z == x)) p,
          <- rest in
        Nat.addComm (Bool.toNat (p x)) (List.occurrences xs p)

--| `n` is the number of values `x` with `p x`: some list without repeats has
--| exactly those values, and `n` elements. For a `p` true of finitely many
--| values, where a `Set` isn't at hand: the points where two lines cross,
--| say. Any two such lists have the same length ([`List.numberWithUnique`]),
--| so it says what the number is.
def List.NumberWith (n: Nat) (p: a → Bool): Prop :=
  Exists (List a) (xs => List.Distinct xs ∧ (∀ (x: a) => (x ∈ xs ↔ p x = True)) ∧ List.length xs = n)

--| The number of values with `p` is one number.
theorem List.numberWithUnique ∀ [auto eq: DecEq a] (p: a → Bool) (n m: Nat)
    (first: List.NumberWith n p)
    (second: List.NumberWith m p):
    n = m :=
  match first, second with
    | Witness xs (Both dx (Both memX lengthX)), Witness ys (Both dy (Both memY lengthY)) =>
      let same := List.permOfSameMembers xs ys dx dy (x inX => (memY x).backward ((memX x).forward inX)) (y inY =>
        (memX y).backward ((memY y).forward inY))
      rewrite <- lengthX, <- lengthY in List.permLength xs ys same

--| Two tests that agree everywhere are true of the same number of values.
theorem List.numberWithCong ∀ (n: Nat) (p q: a → Bool)
    (same: ∀ (x: a) => p x = q x)
    (counted: List.NumberWith n p):
    List.NumberWith n q :=
  match counted with
    | Witness xs (Both distinct (Both members length)) =>
      Witness xs (Both distinct (Both (x => rewrite <- same x in members x) length))

--| Two lists sorted by the same order, with the same elements, are equal,
--| when the order puts no two different elements both ways round.
theorem List.sortedPermEq ∀ [auto eq: DecEq a] (le: a → a → Bool)
    (trans: ∀ (x y z: a) => le x y = True → le y z = True → le x z = True)
    (antisymm: ∀ (x y: a) => le x y = True → le y x = True → x = y) (xs ys: List a)
    (h: List.Sorted le xs)
    (h1: List.Sorted le ys)
    (p: List.Perm xs ys):
    xs = ys :=
  match xs, ys, h, h1 with
    | [], [], sx, sy => rfl
    | [], [y, ..ys], sx, sy => Void.exfalso (Nat.zeroNotSucc (List.length ys) (List.permLength [] [y, ..ys] p))
    | [x, ..xs], [], sx, sy => Void.exfalso (Nat.succNotZero (List.length xs) (List.permLength [x, ..xs] [] p))
    | [x, ..xs], [y, ..ys], Both hx sx, Both hy sy =>
      let same: x = y := match List.memPerm [y, ..ys] [x, ..xs] (List.permSym [x, ..xs] [y, ..ys] p) y (Inl rfl) with
        | Inl e => e
        | Inr my =>
          match List.memPerm [x, ..xs] [y, ..ys] p x (Inl rfl) with
            | Inl e => Eq.sym e
            | Inr mx =>
              antisymm x y
                (List.sortedHeadLe le trans x y xs (Both hx sx) my)
                (List.sortedHeadLe le trans y x ys (Both hy sy) mx)
      let rest: xs = ys := List.sortedPermEq le trans antisymm xs ys sx sy (q =>
        Nat.addCancelLeft
          (Bool.toNat (q x))
          (List.occurrences xs q)
          (List.occurrences ys q)
          (Eq.trans (p q) (Eq.cong (t => Bool.toNat (q t) + List.occurrences ys q) (Eq.sym same))))
      rewrite same, rest in rfl

--| Two lists without repeats, sorted by the same order, with the same
--| members, are equal, when the order puts no two different elements both
--| ways round. [`List.sortedPermEq`] for lists known only by their members.
theorem List.sortedEqOfMembers ∀ [auto eq: DecEq a] (le: a → a → Bool)
    (trans: ∀ (x y z: a) => le x y = True → le y z = True → le x z = True)
    (antisymm: ∀ (x y: a) => le x y = True → le y x = True → x = y) (xs ys: List a)
    (dx: List.Distinct xs)
    (dy: List.Distinct ys)
    (sx: List.Sorted le xs)
    (sy: List.Sorted le ys)
    (there: ∀ (x: a) => x ∈ xs → x ∈ ys)
    (back: ∀ (y: a) => y ∈ ys → y ∈ xs):
    xs = ys :=
  List.sortedPermEq le trans antisymm xs ys sx sy (List.permOfSameMembers xs ys dx dy there back)

--| A list sorted by an `Ord` is the sort of any list with the same elements.
theorem List.sortOfSorted ∀ [auto ord: Ord a] (xs ys: List a)
    (sorted: List.Sorted (x y => Ordering.isLessEq (Ord.compare x y)) ys)
    (same: List.Perm ys xs):
    ys = xs.sort :=
  List.sortedPermEq
    (x y => Ordering.isLessEq (Ord.compare x y))
    Ord.isLessEqTrans
    Ord.isLessEqAntisymm
    ys
    xs.sort
    sorted
    (List.sortSorted xs)
    (List.permTrans ys xs xs.sort same (List.permSym xs.sort xs (List.sortPerm xs)))

--| Lists with the same elements sort to the same list.
theorem List.sortEqOfPerm ∀ [auto ord: Ord a] (xs ys: List a) (same: List.Perm xs ys): xs.sort = ys.sort :=
  List.sortOfSorted ys xs.sort (List.sortSorted xs) (List.permTrans xs.sort xs ys (List.sortPerm xs) same)

--| For numbers, sorted by `Nat.leq`.
theorem List.sortOfSortedNat ∀ (xs ys: List Nat)
    (sorted: List.Sorted Nat.leq ys)
    (same: List.Perm ys xs):
    ys = xs.sort :=
  List.sortOfSorted xs ys
    (List.sortedCong Nat.leq
      (x y => Ordering.isLessEq (Nat.compare x y))
      (x y => Eq.sym (Nat.compareLeq x y))
      ys
      sorted)
    same

--| Without `x` in the list, nothing is taken out.
theorem List.removeFirstAbsent ∀ [auto eq: DecEq a] (xs: List a) (x: a) (n: ¬(List.Mem x xs)): xs.removeFirst x = xs :=
  match xs with
    | [] => rfl
    | [y, ..ys] =>
      match e: y == x with
        | True => Void.exfalso (n (Inl e.read))
        | False => rewrite List.removeFirstAbsent ys x (m => n (Inr m)) in rfl

--| With `x` in the list, `x` and the rest are the list in another order.
theorem List.occurrencesRemoveFirst [auto eq: DecEq a]:
    ∀ (ys: List a) (x: a) => List.Mem x ys
      → ∀ (p: a → Bool) => List.occurrences ys p = Bool.toNat (p x) + List.occurrences (ys.removeFirst x) p
  | [], x, m, p => Void.exfalso m
  | [y, ..ys], x, m, p =>
    match e: y == x with
      | True => rewrite e.read in rfl
      | False =>
        let later: List.Mem x ys := match m with
          | Inl same => Void.exfalso (e.read same)
          | Inr rest => rest
        rewrite List.occurrencesRemoveFirst ys x later p in Nat.addLeftComm (Bool.toNat (p y)) (Bool.toNat (p x)) _

theorem List.permRemoveFirst ∀ [auto eq: DecEq a] (ys: List a) (x: a)
    (m: List.Mem x ys):
    List.Perm [x, ..ys.removeFirst x] ys :=
  p => Eq.sym (List.occurrencesRemoveFirst ys x m p)

theorem List.lengthRemoveFirst ∀ [auto eq: DecEq a] (ys: List a) (x: a)
    (m: List.Mem x ys):
    List.length ys = Succ (List.length (ys.removeFirst x)) :=
  Eq.sym (List.permLength [x, ..ys.removeFirst x] ys (List.permRemoveFirst ys x m))

--| Taking the same element off the front of one list and out of the other
--| leaves a permutation.
theorem List.permRemoveFirstOfCons ∀ [auto eq: DecEq a] (x: a) (xs ys: List a)
    (same: List.Perm [x, ..xs] ys):
    List.Perm xs (ys.removeFirst x) :=
  p =>
    Nat.addCancelLeft
      (Bool.toNat (p x))
      (List.occurrences xs p)
      (List.occurrences (ys.removeFirst x) p)
      (Eq.trans (same p) (List.occurrencesRemoveFirst ys x (List.memPerm [x, ..xs] ys same x (Inl rfl)) p))

theorem List.sumByRemoveFirst [auto eq: DecEq a] [auto add: Add b]:
    ∀ (ys: List a) (x: a) => List.Mem x ys → ∀ (f: a → b) => List.sumBy ys f = f x + List.sumBy (ys.removeFirst x) f
  | [], x, m, f => Void.exfalso m
  | [y, ..ys], x, m, f =>
    match e: y == x with
      | True => rewrite List.sumByCons ys y f, e.read in rfl
      | False =>
        let later: List.Mem x ys := match m with
          | Inl same => Void.exfalso (e.read same)
          | Inr rest => rest
        rewrite List.sumByCons ys y f, List.sumByCons (ys.removeFirst x) y f, List.sumByRemoveFirst ys x later f in
          Add.addLeftComm (f y) (f x) _

--| Sums and counts are the same in any order.
theorem List.sumByPerm [auto eq: DecEq a] [auto add: Add b]:
    ∀ (xs ys: List a) => List.Perm xs ys → ∀ (f: a → b) => List.sumBy xs f = List.sumBy ys f
  | [], [], same, f => rfl
  | [], [y, ..ys], same, f => Void.exfalso (Nat.zeroNotSucc (List.length ys) (List.permLength [] [y, ..ys] same))
  | [x, ..xs], ys, same, f =>
    let found: List.Mem x ys := List.memPerm [x, ..xs] ys same x (Inl rfl)
    rewrite List.sumByCons xs x f,
        List.sumByPerm xs (ys.removeFirst x) (List.permRemoveFirstOfCons x xs ys same) f,
        List.sumByRemoveFirst ys x found f in
      rfl

theorem List.sumPerm ∀ [auto eq: DecEq a] [auto add: Add a] (xs ys: List a)
    (same: List.Perm xs ys):
    List.sum xs = List.sum ys :=
  List.sumByPerm xs ys same (x => x)

theorem List.countPerm ∀ (xs ys: List a) (same: List.Perm xs ys) (p: a → Bool): List.count xs p = List.count ys p :=
  rewrite List.countOccurrences xs p, List.countOccurrences ys p in same p

--| A `flatMap` of lists that are permutations of each other gives
--| permutations.
theorem List.permFlatMap ∀ [auto eq: DecEq a] (xs ys: List a)
    (same: List.Perm xs ys) (f: a → List b):
    List.Perm (List.flatMap xs f) (List.flatMap ys f) :=
  p =>
    rewrite List.occurrencesFlatMap f p xs, List.occurrencesFlatMap f p ys in
      List.sumByPerm xs ys same (x => List.occurrences (f x) p)

theorem List.findKeyExample: List.find [MkPair "a" 1, MkPair "b" 2, MkPair "b" 3] (x => Pair.fst x == "b")
      = Some (MkPair "b" 2) :=
  rfl

--| Adding an element in front keeps every subsequence.
theorem List.subsequenceCons ∀ (x: a) (s ys: List a) (h: List.Subsequence s ys): List.Subsequence s [x, ..ys] :=
  match s with
    | [] => Trivial
    | [y, ..s] => Inr h

theorem List.subsequenceRefl ∀ (xs: List a): List.Subsequence xs xs := match xs with
  | [] => Trivial
  | [x, ..xs] => Inl (Both rfl (List.subsequenceRefl xs))

theorem List.subsequenceLength ∀ (s ys: List a) (h1: List.Subsequence s ys): List.length s ≤ List.length ys :=
  match s, ys, h1 with
    | [], ys, h => rfl
    | [x, ..xs], [], h => Void.exfalso h
    | [x, ..xs], [y, ..ys], Inl (Both e h) => List.subsequenceLength xs ys h
    | [x, ..xs], [y, ..ys], Inr h =>
      Nat.leTrans
        (List.length [x, ..xs])
        (List.length ys)
        (Succ (List.length ys))
        (List.subsequenceLength [x, ..xs] ys h)
        (Nat.leSucc (List.length ys))

--| Dropping the first element keeps a subsequence.
theorem List.subsequenceTail ∀ (x: a) (s ys: List a) (h1: List.Subsequence [x, ..s] ys): List.Subsequence s ys :=
  match ys, h1 with
    | [], h => Void.exfalso h
    | [y, ..ys], Inl (Both e h) => List.subsequenceCons y s ys h
    | [y, ..ys], Inr h => List.subsequenceCons y s ys (List.subsequenceTail x s ys h)

--| A subsequence of a subsequence is a subsequence.
theorem List.subsequenceTrans ∀ (xs ys zs: List a)
    (h: List.Subsequence xs ys)
    (h3: List.Subsequence ys zs):
    List.Subsequence xs zs :=
  match xs, ys, zs, h, h3 with
    | [], ys, zs, h1, h2 => Trivial
    | [x, ..xs], [], zs, h1, h2 => Void.exfalso h1
    | [x, ..xs], [y, ..ys], [], h1, h2 => Void.exfalso h2
    | [x, ..xs], [y, ..ys], [z, ..zs], h1, Inr h2 => Inr (List.subsequenceTrans [x, ..xs] [y, ..ys] zs h1 h2)
    | [x, ..xs], [y, ..ys], [z, ..zs], Inl (Both e1 h1), Inl (Both e2 h2) =>
      Inl (Both (Eq.trans e1 e2) (List.subsequenceTrans xs ys zs h1 h2))
    | [x, ..xs], [y, ..ys], [z, ..zs], Inr h1, Inl (Both e2 h2) => Inr (List.subsequenceTrans [x, ..xs] ys zs h1 h2)

--| Every subsequence of `xs` is one of its combinations of its own length.
theorem List.combinationsMemLength ∀ (xs ys: List a)
    (h1: List.Subsequence ys xs):
    ys ∈ List.combinations xs (List.length ys) :=
  match xs, ys, h1 with
    | [], [], h => Inl rfl
    | [], [y, ..ys], h => Void.exfalso h
    | [x, ..xs], [], h => Inl rfl
    | [x, ..xs], [y, ..ys], Inl (Both e h) =>
      List.memAppendLeft
        [y, ..ys]
        (List.map (List.combinations xs (List.length ys)) (zs => [x, ..zs]))
        (List.combinations xs (Succ (List.length ys)))
        (rewrite e in
          List.memMap (List.combinations xs (List.length ys)) ys (List.combinationsMemLength xs ys h) (zs => [x, ..zs]))
    | [x, ..xs], [y, ..ys], Inr h =>
      List.memAppendRight
        [y, ..ys]
        (List.map (List.combinations xs (List.length ys)) (zs => [x, ..zs]))
        (List.combinations xs (Succ (List.length ys)))
        (List.combinationsMemLength xs [y, ..ys] h)

--| A subsequence of `xs` of length `k` is one of its combinations of `k`.
theorem List.combinationsMem ∀ (xs ys: List a) (k: Nat)
    (sub: List.Subsequence ys xs)
    (len: List.length ys = k):
    ys ∈ List.combinations xs k :=
  rewrite <- len in List.combinationsMemLength xs ys sub

--| A combination of `k` elements of `xs` has `k` elements and is a subsequence of `xs`.
theorem List.memCombinations ∀ (xs: List a) (k: Nat) (ys: List a)
    (h: ys ∈ List.combinations xs k):
    (List.length ys = k) ∧ (List.Subsequence ys xs) :=
  match xs, k, h with
    | xs, Zero, Inl e => rewrite <- e in Both rfl Trivial
    | xs, Zero, Inr m => Void.exfalso m
    | [], Succ k, m => Void.exfalso m
    | [x, ..xs], Succ k, m =>
      match List.memAppend ys
        (List.map (List.combinations xs k) (zs => [x, ..zs]))
        (List.combinations xs (Succ k))
        m with
        | Inl inMap => Exists.elim (List.memMapElim (zs => [x, ..zs]) ys (List.combinations xs k) inMap) (zs both =>
          match List.memCombinations xs k zs (And.left both) with
            | Both len sub => rewrite <- And.right both in Both (Eq.cong Succ len) (Inl (Both rfl sub)))
        | Inr inRest =>
          match List.memCombinations xs (Succ k) ys inRest with
            | Both len sub => Both len (List.subsequenceCons x ys xs sub)

--| Taking apart a choice from `Cons x rest`: it starts with `x` and continues with a choice
--| from `rest` of one fewer, or it is a choice from `rest`. (Each way round.)
theorem List.memCombinationsCons ∀ (y: a) (zs: List a) (x: a) (rest: List a) (k: Nat):
    ([y, ..zs] ∈ List.combinations [x, ..rest] (Succ k))
      ↔ (((y = x) ∧ (zs ∈ List.combinations rest k)) ∨ ([y, ..zs] ∈ List.combinations rest (Succ k))) :=
  {
    forward = m =>
      match List.memAppend
        [y, ..zs]
        (List.map (List.combinations rest k) (ws => [x, ..ws]))
        (List.combinations rest (Succ k))
        m with
        | Inl inMap =>
          Exists.elim (List.memMapElim (ws => [x, ..ws]) [y, ..zs] (List.combinations rest k) inMap) (ws both =>
            let made := And.right both
            let headIs: x = y := Option.someInjective (Eq.cong List.head made)
            let tailIs: ws = zs := Eq.cong (.drop 1) made
            Inl (Both (Eq.sym headIs) (rewrite <- tailIs in And.left both)))
        | Inr inRest => Inr inRest,
    backward = h =>
      match h with
        | Inl both =>
          List.memAppendLeft
            [y, ..zs]
            (List.map (List.combinations rest k) (ws => [x, ..ws]))
            (List.combinations rest (Succ k))
            (rewrite And.left both in List.memMap (List.combinations rest k) zs (And.right both) (ws => [x, ..ws]))
        | Inr inRest =>
          List.memAppendRight
            [y, ..zs]
            (List.map (List.combinations rest k) (ws => [x, ..ws]))
            (List.combinations rest (Succ k))
            inRest
  }

--| The choices of one element are the elements.
theorem List.memCombinationsOne ∀ (v: a) (xs: List a): ([v] ∈ List.combinations xs 1) ↔ (v ∈ xs) := match xs with
  | [] => { forward = m => m, backward = m => m }
  | [x, ..rest] => {
    forward = m =>
      match (List.memCombinationsCons v [] x rest 0).forward m with
        | Inl both => Inl (Eq.sym (And.left both))
        | Inr later => Inr ((List.memCombinationsOne v rest).forward later),
    backward = m =>
      (List.memCombinationsCons v [] x rest 0).backward
        (match m with
          | Inl e => Inl (Both (Eq.sym e) (Inl rfl))
          | Inr later => Inr ((List.memCombinationsOne v rest).backward later))
  }

--| The choices of two elements are the pairs.
theorem List.memCombinationsTwo ∀ (u v: a) (xs: List a): ([u, v] ∈ List.combinations xs 2) ↔ ((u, v) ∈ List.pairs xs) :=
  match xs with
    | [] => { forward = m => m, backward = m => m }
    | [x, ..rest] => {
      forward = m =>
        (List.memPairsCons u v x rest).backward
          (match (List.memCombinationsCons u [v] x rest 1).forward m with
            | Inl both => Inl (Both (And.left both) ((List.memCombinationsOne v rest).forward (And.right both)))
            | Inr later => Inr ((List.memCombinationsTwo u v rest).forward later)),
      backward = m =>
        (List.memCombinationsCons u [v] x rest 1).backward
          (match (List.memPairsCons u v x rest).forward m with
            | Inl both => Inl (Both (And.left both) ((List.memCombinationsOne v rest).backward (And.right both)))
            | Inr later => Inr ((List.memCombinationsTwo u v rest).backward later))
    }

--| The count of combinations, one element at a time (Pascal's rule): those with the first element, and those without.
theorem List.lengthCombinationsCons ∀ (x: a) (xs: List a) (k: Nat):
    List.length (List.combinations [x, ..xs] (Succ k))
      = List.length (List.combinations xs k) + List.length (List.combinations xs (Succ k)) :=
  rewrite List.lengthAppend (List.map (List.combinations xs k) (zs => [x, ..zs])) (List.combinations xs (Succ k)),
      List.lengthMap (List.combinations xs k) (zs => [x, ..zs]) in
    rfl

theorem List.mergeCount ∀ (xs ys: List a) (le: a → a → Bool) (p: a → Bool):
    List.occurrences (List.merge le xs ys) p = List.occurrences xs p + List.occurrences ys p :=
  match xs, ys with
    | [], ys => rfl
    | [x, ..xs], [] => ring
    | [x, ..xs], [y, ..ys] =>
      Bool.inspect
        (le x y)
        (c =>
          List.occurrences (if c then [x, ..List.merge le xs [y, ..ys]] else [y, ..List.merge le [x, ..xs] ys]) p
            = List.occurrences [x, ..xs] p + List.occurrences [y, ..ys] p)
        (e => ring [List.mergeCount xs [y, ..ys] le p])
        (e => ring [List.mergeCount [x, ..xs] ys le p])

--| How many elements of all the runs satisfy `p`.
@[noReceiver]
def List.runsCount (p: a → Bool): (runs: List (Option (List a))) → Nat
  | [] => 0
  | [None, ..rest] => List.runsCount p rest
  | [Some r, ..rest] => List.occurrences r p + List.runsCount p rest

theorem List.pushRunCount ∀ (run: List a) (c: List (Option (List a))) (le: a → a → Bool) (p: a → Bool):
    List.runsCount p (List.pushRun le run c) = List.occurrences run p + List.runsCount p c :=
  match c with
    | [] => rfl
    | [None, ..rest] => rfl
    | [Some r, ..rest] => ring [List.pushRunCount (List.merge le r run) rest le p, List.mergeCount r run le p]

theorem List.buildRunsCount ∀ (c: List (Option (List a))) (xs: List a) (le: a → a → Bool) (p: a → Bool):
    List.runsCount p (List.buildRuns le c xs) = List.runsCount p c + List.occurrences xs p :=
  match xs with
    | [] => ring
    | [x, ..xs] => ring [List.buildRunsCount (List.pushRun le [x] c) xs le p, List.pushRunCount [x] c le p]

theorem List.mergeRunsCount ∀ (acc: List a) (c: List (Option (List a))) (le: a → a → Bool) (p: a → Bool):
    List.occurrences (List.mergeRuns le acc c) p = List.occurrences acc p + List.runsCount p c :=
  match c with
    | [] => ring
    | [None, ..rest] => List.mergeRunsCount acc rest le p
    | [Some r, ..rest] => ring [List.mergeRunsCount (List.merge le r acc) rest le p, List.mergeCount r acc le p]

theorem List.sortWithPerm ∀ (xs: List a) (le: a → a → Bool): List.Perm (List.sortWith xs le) xs := p =>
  Eq.trans (List.mergeRunsCount [] (List.buildRuns le [] xs) le p) (List.buildRunsCount [] xs le p)

theorem List.sortByPerm ∀ (xs: List a) (cmp: a → a → Ordering): List.Perm (List.sortBy xs cmp) xs :=
  List.sortWithPerm xs (x y => Ordering.isLessEq (cmp x y))

theorem List.sortPerm ∀ [auto ord: Ord a] (xs: List a): List.Perm (List.sort xs) xs := List.sortByPerm xs Ord.compare

theorem List.sortLength ∀ [auto ord: Ord a] (xs: List a): List.length (List.sort xs) = List.length xs :=
  List.permLength (List.sort xs) xs (List.sortPerm xs)

theorem Bool.andFalse ∀ (b: Bool): (b ∧ False) = False := match b with
  | True => rfl
  | False => rfl

theorem Bool.andTrue ∀ (b: Bool): (b ∧ True) = b := match b with
  | True => rfl
  | False => rfl

theorem Nat.addSubLeft ∀ (s m: Nat): (s + m) - s = m := rewrite Nat.addComm s m in Nat.addSub m s

--| Sums and products don't mind the order.
theorem List.sumReverse ∀ (xs: List Nat): List.sum (List.reverse xs) = List.sum xs := List.sumByReverse xs (x => x)

theorem List.productFrom ∀ [auto mul: Mul a] (xs: List a) (z: a): List.foldLeft xs z Mul.mul = z * List.product xs :=
  match xs with
    | [] => Eq.sym (mul.mulOne z)
    | [x, ..xs] =>
      calc List.foldLeft xs (z * x) Mul.mul
        _ = (z * x) * List.product xs := List.productFrom xs (z * x)
        _ = z * (x * List.product xs) := mul.assoc z x (List.product xs)
        _ = z * List.foldLeft xs x Mul.mul := Eq.cong (t => z * t) (Eq.sym (List.productFrom xs x))
        _ = z * List.product [x, ..xs] := Eq.cong (t => z * List.foldLeft xs t Mul.mul) (Eq.sym (mul.oneMul x))

theorem List.productCons ∀ [auto mul: Mul a] (x: a) (xs: List a): List.product [x, ..xs] = x * List.product xs :=
  Eq.trans (Eq.cong (t => List.foldLeft xs t Mul.mul) (mul.oneMul x)) (List.productFrom xs x)

theorem List.productReverseOnto ∀ (xs acc: List Nat):
    List.product (List.reverseOnto xs acc) = List.product xs * List.product acc :=
  match xs with
    | [] => ring
    | [x, ..xs] => rewrite List.productReverseOnto xs [x, ..acc], List.productCons x acc, List.productCons x xs in ring

theorem List.productReverse ∀ (xs: List Nat): List.product (List.reverse xs) = List.product xs :=
  rewrite List.productReverseOnto xs [] in ring

--| Taking away a smaller sum term by term.
theorem List.sumBySplit ∀ (xs: List a) (f g: a → Nat)
    (h: ∀ (x: a) => g x ≤ f x):
    List.sumBy xs f = List.sumBy xs g + List.sumBy xs (x => f x - g x) :=
  calc List.sumBy xs f
    _ = List.sumBy xs (x => g x + (f x - g x)) :=
      List.sumByCong xs f (x => g x + (f x - g x)) (x => Eq.sym (Nat.addSubCancel (g x) (f x) (h x)))
    _ = List.sumBy xs g + List.sumBy xs (x => f x - g x) := List.sumByAdd xs g (x => f x - g x)

theorem List.sumByLe ∀ (xs: List a) (f g: a → Nat) (h: ∀ (x: a) => g x ≤ f x): List.sumBy xs g ≤ List.sumBy xs f :=
  rewrite List.sumBySplit xs f g h in Nat.leAddRight (List.sumBy xs g) (List.sumBy xs (x => f x - g x))

theorem List.sumBySub ∀ (xs: List a) (f g: a → Nat)
    (h: ∀ (x: a) => g x ≤ f x):
    List.sumBy xs f - List.sumBy xs g = List.sumBy xs (x => f x - g x) :=
  rewrite List.sumBySplit xs f g h in Nat.addSubLeft (List.sumBy xs g) (List.sumBy xs (x => f x - g x))

--| A filter that keeps more keeps at least as large a sum.
theorem List.sumByFilterMono ∀ (keep1 keep2: a → Bool) (value: a → Nat) (xs: List a)
    (included: ∀ (x: a) => keep1 x = True → keep2 x = True):
    List.sumBy (List.filter xs keep1) value ≤ List.sumBy (List.filter xs keep2) value :=
  rewrite List.sumByFilter xs value keep1, List.sumByFilter xs value keep2 in
    List.sumByLe xs (x => if keep2 x then value x else 0) (x => if keep1 x then value x else 0) (x =>
      match kept: keep1 x with
        | True => rewrite included x kept in Nat.leRefl (value x)
        | False => Nat.zeroLe (if keep2 x then value x else 0))

--| Counting with a test that passes wherever another does, on the list's
--| elements, counts at least as many.
theorem List.countLeMem ∀ (xs: List a) (p q: a → Bool)
    (weaker: ∀ (x: a) (m: List.Mem x xs) => p x = True → q x = True):
    List.count xs p ≤ List.count xs q :=
  match xs with
    | [] => Nat.leRefl 0
    | [x, ..rest] =>
      let below := List.countLeMem rest p q (y m => weaker y (Inr m))
      rewrite List.countCons rest x p, List.countCons rest x q in
        match passes: p x with
          | True => rewrite weaker x (Inl rfl) passes in below
          | False => Nat.leTrans _ _ _ below (Nat.leAddLeft (Bool.toNat (q x)) (List.count rest q))

--| Counting with a test that passes wherever another does counts strictly more when some element passes it but not the other.
theorem List.countLtMem: ∀ (xs: List a) (p q: a → Bool) => (∀ (x: a) (m: List.Mem x xs) => p x = True → q x = True)
      → ∀ (y: a) => List.Mem y xs → q y = True → p y = False → List.count xs p < List.count xs q
  | [], p, q, weaker, y, none, passes, fails => Void.exfalso none
  | [x, ..rest], p, q, weaker, y, Inl same, passes, fails =>
    rewrite List.countCons rest x p, List.countCons rest x q, same, passes, fails in
      List.countLeMem rest p q (z m => weaker z (Inr m))
  | [x, ..rest], p, q, weaker, y, Inr later, passes, fails =>
    let below := List.countLtMem rest p q (z m => weaker z (Inr m)) y later passes fails
    rewrite List.countCons rest x p, List.countCons rest x q in
      match kept: p x with
        | True => rewrite weaker x (Inl rfl) kept in below
        | False => Nat.leTrans _ _ _ below (Nat.leAddLeft (Bool.toNat (q x)) (List.count rest q))

--| `all` is "no element fails", so a permutation keeps it.
theorem List.allNotAny ∀ (xs: List a) (p: a → Bool): List.all xs p = ¬(List.any xs (x => ¬(p x))) := match xs with
  | [] => rfl
  | [x, ..xs] =>
    match e: p x with
      | True => List.allNotAny xs p
      | False => rfl

--| "No x is related to any y" read either way round.
theorem List.allNotAnyComm ∀ (related: a → b → Bool) (xs: List a) (ys: List b):
    List.all xs (x => ¬(List.any ys (y => related x y))) = List.all ys (y => ¬(List.any xs (x => related x y))) :=
  match xs with
    | [] => Eq.sym (List.allTrue ys (y => True) (y => rfl))
    | [x, ..xs] =>
      let unfolded :=
        List.allCong ys
          (y => ¬(List.any [x, ..xs] (x2 => related x2 y)))
          (y => ¬(related x y) ∧ ¬(List.any xs (x2 => related x2 y)))
          (y =>
            match r: related x y with
              | True => rfl
              | False => rfl)
      rewrite unfolded,
          List.allAnd ys (y => ¬(related x y)) (y => ¬(List.any xs (x2 => related x2 y))),
          <- List.allNotAnyComm related xs ys,
          List.allNotAny ys (y => ¬(related x y)) in
        rewrite List.anyCong ys (y => ¬(¬(related x y))) (y => related x y) (y => cases) in rfl

theorem List.allPerm ∀ (xs ys: List a) (h: List.Perm xs ys) (p: a → Bool): List.all xs p = List.all ys p :=
  rewrite List.allNotAny xs p, List.allNotAny ys p, List.anyPerm xs ys h (x => ¬(p x)) in rfl

theorem List.sortOnEq ∀ [auto ord: Ord k] (xs: List a) (key: a → k):
    List.sortOn xs key = List.sortBy xs (x y => Ord.compare (key x) (key y)) :=
  rfl

theorem List.sortOnPerm ∀ [auto ord: Ord k] (xs: List a) (key: a → k): List.Perm (List.sortOn xs key) xs :=
  List.sortByPerm xs (x y => Ord.compare (key x) (key y))

--| The keys of the sorted list are the sorted keys.
theorem List.sortOnMap ∀ [auto ord: Ord k] (xs: List a) (key: a → k):
    List.map (List.sortOn xs key) key = List.sort (List.map xs key) :=
  List.sortByMap xs key Ord.compare (x y => Ord.compare (key x) (key y)) (x y => rfl)

-- dedup ---------------------------------------------------------------------

--| What `List.dedupAfter` keeps was in the list.
theorem List.memDedupAfter ∀ [auto eq: DecEq a] (x previous: a) (xs: List a)
    (m: List.Mem x (List.dedupAfter previous xs)):
    List.Mem x xs :=
  match xs with
    | [y, ..ys] =>
      match e: y == previous with
        | True => Inr (List.memDedupAfter x previous ys m)
        | False =>
          match m with
            | Inl q => Inl q
            | Inr rest => Inr (List.memDedupAfter x y ys rest)

--| `List.dedupAfter` drops only elements equal to the one before.
theorem List.memDedupAfterIntro ∀ [auto eq: DecEq a] (x previous: a) (xs: List a)
    (m: List.Mem x xs):
    (previous = x) ∨ (List.Mem x (List.dedupAfter previous xs)) :=
  match xs with
    | [y, ..ys] =>
      match e: y == previous with
        | True =>
          match m with
            | Inl q => Inl (Eq.trans (Eq.sym e.read) q)
            | Inr rest => List.memDedupAfterIntro x previous ys rest
        | False =>
          match m with
            | Inl q => Inr (Inl q)
            | Inr rest =>
              match List.memDedupAfterIntro x y ys rest with
                | Inl q => Inr (Inl q)
                | Inr later => Inr (Inr later)

--| What `List.dedup` keeps was in the list.
theorem List.memDedupElim ∀ [auto eq: DecEq a] (x: a) (xs: List a) (m: List.Mem x (List.dedup xs)): List.Mem x xs :=
  match xs, m with
    | [], m => m
    | [y, ..ys], Inl q => Inl q
    | [y, ..ys], Inr rest => Inr (List.memDedupAfter x y ys rest)

--| `List.dedup` keeps every value.
theorem List.memDedupIntro ∀ [auto eq: DecEq a] (x: a) (xs: List a) (m: List.Mem x xs): List.Mem x (List.dedup xs) :=
  match xs, m with
    | [], m => m
    | [y, ..ys], Inl q => Inl q
    | [y, ..ys], Inr rest =>
      match List.memDedupAfterIntro x y ys rest with
        | Inl q => Inl q
        | Inr later => Inr later

--| `List.dedup` keeps a list sorted.
theorem List.sortedDedupAfter ∀ [auto eq: DecEq a] (le: a → a → Bool) (previous: a) (xs: List a)
    (s: List.Sorted le [previous, ..xs]):
    List.Sorted le [previous, ..List.dedupAfter previous xs] :=
  match xs, s with
    | [], s => s
    | [y, ..ys], Both first rest =>
      match e: y == previous with
        | True => List.sortedDedupAfter le previous ys (rewrite e.read at rest)
        | False => Both first (List.sortedDedupAfter le y ys rest)

theorem List.sortedDedup ∀ [auto eq: DecEq a] (le: a → a → Bool) (xs: List a)
    (s: List.Sorted le xs):
    List.Sorted le (List.dedup xs) :=
  match xs with
    | [] => s
    | [y, ..ys] => List.sortedDedupAfter le y ys s

--| A sum over the first n + 1 numbers is the first term and the sum over the rest.
theorem List.sumByRangeSucc ∀ (f: Nat → Nat) (n: Nat):
    List.sumBy (List.range 0 (Succ n)) f = f 0 + List.sumBy (List.range 0 n) (i => f (Succ i)) :=
  rewrite List.sumByCons (List.rangeFrom n 1) 0 f, List.sumByRangeShift f n 0 in rfl

--| Removing one element keeps the rest: everything left in
--| `ys.removeFirst x` was in `ys`.
theorem List.memOfRemoveFirst ∀ [auto eq: DecEq a] (ys: List a) (x y: a) (member: y ∈ ys.removeFirst x): y ∈ ys :=
  match ys with
    | [first, ..ys] =>
      match e: first == x with
        | True => Inr member
        | False =>
          match member with
            | Inl same => Inl same
            | Inr later => Inr (List.memOfRemoveFirst ys x y later)

--| `removeFirst x` loses only `x`: an element different from `x` that was in
--| the list is still there.
theorem List.memRemoveFirst ∀ [auto eq: DecEq a] (ys: List a) (x y: a)
    (apart: y ≠ x)
    (member: y ∈ ys):
    y ∈ ys.removeFirst x :=
  match ys with
    | [first, ..ys] =>
      match e: first == x with
        | True =>
          match member with
            | Inl same => Void.exfalso (apart (Eq.trans (Eq.sym same) e.read))
            | Inr later => later
        | False =>
          match member with
            | Inl same => Inl same
            | Inr later => Inr (List.memRemoveFirst ys x y apart later)

--| Removing an element from a list without repeats leaves a list without
--| repeats that no longer holds the element.
theorem List.distinctRemoveFirst ∀ [auto eq: DecEq a] (ys: List a) (x: a) (h: ys.Distinct):
    (ys.removeFirst x).Distinct ∧ x ∉ ys.removeFirst x :=
  match ys, h with
    | [], distinct => Both Trivial (member => member)
    | [first, ..ys], (Both fresh distinct) =>
      match e: first == x with
        | True => Both distinct (rewrite <- e.read in fresh)
        | False =>
          match List.distinctRemoveFirst ys x distinct with
            | Both restDistinct absent =>
              Both (Both (member => fresh (List.memOfRemoveFirst ys x first member)) restDistinct) (member =>
                match member with
                  | Inl same => e.read same
                  | Inr later => absent later)

--| The terms where `f` is not 0 that `ys` has are in `rest`, once `x` is taken from both.
theorem List.sumByDistinctNonzeroThere ∀ [auto eq: DecEq a] (f: a → Nat) (x: a) (rest ys: List a)
    (fresh: ¬(x ∈ rest))
    (there: ∀ (y: a) => f y ≠ 0 → y ∈ [x, ..rest] → y ∈ ys):
    (∀ (y: a) => f y ≠ 0 → y ∈ rest → y ∈ ys.removeFirst x) :=
  y nonzero member =>
    List.memRemoveFirst ys x y (same => fresh (Eq.subst (z => z ∈ rest) same member)) (there y nonzero (Inr member))

--| The terms where `f` is not 0 that `rest` has are in `ys`, once `x` is taken from both.
theorem List.sumByDistinctNonzeroBack ∀ [auto eq: DecEq a] (f: a → Nat) (x: a) (rest ys: List a)
    (absent: ¬(x ∈ ys.removeFirst x))
    (back: ∀ (y: a) => f y ≠ 0 → y ∈ ys → y ∈ [x, ..rest]):
    (∀ (y: a) => f y ≠ 0 → y ∈ ys.removeFirst x → y ∈ rest) :=
  y nonzero member =>
    match back y nonzero (List.memOfRemoveFirst ys x y member) with
      | Inl same => Void.exfalso (absent (Eq.subst (z => z ∈ ys.removeFirst x) (Eq.sym same) member))
      | Inr later => later

--| Two lists without repeats that hold the same elements where `f` is not 0
--| have the same `sumBy f`: elements where `f` is 0 add nothing, so the lists
--| may differ in those.
theorem List.sumByDistinctNonzero ∀ [auto eq: DecEq a] (f: a → Nat) (xs ys: List a)
    (distinctX: xs.Distinct) (distinctY: ys.Distinct)
    (there: ∀ (x: a) => f x ≠ 0 → x ∈ xs → x ∈ ys)
    (back: ∀ (x: a) => f x ≠ 0 → x ∈ ys → x ∈ xs):
    xs.sumBy f = ys.sumBy f :=
  match xs, distinctX with
    | [], distinctX =>
      Eq.sym
        (List.sumByZeroIntro ys f (x member =>
          match zero: f x with
            | 0 => rfl
            | Succ more => Void.exfalso (back x (rewrite zero in Nat.succNotZero more) member)))
    | [x, ..rest], (Both fresh distinctRest) =>
      Eq.trans
        (List.sumByCons rest x f)
        (match zero: f x with
          | 0 =>
            List.sumByDistinctNonzero f rest ys distinctRest distinctY
              (y nonzero member => there y nonzero (Inr member))
              (y nonzero member =>
                match back y nonzero member with
                  | Inl same => Void.exfalso (nonzero (rewrite <- same in zero))
                  | Inr later => later)
          | Succ more =>
            let nonzero: f x ≠ 0 := rewrite zero in Nat.succNotZero more
            let found := there x nonzero (Inl rfl)
            match List.distinctRemoveFirst ys x distinctY with
              | Both restDistinct absent =>
                Eq.trans
                  (Eq.cong
                    (total => f x + total)
                    (List.sumByDistinctNonzero f rest
                      (ys.removeFirst x)
                      distinctRest
                      restDistinct
                      (List.sumByDistinctNonzeroThere f x rest ys fresh there)
                      (List.sumByDistinctNonzeroBack f x rest ys absent back)))
                  (Eq.sym (List.sumByRemoveFirst ys x found f)))
