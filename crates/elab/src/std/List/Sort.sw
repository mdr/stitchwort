-- Sorting: merge sort and its proofs (sorted, a permutation, the same length),
-- with the Nat and List lemmas around them (sums of lists, Gauss, counting
-- occurrences). This file was the prelude's "Sorting" section; the declarations
-- that the core or a later section of the prelude uses stayed there, and its
-- opening `Bool` lemmas are now std/Bool/Bool.sw.
--
-- A library file is written like the prelude: names are as they are in the
-- namespaces they go in (`List.sort` is `Std.List.sort`), so one file can add
-- to several namespaces. It is checked when a program uses something in it.

-- `<=` is total: if `m <= n` is false, then `n <= m`.
theorem Nat.leqTotal (m: Nat) (n: Nat) (h: Nat.leq m n = False): Nat.leq n m = True := Nat.lessLe n m (Nat.leqFalse m n h)

-- Sums of lists: one element at a time, sums of intervals (Gauss), and
-- rewriting under `map`, `filter` and `foldLeft`.
theorem Nat.addSwap (a: Nat) (b: Nat) (c: Nat) (d: Nat): (a + b) + (c + d) = (a + c) + (b + d) := ring

-- Sums from a starting total, one element at a time and of two lists, for
-- any `Add` (docs/proposals/interfaces.md §7.7). At `Nat` they state the
-- facts about `Nat` sums, by computation.
theorem List.sumFrom [auto add: Add a]: (xs: List a) → (z: a) → List.foldLeft xs z Add.add = z + List.sum xs
  | Nil, z => Eq.sym (Add.addZero z)
  | Cons x xs, z =>
    calc List.foldLeft xs (z + x) Add.add
      _ = (z + x) + List.sum xs := List.sumFrom xs (z + x)
      _ = z + (x + List.sum xs) := add.assoc z x (List.sum xs)
      _ = z + List.foldLeft xs x Add.add := Eq.cong (t => z + t) (Eq.sym (List.sumFrom xs x))
      _ = z + List.sum (Cons x xs) := Eq.cong (t => z + List.foldLeft xs t Add.add) (Eq.sym (add.zeroAdd x))

theorem List.sumCons [auto add: Add a] (x: a) (xs: List a): List.sum (Cons x xs) = x + List.sum xs :=
  Eq.trans (Eq.cong (t => List.foldLeft xs t Add.add) (add.zeroAdd x)) (List.sumFrom xs x)

theorem List.sumAppend [auto add: Add a]: (xs: List a) → (ys: List a) →
    List.sum (List.append xs ys) = List.sum xs + List.sum ys
  | Nil, ys => Eq.sym (add.zeroAdd (List.sum ys))
  | Cons x xs, ys =>
    Eq.trans (List.sumCons x (List.append xs ys))
      (Eq.trans (Eq.cong (t => x + t) (List.sumAppend xs ys))
        (Eq.trans (Eq.sym (add.assoc x (List.sum xs) (List.sum ys)))
          (Eq.cong (t => t + List.sum ys) (Eq.sym (List.sumCons x xs)))))

theorem List.sumByMulLeft: (xs: List a) → (c: Nat) → (f: a → Nat) → List.sumBy xs (x => c * f x) = c * List.sumBy xs f
  | Nil, c, f => ring
  | Cons x xs, c, f => rewrite List.sumByCons xs x (y => c * f y), List.sumByCons xs x f, List.sumByMulLeft xs c f in ring

theorem List.sumByRangeShift (f: Nat → Nat): (n: Nat) → (s: Nat) →
    List.sumBy (List.rangeFrom n (Succ s)) f = List.sumBy (List.rangeFrom n s) (i => f (Succ i))
  | Zero, s => rfl
  | Succ n, s =>
    Eq.trans (List.sumByCons (List.rangeFrom n (Succ (Succ s))) (Succ s) f)
      (Eq.trans (Eq.cong (t => f (Succ s) + t) (List.sumByRangeShift f n (Succ s)))
        (Eq.sym (List.sumByCons (List.rangeFrom n (Succ s)) s (i => f (Succ i)))))

-- A sum over `s, s + 1, ..., s + n - 1`, as one over `0, 1, ..., n - 1`.
theorem List.sumByRangeOffset (f: Nat → Nat): (s: Nat) → (n: Nat) →
    List.sumBy (List.rangeFrom n s) f = List.sumBy (List.range n) (i => f (s + i))
  | Zero, n => List.sumByCong (List.range n) f (i => f (0 + i)) (i => rfl)
  | Succ s, n => Eq.trans (List.sumByRangeShift f n s) (List.sumByRangeOffset (i => f (Succ i)) s n)

theorem List.sumByRangeOffsetExample: List.sumBy (List.rangeFrom 3 10) (i => i) = List.sumBy (List.range 3) (i => 10 + i) := rfl

-- Gauss: twice the sum of `x, x + 1, ..., x + d` is `(d + 1) * (x + (x + d))`.
theorem List.gaussSum: (d: Nat) → (x: Nat) →
    List.sum (List.rangeFrom (Succ d) x) + List.sum (List.rangeFrom (Succ d) x) = Succ d * (x + (x + d))
  | Zero, x => ring
  | Succ d, x => rewrite List.sumCons x (List.rangeFrom (Succ d) (Succ x)) in ring [List.gaussSum d (Succ x)]

-- `x + (x + 1) + ... + (y - 1)`
def Nat.span (x: Nat) (y: Nat): Nat := List.sum (List.rangeFrom (y - x) x)

theorem Nat.spanEmpty (x: Nat) (y: Nat) (h: y ≤ x): Nat.span x y = 0 := Eq.cong (t => List.sum (List.rangeFrom t x)) (Nat.subEqZero y x h)

theorem Nat.spanStep (s: Nat) (y: Nat) (h: Succ s ≤ y): Nat.span s y = s + Nat.span (Succ s) y :=
  Eq.trans (Eq.cong (t => List.sum (List.rangeFrom t s)) (Nat.subSuccRight s y h)) (List.sumCons s (List.rangeFrom (y - Succ s) (Succ s)))

-- The closed form is the sum of `lo..hi`.
theorem Nat.gaussSpan (d: Nat) (lo: Nat) (hi: Nat) (h: lo ≤ hi): d * ((lo + hi) * (hi - lo + 1) / 2) = d * Nat.span lo (Succ hi) :=
  Eq.trans
    (Eq.cong (t => d * (t / 2))
      (Eq.trans (Eq.cong (t => (lo + t) * (hi - lo + 1)) (Eq.sym (Nat.addSubCancel lo hi h)))
        (Eq.trans (Eq.cong (t => (lo + (lo + (hi - lo))) * t) (Nat.addOne (hi - lo)))
          (Eq.trans (Nat.mulComm (lo + (lo + (hi - lo))) (Succ (hi - lo))) (Eq.sym (List.gaussSum (hi - lo) lo))))))
    (Eq.trans (Eq.cong (t => d * t) (Nat.halfDouble (List.sum (List.rangeFrom (Succ (hi - lo)) lo))))
      (Eq.sym (Eq.cong (t => d * List.sum (List.rangeFrom t lo)) (Nat.subSuccRight lo (Succ hi) h))))

-- first + (first + 1) + ... + last: an arithmetic series, the number of
-- terms times their average. There are `last + 1 - first` terms, which is 0
-- when first > last (as in `List.between`), so then the sum is 0.
def Nat.sumBetween (first: Nat) (last: Nat): Nat := (first + last) * (last + 1 - first) / 2

-- Gauss's formula is the sum of the numbers from first to last, for any bounds.
theorem Nat.sumBetweenCorrect (first: Nat) (last: Nat): Nat.sumBetween first last = (List.between first last).sum :=
  match h: Nat.leq first last with
    | True =>
      calc Nat.sumBetween first last
        _ = (first + last) * (last - first + 1) / 2 := rewrite Nat.addOneSub last first h
        _ = 1 * ((first + last) * (last - first + 1) / 2) := ring
        _ = 1 * Nat.span first (Succ last) := Nat.gaussSpan 1 first last h
        _ = Nat.span first (Succ last) := ring
        _ = (List.between first last).sum := Eq.cong (t => List.sum (List.rangeFrom (t - first) first)) (Eq.sym (Nat.addOne last))
    | False =>
      calc Nat.sumBetween first last
        _ = (first + last) * 0 / 2 := rewrite Nat.addOneSubEqZero last first h
        _ = 0 := rewrite Nat.mulZero (first + last)
        _ = (List.between first last).sum := rewrite Nat.addOneSubEqZero last first h

test "Nat.sumBetween" := Nat.sumBetween 3 7 == 25 ∧ Nat.sumBetween 5 5 == 5 ∧ Nat.sumBetween 1 100 == 5050

test "Nat.sumBetween, reversed bounds" := Nat.sumBetween 5 3 == 0 ∧ Nat.sumBetween 7 3 == 0 ∧ Nat.sumBetween 1 0 == 0

-- How many pairs `List.pairs` makes: n(n - 1)/2. One step of the count:
-- `x` is paired with the n others, and p is the number of pairs among those.
theorem List.pairsStep (n: Nat) (p: Nat) (h: p + p + n = n * n): (n + p) + (n + p) + Succ n = Succ n * Succ n :=
  ring [h]

-- Twice the number of pairs, and the number of elements, make n * n.
theorem List.lengthPairsDouble: (xs: List a) →
    List.length (List.pairs xs) + List.length (List.pairs xs) + List.length xs = List.length xs * List.length xs
  | Nil => rfl
  | Cons x xs =>
    rewrite List.lengthAppend (List.map xs (y => MkPair x y)) (List.pairs xs), List.lengthMap xs (y => MkPair x y)
      in List.pairsStep (List.length xs) (List.length (List.pairs xs)) (List.lengthPairsDouble xs)

theorem List.pairsDoubleSub: (n: Nat) → (p: Nat) → p + p + n = n * n → p + p = n * (n - 1)
  | Zero, p, h => ring [h]
  | Succ m, p, h => ring [h]

-- Twice the number of pairs is n * (n - 1).
theorem List.lengthPairsDoubled (xs: List a):
    List.length (List.pairs xs) + List.length (List.pairs xs) = List.length xs * (List.length xs - 1) :=
  List.pairsDoubleSub (List.length xs) (List.length (List.pairs xs)) (List.lengthPairsDouble xs)

-- n(n - 1)/2 pairs.
theorem List.lengthPairs (xs: List a): List.length (List.pairs xs) = List.length xs * (List.length xs - 1) / 2 :=
  rewrite Eq.sym (List.lengthPairsDoubled xs), Nat.halfDouble (List.length (List.pairs xs)) in rfl

-- `p` written n times: n times as long, and one more copy goes on the end.
theorem List.lengthConcatReplicate (p: List a): (n: Nat) → List.length (List.concat (List.replicate n p)) = n * List.length p
  | Zero => rfl
  | Succ n => Eq.trans (List.lengthAppend p (List.concat (List.replicate n p))) (Eq.cong (t => List.length p + t) (List.lengthConcatReplicate p n))

theorem List.concatReplicateSnoc (p: List a): (n: Nat) → List.concat (List.replicate (Succ n) p) = List.append (List.concat (List.replicate n p)) p
  | Zero => List.appendNil p
  | Succ n =>
    calc List.append p (List.concat (List.replicate (Succ n) p))
      _ = List.append p (List.append (List.concat (List.replicate n p)) p) := Eq.cong (List.append p) (List.concatReplicateSnoc p n)
      _ = List.append (List.append p (List.concat (List.replicate n p))) p := Eq.sym (List.appendAssoc p (List.concat (List.replicate n p)) p)

theorem List.lengthTake: (xs: List a) → (k: Nat) → k ≤ List.length xs → List.length (List.take xs k) = k
  | xs, Zero, h => rfl
  | Nil, Succ k, h => Void.exfalso (Bool.falseNotTrue h)
  | Cons x xs, Succ k, h => Eq.cong Succ (List.lengthTake xs k h)

theorem List.takeAll: (xs: List a) → (k: Nat) → List.length xs ≤ k → List.take xs k = xs
  | Nil, Zero, h => rfl
  | Cons x xs, Zero, h => Void.exfalso (Bool.falseNotTrue h)
  | Nil, Succ k, h => rfl
  | Cons x xs, Succ k, h => Eq.cong (Cons x) (List.takeAll xs k h)

-- Dropping n elements of a list at least n long leaves the rest.
theorem List.lengthDrop: (xs: List a) → (n: Nat) → n ≤ List.length xs → n + List.length (List.drop xs n) = List.length xs
  | xs, Zero, h => rfl
  | Nil, Succ n, h => Void.exfalso (Bool.falseNotTrue h)
  | Cons x xs, Succ n, h => Eq.cong Succ (List.lengthDrop xs n h)

theorem List.lengthDropExample: List.length (List.drop [1, 2, 3, 4, 5] 2) = 3 := rfl

theorem List.takeAppend: (xs: List a) → (ys: List a) → List.take (List.append xs ys) (List.length xs) = xs
  | Nil, ys => rfl
  | Cons x xs, ys => Eq.cong (Cons x) (List.takeAppend xs ys)

theorem List.headTake: (xs: List a) → (d: a) → (k: Nat) → 1 ≤ k → List.headOr (List.take xs k) d = List.headOr xs d
  | xs, d, Zero, h => Void.exfalso (Bool.falseNotTrue h)
  | Nil, d, Succ k, h => rfl
  | Cons x xs, d, Succ k, h => rfl

-- `x` when the condition holds, else 0: a term a sum may leave out.
def Nat.keepIf (x: Nat): Bool → Nat
  | True => x
  | False => 0

-- `if b then x else 0` is `keepIf x b`.
theorem Nat.ifKeep (x: Nat): (b: Bool) → (if b then x else 0) = Nat.keepIf x b
  | True => rfl
  | False => rfl

theorem List.sumByZero [auto add: Add c]: (xs: List a) → List.sumBy xs (x => Add.zero) = (Add.zero: c)
  | Nil => rfl
  | Cons x xs => Eq.trans (List.sumByCons xs x (x => Add.zero)) (Eq.trans (add.zeroAdd (List.sumBy xs (x => Add.zero))) (List.sumByZero xs))

theorem Nat.keepIfZero: (b: Bool) → Nat.keepIf 0 b = 0
  | True => rfl
  | False => rfl

theorem Nat.keepIfOne: (b: Bool) → Nat.keepIf 1 b = Bool.toNat b
  | True => rfl
  | False => rfl

-- Keeping a sum is keeping each term.
theorem Nat.keepIfSumBy (g: a → Nat) (xs: List a): (b: Bool) → Nat.keepIf (List.sumBy xs g) b = List.sumBy xs (x => Nat.keepIf (g x) b)
  | True => rfl
  | False => Eq.sym (List.sumByZero [add := Nat.instAdd] xs)

-- `keepIf` as multiplying by 1 or 0.
theorem Nat.mulToNat (x: Nat): (a: Bool) → x * Bool.toNat a = Nat.keepIf x a
  | True => ring
  | False => ring

theorem Nat.keepIfKeepIf (x: Nat): (a: Bool) → (b: Bool) → Nat.keepIf (Nat.keepIf x a) b = x * Bool.toNat (a ∧ b)
  | True, True => ring
  | True, False => ring
  | False, True => ring
  | False, False => ring

theorem List.sumByAdd [auto add: Add c]: (xs: List a) → (f: a → c) → (g: a → c) → List.sumBy xs (x => f x + g x) = List.sumBy xs f + List.sumBy xs g
  | Nil, f, g => Eq.sym (add.zeroAdd Add.zero)
  | Cons x xs, f, g =>
    Eq.trans (List.sumByCons xs x (y => f y + g y))
      (Eq.trans (Eq.cong (t => (f x + g x) + t) (List.sumByAdd xs f g))
        (Eq.trans (Add.addSwap (f x) (g x) (List.sumBy xs f) (List.sumBy xs g))
          (Eq.sym (Eq.trans (Eq.cong (t => t + List.sumBy (Cons x xs) g) (List.sumByCons xs x f))
            (Eq.cong (t => (f x + List.sumBy xs f) + t) (List.sumByCons xs x g))))))

-- A double sum of two terms is two double sums.
theorem List.sumByNestedAdd (xs: List a) (ys: List b) (f: a → b → Nat) (g: a → b → Nat):
    List.sumBy xs (x => List.sumBy ys (y => f x y + g x y))
      = List.sumBy xs (x => List.sumBy ys (y => f x y)) + List.sumBy xs (x => List.sumBy ys (y => g x y)) :=
  Eq.trans
    (List.sumByCong xs _ _ (x => List.sumByAdd ys (y => f x y) (y => g x y)))
    (List.sumByAdd xs (x => List.sumBy ys (y => f x y)) (x => List.sumBy ys (y => g x y)))

theorem List.sumBySwap [auto add: Add c] (ys: List b): (xs: List a) → (h: a → b → c) →
    List.sumBy xs (x => List.sumBy ys (y => h x y)) = List.sumBy ys (y => List.sumBy xs (x => h x y))
  | Nil, h => Eq.sym (List.sumByZero ys)
  | Cons x xs, h =>
    Eq.trans (List.sumByCons xs x (x => List.sumBy ys (y => h x y)))
      (Eq.trans (Eq.cong (t => List.sumBy ys (y => h x y) + t) (List.sumBySwap ys xs h))
        (Eq.trans (Eq.sym (List.sumByAdd ys (y => h x y) (y => List.sumBy xs (x => h x y))))
          (List.sumByCong ys (y => h x y + List.sumBy xs (x => h x y))
            (y => List.sumBy (Cons x xs) (x => h x y)) (y => Eq.sym (List.sumByCons xs x (x => h x y))))))

theorem List.sumByMap [auto add: Add c]: (xs: List a) → (g: b → c) → (f: a → b) → List.sumBy (List.map xs f) g = List.sumBy xs (x => g (f x))
  | Nil, g, f => rfl
  | Cons x xs, g, f =>
    Eq.trans (List.sumByCons (List.map xs f) (f x) g)
      (Eq.trans (Eq.cong (t => g (f x) + t) (List.sumByMap xs g f)) (Eq.sym (List.sumByCons xs x (x => g (f x)))))

-- Summing over a `flatMap` is summing the sums.
theorem List.sumByFlatMap [auto add: Add c]: (xs: List a) → (f: b → c) → (g: a → List b) → List.sumBy (List.flatMap xs g) f = List.sumBy xs (x => List.sumBy (g x) f)
  | Nil, f, g => rfl
  | Cons x xs, f, g =>
    Eq.trans (List.sumByAppend (g x) (List.flatMap xs g) f)
      (Eq.trans (Eq.cong (t => List.sumBy (g x) f + t) (List.sumByFlatMap xs f g)) (Eq.sym (List.sumByCons xs x (x => List.sumBy (g x) f))))

-- Summing over a `filter` is summing the terms that pass, the rest counting 0.
theorem List.sumByFilter [auto add: Add c]: (xs: List a) → (f: a → c) → (p: a → Bool) → List.sumBy (List.filter xs p) f = List.sumBy xs (x => if p x then f x else Add.zero)
  | Nil, f, p => rfl
  | Cons x xs, f, p =>
    Bool.inspect (p x) (b => List.sumBy (List.filter (Cons x xs) p) f = List.sumBy (Cons x xs) (x => if p x then f x else Add.zero))
      (h => Eq.trans (Eq.cong (.sumBy f) (List.filterKeep xs p x h))
        (Eq.trans (List.sumByCons (List.filter xs p) x f)
          (Eq.trans (Eq.cong (t => f x + t) (List.sumByFilter xs f p))
            (Eq.sym (Eq.trans (List.sumByCons xs x (x => if p x then f x else Add.zero)) (Eq.cong (t => (if t then f x else Add.zero) + List.sumBy xs (x => if p x then f x else Add.zero)) h))))))
      (h => Eq.trans (Eq.cong (.sumBy f) (List.filterSkip xs p x h))
        (Eq.trans (List.sumByFilter xs f p)
          (Eq.trans (Eq.sym (add.zeroAdd (List.sumBy xs (x => if p x then f x else Add.zero))))
            (Eq.sym (Eq.trans (List.sumByCons xs x (x => if p x then f x else Add.zero)) (Eq.cong (t => (if t then f x else Add.zero) + List.sumBy xs (x => if p x then f x else Add.zero)) h))))))

theorem List.sumFilter: (xs: List Nat) → (p: Nat → Bool) → List.sum (List.filter xs p) = List.sumBy xs (x => Nat.keepIf x (p x))
  | Nil, p => rfl
  | Cons x xs, p =>
    Bool.inspect (p x) (c => List.sum (List.filter (Cons x xs) p) = List.sumBy (Cons x xs) (x => Nat.keepIf x (p x)))
      (h => Eq.trans (Eq.cong List.sum (List.filterKeep xs p x h))
        (Eq.trans (List.sumCons x (List.filter xs p))
          (Eq.trans (Eq.cong (t => Nat.keepIf x t + List.sum (List.filter xs p)) (Eq.sym h))
            (Eq.trans (Eq.cong (t => Nat.keepIf x (p x) + t) (List.sumFilter xs p))
              (Eq.sym (List.sumByCons xs x (x => Nat.keepIf x (p x))))))))
      (h => Eq.trans (Eq.cong List.sum (List.filterSkip xs p x h))
        (Eq.trans (Eq.cong (t => Nat.keepIf x t + List.sum (List.filter xs p)) (Eq.sym h))
          (Eq.trans (Eq.cong (t => Nat.keepIf x (p x) + t) (List.sumFilter xs p))
            (Eq.sym (List.sumByCons xs x (x => Nat.keepIf x (p x)))))))

-- Sums over a run of numbers that pick nothing, or pick one.
theorem List.sumRangeNone (q: Nat → Bool) (g: Nat → Nat): (c: Nat) → (s: Nat) →
    ((b: Nat) → s ≤ b → b < s + c → q b = False) →
    List.sumBy (List.rangeFrom c s) (b => Nat.keepIf (g b) (q b)) = 0
  | Zero, s, h => rfl
  | Succ c, s, h =>
    Eq.trans (List.sumByCons (List.rangeFrom c (Succ s)) s (b => Nat.keepIf (g b) (q b)))
      (Eq.trans (Eq.cong (t => Nat.keepIf (g s) t + List.sumBy (List.rangeFrom c (Succ s)) (b => Nat.keepIf (g b) (q b))) (h s (Nat.leRefl s) (Nat.ltAddSuccSelf s c)))
        (List.sumRangeNone q g c (Succ s) (b hb1 hb2 => h b (Nat.leTrans s (Succ s) b (Nat.leSucc s) hb1) (Nat.ltAddSucc s c b hb2))))

theorem List.sumRangeOne (q: Nat → Bool) (g: Nat → Nat) (v: Nat) (hv: q v = True) (uniq: (b: Nat) → q b = True → b = v):
    (c: Nat) → (s: Nat) → s ≤ v → v < s + c → List.sumBy (List.rangeFrom c s) (b => Nat.keepIf (g b) (q b)) = g v
  | Zero, s, h1, h2 => Void.exfalso (Nat.lessIrrefl v (Nat.leTrans (Succ v) s v (Nat.ltCongRight v (s + 0) s ring h2) h1))
  | Succ c, s, h1, h2 =>
    Bool.inspect (q s) (u => List.sumBy (List.rangeFrom (Succ c) s) (b => Nat.keepIf (g b) (q b)) = g v)
      (hs => Eq.trans (List.sumByCons (List.rangeFrom c (Succ s)) s (b => Nat.keepIf (g b) (q b)))
        (Eq.trans (Eq.cong (t => Nat.keepIf (g s) t + List.sumBy (List.rangeFrom c (Succ s)) (b => Nat.keepIf (g b) (q b))) hs)
          (Eq.trans (Eq.cong (t => g s + t)
              (List.sumRangeNone q g c (Succ s) (b hb1 hb2 =>
                Bool.inspect (q b) (u => u = False)
                  (t => Void.exfalso (Nat.lessIrrefl s (Nat.leCongRight (Succ s) b s (Eq.trans (uniq b t) (Eq.sym (uniq s hs))) hb1)))
                  (f => rfl))))
            (Eq.trans (Nat.addZero (g s)) (Eq.cong g (uniq s hs))))))
      (hs => Eq.trans (List.sumByCons (List.rangeFrom c (Succ s)) s (b => Nat.keepIf (g b) (q b)))
        (Eq.trans (Eq.cong (t => Nat.keepIf (g s) t + List.sumBy (List.rangeFrom c (Succ s)) (b => Nat.keepIf (g b) (q b))) hs)
          (List.sumRangeOne q g v hv uniq c (Succ s)
            (Nat.leNeSucc s v h1 (e => Bool.trueNotFalse (Eq.trans (Eq.sym hv) (Eq.trans (Eq.cong q (Eq.sym e)) hs))))
            (Nat.ltSuccAdd s c v h2))))

theorem List.sumByCongRange [auto add: Add c] (f: Nat → c) (g: Nat → c): (c: Nat) → (s: Nat) → ((x: Nat) → s ≤ x → x < s + c → f x = g x) →
    List.sumBy (List.rangeFrom c s) f = List.sumBy (List.rangeFrom c s) g
  | Zero, s, h => rfl
  | Succ c, s, h =>
    Eq.trans (List.sumByCons (List.rangeFrom c (Succ s)) s f)
      (Eq.trans (Eq.cong (t => t + List.sumBy (List.rangeFrom c (Succ s)) f) (h s (Nat.leRefl s) (Nat.ltAddSuccSelf s c)))
        (Eq.trans (Eq.cong (t => g s + t) (List.sumByCongRange f g c (Succ s) (x hx1 hx2 => h x (Nat.leTrans s (Succ s) x (Nat.leSucc s) hx1) (Nat.ltAddSucc s c x hx2))))
          (Eq.sym (List.sumByCons (List.rangeFrom c (Succ s)) s g))))

-- A sum over a run of numbers that is 0 has every term 0.
theorem List.sumRangeZero (f: Nat → Nat): (c: Nat) → (s: Nat) → List.sumBy (List.rangeFrom c s) f = 0 →
    (x: Nat) → s ≤ x → x < s + c → f x = 0
  | Zero, s, h, x, h1, h2 => Void.exfalso (Nat.lessIrrefl x (Nat.leTrans (Succ x) s x (Nat.ltCongRight x (s + 0) s ring h2) h1))
  | Succ c, s, h, x, h1, h2 =>
    let parts := Nat.addEqZero (f s) (List.sumBy (List.rangeFrom c (Succ s)) f) (Eq.trans (Eq.sym (List.sumByCons (List.rangeFrom c (Succ s)) s f)) h)
    match e: Nat.equal s x with
      | True => rewrite <- Nat.equalSound s x e in And.left parts
      | False =>
        List.sumRangeZero f c (Succ s) (And.right parts) x (Nat.leNeSucc s x h1 (Nat.equalFalse s x e)) (Nat.ltSuccAdd s c x h2)

-- Sums over the ids of a run that pick out `y`.
theorem List.sumRangeEq (y: Nat) (c: Nat) (s: Nat) (h1: s ≤ y) (h2: y < s + c): List.sumBy (List.rangeFrom c s) (x => Nat.keepIf x (y == x)) = y :=
  List.sumRangeOne (x => y == x) (x => x) y (Decidable.toBoolOf (Nat.decEq y y) rfl) (b h => Eq.sym (Decidable.toBoolSound (Nat.decEq y b) h)) c s h1 h2

theorem List.sumRangeEqNone (y: Nat) (c: Nat) (s: Nat) (h: (x: Nat) → s ≤ x → x < s + c → Not (y = x)): List.sumBy (List.rangeFrom c s) (x => Nat.keepIf x (y == x)) = 0 :=
  List.sumRangeNone (x => y == x) (x => x) c s (b h1 h2 => Decidable.toBoolOfNot (Nat.decEq y b) (h b h1 h2))

-- A sum over 0, 1, …, n - 1 that picks out `v`: `g v`, which must be 0
-- when `v` is past the end.
theorem List.sumRangePick (g: Nat → Nat) (n: Nat) (v: Nat) (hz: n ≤ v → g v = 0):
    List.sumBy (List.range n) (x => Nat.keepIf (g x) (Nat.equal v x)) = g v :=
  match e: Nat.leq (Succ v) n with
    | True => List.sumRangeOne (x => Nat.equal v x) g v (Nat.equalRefl v) (b h => Eq.sym (Nat.equalSound v b h)) n 0 (Nat.zeroLe v) e
    | False =>
      rewrite hz (Nat.leqFalse (Succ v) n e) in
        List.sumRangeNone (x => Nat.equal v x) g n 0
          (b h1 h2 => Nat.equalOfLess b v (Nat.leTrans (Succ b) n v h2 (Nat.leqFalse (Succ v) n e)))

-- `any` over a run of numbers: a witness out, a witness in.
theorem List.anyRangeElim (q: Nat → Bool) (goal: Prop): (c: Nat) → (s: Nat) → List.any (List.rangeFrom c s) q = True →
    ((k: Nat) → s ≤ k → k < s + c → q k = True → goal) → goal
  | Zero, s, h, k => Void.exfalso (Bool.falseNotTrue h)
  | Succ c, s, h, k =>
    Bool.inspect (q s) (u => goal)
      (t => k s (Nat.leRefl s) (Nat.ltAddSuccSelf s c) t)
      (f => List.anyRangeElim q goal c (Succ s)
        (Eq.trans (Eq.cong (b => Bool.ifThenElse b (u => True) (u => List.any (List.rangeFrom c (Succ s)) q)) (Eq.sym f)) h)
        (j h1 h2 hj => k j (Nat.leTrans s (Succ s) j (Nat.leSucc s) h1) (Nat.ltAddSucc s c j h2) hj))

theorem List.anyRangeIntro (q: Nat → Bool): (c: Nat) → (s: Nat) → (k: Nat) → s ≤ k → k < s + c → q k = True → List.any (List.rangeFrom c s) q = True
  | Zero, s, k, h1, h2, hk => Void.exfalso (Nat.lessIrrefl k (Nat.leTrans (Succ k) s k (Nat.ltCongRight k (s + 0) s ring h2) h1))
  | Succ c, s, k, h1, h2, hk =>
    Bool.inspect (q s) (u => List.any (List.rangeFrom (Succ c) s) q = True)
      (t => Eq.cong (b => Bool.ifThenElse b (u => True) (u => List.any (List.rangeFrom c (Succ s)) q)) t)
      (f => Eq.trans (Eq.cong (b => Bool.ifThenElse b (u => True) (u => List.any (List.rangeFrom c (Succ s)) q)) f)
        (List.anyRangeIntro q c (Succ s) k (Nat.leNeSucc s k h1 (e => Bool.trueNotFalse (Eq.trans (Eq.sym hk) (Eq.trans (Eq.cong q (Eq.sym e)) f)))) (Nat.ltSuccAdd s c k h2) hk))

-- `all` over a run of numbers: each element passes, and back. With a check
-- that computes to `True`, the first turns a finite computation into a fact
-- about every number of the run.
theorem List.allRangeElim (q: Nat → Bool): (c: Nat) → (s: Nat) → List.all (List.rangeFrom c s) q = True →
    (k: Nat) → s ≤ k → k < s + c → q k = True
  | Zero, s, h, k, h1, h2 => Void.exfalso (Nat.lessIrrefl k (Nat.leTrans (Succ k) s k (Nat.ltCongRight k (s + 0) s ring h2) h1))
  | Succ c, s, h, k, h1, h2 =>
    Bool.inspect (q s) (u => q k = True)
      (t => Bool.inspect (k == s) (u => q k = True)
        (e => rewrite <- Decidable.toBoolSound (Nat.decEq k s) e at t)
        (ne => List.allRangeElim q c (Succ s)
          (Eq.trans (Eq.cong (b => Bool.ifThenElse b (u => List.all (List.rangeFrom c (Succ s)) q) (u => False)) (Eq.sym t)) h)
          k (Nat.leNeSucc s k h1 (e => Bool.trueNotFalse (Eq.trans (Eq.sym (Decidable.toBoolOf (Nat.decEq k s) (Eq.sym e))) ne))) (Nat.ltSuccAdd s c k h2)))
      (f => Void.exfalso (Bool.trueNotFalse (Eq.trans (Eq.sym h) (Eq.cong (b => Bool.ifThenElse b (u => List.all (List.rangeFrom c (Succ s)) q) (u => False)) f))))

theorem List.allRangeIntro (q: Nat → Bool): (c: Nat) → (s: Nat) → ((k: Nat) → s ≤ k → k < s + c → q k = True) → List.all (List.rangeFrom c s) q = True
  | Zero, s, h => rfl
  | Succ c, s, h =>
    Eq.trans (Eq.cong (b => Bool.ifThenElse b (u => List.all (List.rangeFrom c (Succ s)) q) (u => False)) (h s (Nat.leRefl s) (Nat.ltAddSuccSelf s c)))
      (List.allRangeIntro q c (Succ s) (k h1 h2 => h k (Nat.leTrans s (Succ s) k (Nat.leSucc s) h1) (Nat.ltAddSucc s c k h2)))

theorem List.allRangeExample: List.all (List.rangeFrom 100 0) (k => k * k ≠ 2) = True := rfl

-- The first number of the run `start .. start + count - 1` that passes `passes` (`start + count` if
-- none does): a least witness, found by computation. Nothing before it passes,
-- and if some `k` of the run passes, so does it, and it is at most `k`.
@[noReceiver]
def Nat.firstFrom (passes: Nat → Bool): Nat → Nat → Nat
  | Zero, start => start
  | Succ count, start => if passes start then start else Nat.firstFrom passes count (Succ start)

theorem Nat.firstFromExample: Nat.firstFrom (k => Nat.leq 11 (k * k)) 9 1 = 4 := rfl

theorem Nat.firstFromStop (q: Nat → Bool) (c: Nat) (s: Nat) (h: q s = True): Nat.firstFrom q (Succ c) s = s :=
  Eq.cong (b => Bool.ifThenElse b (u => s) (u => Nat.firstFrom q c (Succ s))) h

theorem Nat.firstFromSkip (q: Nat → Bool) (c: Nat) (s: Nat) (h: q s = False): Nat.firstFrom q (Succ c) s = Nat.firstFrom q c (Succ s) :=
  Eq.cong (b => Bool.ifThenElse b (u => s) (u => Nat.firstFrom q c (Succ s))) h

theorem Nat.firstFromAtLeast (q: Nat → Bool): (c: Nat) → (s: Nat) → s ≤ Nat.firstFrom q c s
  | Zero, s => Nat.leRefl s
  | Succ c, s =>
    Bool.inspect (q s) (u => s ≤ Nat.firstFrom q (Succ c) s)
      (t => J (z p => s ≤ z) (Nat.leRefl s) (Eq.sym (Nat.firstFromStop q c s t)))
      (f => rewrite <- Nat.firstFromSkip q c s f at Nat.leTrans s (Succ s) (Nat.firstFrom q c (Succ s)) (Nat.leSucc s) (Nat.firstFromAtLeast q c (Succ s)))

theorem Nat.firstFromBefore (q: Nat → Bool): (c: Nat) → (s: Nat) → (j: Nat) → s ≤ j → j < Nat.firstFrom q c s → q j = False
  | Zero, s, j, h1, h2 => Void.exfalso (Nat.lessIrrefl j (Nat.leTrans (Succ j) s j h2 h1))
  | Succ c, s, j, h1, h2 =>
    Bool.inspect (q s) (u => q j = False)
      (t => Void.exfalso (Nat.lessIrrefl j (Nat.leTrans (Succ j) s j (Nat.ltCongRight j (Nat.firstFrom q (Succ c) s) s (Nat.firstFromStop q c s t) h2) h1)))
      (f => Bool.inspect (j == s) (u => q j = False)
        (e => rewrite <- Decidable.toBoolSound (Nat.decEq j s) e at f)
        (ne => Nat.firstFromBefore q c (Succ s) j
          (Nat.leNeSucc s j h1 (e => Bool.trueNotFalse (Eq.trans (Eq.sym (Decidable.toBoolOf (Nat.decEq j s) (Eq.sym e))) ne)))
          (Nat.ltCongRight j (Nat.firstFrom q (Succ c) s) (Nat.firstFrom q c (Succ s)) (Nat.firstFromSkip q c s f) h2)))

theorem Nat.firstFromFound (q: Nat → Bool): (c: Nat) → (s: Nat) → (k: Nat) → s ≤ k → k < s + c → q k = True → q (Nat.firstFrom q c s) = True
  | Zero, s, k, h1, h2, hk => Void.exfalso (Nat.lessIrrefl k (Nat.leTrans (Succ k) s k (Nat.ltCongRight k (s + 0) s ring h2) h1))
  | Succ c, s, k, h1, h2, hk =>
    Bool.inspect (q s) (u => q (Nat.firstFrom q (Succ c) s) = True)
      (t => rewrite <- Nat.firstFromStop q c s t at t)
      (f => rewrite <- Nat.firstFromSkip q c s f at
        Nat.firstFromFound q c (Succ s) k
          (Nat.leNeSucc s k h1 (e => Bool.trueNotFalse (Eq.trans (Eq.sym hk) (Eq.trans (Eq.cong q (Eq.sym e)) f))))
          (Nat.ltSuccAdd s c k h2) hk)

theorem Nat.firstFromLe (q: Nat → Bool) (c: Nat) (s: Nat) (k: Nat) (h1: s ≤ k) (hk: q k = True): Nat.firstFrom q c s ≤ k :=
  match e: Nat.leq (Nat.firstFrom q c s) k with
    | True => rfl
    | False => Void.exfalso (Bool.trueNotFalse (Eq.trans (Eq.sym hk) (Nat.firstFromBefore q c s k h1 (Nat.leqFalse (Nat.firstFrom q c s) k e))))

-- Sums that agree on the elements passing a check `all` says they all pass.
theorem List.sumByCongAll (p: a → Bool) (f: a → Nat) (g: a → Nat) (h: (x: a) → p x = True → f x = g x):
    (xs: List a) → List.all xs p = True → List.sumBy xs f = List.sumBy xs g
  | Nil, ok => rfl
  | Cons x xs, ok =>
    Eq.trans (List.sumByCons xs x f)
      (Eq.trans (Eq.cong (t => t + List.sumBy xs f) (h x (Bool.andLeft (p x) (List.all xs p) ok)))
        (Eq.trans (Eq.cong (t => g x + t) (List.sumByCongAll p f g h xs (Bool.andRight (p x) (List.all xs p) ok)))
          (Eq.sym (List.sumByCons xs x g))))

-- `True` for `Less` and `Equal`.
def Ordering.isLessEq: Ordering → Bool
  | Less => True
  | Equal => True
  | Greater => False

theorem Ordering.isLessEqIf: (d: Bool) → Ordering.isLessEq (if d then Less else Greater) = d
  | True => rfl
  | False => rfl

-- `Nat.compare` agrees with `<=`, so `List.sortBy` with it is total.
theorem Nat.compareLeq (m: Nat) (n: Nat): Ordering.isLessEq (Nat.compare m n) = Nat.leq m n :=
  Bool.inspect (Nat.equal m n)
    (c => Ordering.isLessEq (if c then Equal else (if Nat.leq m n then Less else Greater)) = Nat.leq m n)
    (e => Eq.sym (Nat.leCongRight m m n (Nat.equalSound m n e) (Nat.leRefl m)))
    (e => Ordering.isLessEqIf (Nat.leq m n))

theorem Nat.compareTotal (m: Nat) (n: Nat)
    (h: Ordering.isLessEq (Nat.compare m n) = False): Ordering.isLessEq (Nat.compare n m) = True := Eq.trans (Nat.compareLeq n m) (Nat.leqTotal m n (Eq.trans (Eq.sym (Nat.compareLeq m n)) h))

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

-- The correctness proofs need only that `le` is total: `tot` below.
theorem List.mergeLeHead (le: a → a → Bool) (z: a): (xs: List a) → (ys: List a) →
    List.LeHead le z xs → List.LeHead le z ys → List.LeHead le z (List.merge le xs ys)
  | Nil, ys, hx, hy => hy
  | Cons x xs, Nil, hx, hy => hx
  | Cons x xs, Cons y ys, hx, hy =>
    Bool.inspect (le x y)
      (c => List.LeHead le z (if c then Cons x (List.merge le xs (Cons y ys)) else Cons y (List.merge le (Cons x xs) ys)))
      (e => hx) (e => hy)

theorem List.mergeSorted (le: a → a → Bool) (tot: (x: a) → (y: a) → le x y = False → le y x = True):
    (xs: List a) → (ys: List a) → List.Sorted le xs → List.Sorted le ys → List.Sorted le (List.merge le xs ys)
  | Nil, ys, sx, sy => sy
  | Cons x xs, Nil, sx, sy => sx
  | Cons x xs, Cons y ys, Both hx sxs, Both hy sys =>
    Bool.inspect (le x y)
      (c => List.Sorted le (if c then Cons x (List.merge le xs (Cons y ys)) else Cons y (List.merge le (Cons x xs) ys)))
      (e => Both (List.mergeLeHead le x xs (Cons y ys) hx e) (List.mergeSorted le tot xs (Cons y ys) sxs (Both hy sys)))
      (e => Both (List.mergeLeHead le y (Cons x xs) ys (tot x y e) hy) (List.mergeSorted le tot (Cons x xs) ys (Both hx sxs) sys))

-- Every run in the counter is sorted.
@[noReceiver]
def List.RunsSorted (le: a → a → Bool): List (Option (List a)) → Prop
  | Nil => Unit
  | Cons None rest => List.RunsSorted le rest
  | Cons (Some r) rest => And (List.Sorted le r) (List.RunsSorted le rest)

theorem List.pushRunSorted (le: a → a → Bool) (tot: (x: a) → (y: a) → le x y = False → le y x = True)
    (run: List a): (c: List (Option (List a))) → List.Sorted le run → List.RunsSorted le c → List.RunsSorted le (List.pushRun le run c)
  | Nil, s, h => Both s Trivial
  | Cons None rest, s, h => Both s h
  | Cons (Some r) rest, s, Both sr h =>
    List.pushRunSorted le tot (List.merge le r run) rest (List.mergeSorted le tot r run sr s) h

theorem List.buildRunsSorted (le: a → a → Bool) (tot: (x: a) → (y: a) → le x y = False → le y x = True)
    (c: List (Option (List a))): (xs: List a) → List.RunsSorted le c → List.RunsSorted le (List.buildRuns le c xs)
  | Nil, h => h
  | Cons x xs, h =>
    List.buildRunsSorted le tot (List.pushRun le (Cons x Nil) c) xs (List.pushRunSorted le tot (Cons x Nil) c (Both Trivial Trivial) h)

theorem List.mergeRunsSorted (le: a → a → Bool) (tot: (x: a) → (y: a) → le x y = False → le y x = True)
    (acc: List a): (c: List (Option (List a))) → List.Sorted le acc → List.RunsSorted le c → List.Sorted le (List.mergeRuns le acc c)
  | Nil, s, h => s
  | Cons None rest, s, h => List.mergeRunsSorted le tot acc rest s h
  | Cons (Some r) rest, s, Both sr h =>
    List.mergeRunsSorted le tot (List.merge le r acc) rest (List.mergeSorted le tot r acc sr s) h

theorem List.sortWithSorted (le: a → a → Bool) (tot: (x: a) → (y: a) → le x y = False → le y x = True)
    (xs: List a): List.Sorted le (List.sortWith xs le) :=
  List.mergeRunsSorted le tot Nil (List.buildRuns le Nil xs) Trivial (List.buildRunsSorted le tot Nil xs Trivial)

theorem List.sortBySorted (cmp: a → a → Ordering)
    (tot: (x: a) → (y: a) → Ordering.isLessEq (cmp x y) = False → Ordering.isLessEq (cmp y x) = True)
    (xs: List a): List.Sorted (x y => Ordering.isLessEq (cmp x y)) (List.sortBy xs cmp) := List.sortWithSorted (x y => Ordering.isLessEq (cmp x y)) tot xs

-- If `o` isn't `Less` or `Equal`, its opposite is.
theorem Ordering.flipNotLessEq: (o: Ordering) → Ordering.isLessEq o = False → Ordering.isLessEq (Ordering.flip o) = True
  | Less, h => Void.exfalso (Bool.trueNotFalse h)
  | Equal, h => Void.exfalso (Bool.trueNotFalse h)
  | Greater, h => rfl

-- An `Ord`'s comparison is total, by its `flip` law (§7.6).
theorem Ord.leTotal [auto ord: Ord a] (x: a) (y: a)
    (h: Ordering.isLessEq (Ord.compare x y) = False): Ordering.isLessEq (Ord.compare y x) = True :=
  rewrite ord.flip x y in Ordering.flipNotLessEq (Ord.compare x y) h

theorem List.sortSorted [auto ord: Ord a] (xs: List a):
    List.Sorted (x y => Ordering.isLessEq (Ord.compare x y)) (List.sort xs) :=
  List.sortBySorted Ord.compare Ord.leTotal xs

-- `isLessEq` is "not `Greater`".
theorem Ordering.notGreaterOfIsLessEq (c: Ordering) (h: Ordering.isLessEq c = True): Not (c = Greater) :=
  e => Bool.falseNotTrue (rewrite e at h)

theorem Ordering.isLessEqOfNotGreater: (c: Ordering) → Not (c = Greater) → Ordering.isLessEq c = True
  | Less, n => rfl
  | Equal, n => rfl
  | Greater, n => Void.exfalso (n rfl)

-- The test `List.sort` sorts by is transitive, and holds both ways round
-- only for equal values, by the `Ord`'s laws.
theorem Ord.isLessEqTrans [auto ord: Ord a] (x: a) (y: a) (z: a)
    (h1: Ordering.isLessEq (Ord.compare x y) = True) (h2: Ordering.isLessEq (Ord.compare y z) = True):
    Ordering.isLessEq (Ord.compare x z) = True :=
  Ordering.isLessEqOfNotGreater (Ord.compare x z)
    (Ordering.notGreaterTrans (Ord.compare x y) (Ord.compare y z) (Ord.compare x z) (ord.trans x y z)
      (e => Eq.cong (w => Ord.compare w z) (ord.equal x y e))
      (e => Eq.sym (Eq.cong (w => Ord.compare x w) (ord.equal y z e)))
      (Ordering.notGreaterOfIsLessEq (Ord.compare x y) h1) (Ordering.notGreaterOfIsLessEq (Ord.compare y z) h2))

theorem Ord.isLessEqAntisymm [auto ord: Ord a] (x: a) (y: a)
    (h1: Ordering.isLessEq (Ord.compare x y) = True) (h2: Ordering.isLessEq (Ord.compare y x) = True): x = y :=
  match e: Ord.compare x y with
    | Equal => ord.equal x y e
    | Less => Void.exfalso (Bool.falseNotTrue (rewrite ord.flip x y, e at h2))
    | Greater => Void.exfalso (Bool.falseNotTrue h1)

-- Sorted by one test is sorted by another that agrees with it.
theorem List.leHeadCong (le1: a → a → Bool) (le2: a → a → Bool) (h: (x: a) → (y: a) → le1 x y = le2 x y) (z: a):
    (xs: List a) → List.LeHead le1 z xs → List.LeHead le2 z xs
  | Nil, p => p
  | Cons y ys, p => Eq.trans (Eq.sym (h z y)) p

theorem List.sortedCong (le1: a → a → Bool) (le2: a → a → Bool) (h: (x: a) → (y: a) → le1 x y = le2 x y):
    (xs: List a) → List.Sorted le1 xs → List.Sorted le2 xs
  | Nil, p => p
  | Cons x xs, Both p q => Both (List.leHeadCong le1 le2 h x xs p) (List.sortedCong le1 le2 h xs q)

-- `Sorted le xs` is `xs.chain le = True`, both ways.
theorem List.sortedOfChain (le: a → a → Bool): (xs: List a) → List.chain xs le = True → List.Sorted le xs
  | Nil, chained => Trivial
  | Cons x Nil, chained => Both Trivial Trivial
  | Cons x (Cons next rest), chained => Both (Bool.andLeft _ _ chained) (List.sortedOfChain le (Cons next rest) (Bool.andRight _ _ chained))

theorem List.chainOfSorted (le: a → a → Bool): (xs: List a) → List.Sorted le xs → List.chain xs le = True
  | Nil, sorted => rfl
  | Cons x Nil, sorted => rfl
  | Cons x (Cons next rest), Both first sorted => Bool.andIntro _ _ first (List.chainOfSorted le (Cons next rest) sorted)

-- For numbers, that's `Nat.leq`.
theorem List.sortSortedNat (xs: List Nat): List.Sorted Nat.leq (List.sort xs) :=
  List.sortedCong (x y => Ordering.isLessEq (Nat.compare x y)) Nat.leq Nat.compareLeq (List.sort [ord := Nat.instOrd] xs) (List.sortSorted [ord := Nat.instOrd] xs)

-- The front and the back of a sorted list are sorted (SW-363).
theorem List.sortedPrefix (le: a → a → Bool): (xs: List a) → (ys: List a) → List.Sorted le (List.append xs ys) → List.Sorted le xs
  | Nil, ys, s => Trivial
  | Cons x Nil, ys, s => Both Trivial Trivial
  | Cons x (Cons y zs), ys, Both hx s => Both hx (List.sortedPrefix le (Cons y zs) ys s)

theorem List.sortedSuffix (le: a → a → Bool): (xs: List a) → (ys: List a) → List.Sorted le (List.append xs ys) → List.Sorted le ys
  | Nil, ys, s => s
  | Cons x xs, ys, Both hx s => List.sortedSuffix le xs ys s

-- For a transitive `le`, the first element of a sorted list may come before
-- every later one.
theorem List.sortedHeadLe (le: a → a → Bool) (trans: (x: a) → (y: a) → (z: a) → le x y = True → le y z = True → le x z = True)
    (x: a) (z: a): (rest: List a) → List.Sorted le (Cons x rest) → List.Mem z rest → le x z = True
  | Nil, s, m => Void.exfalso m
  | Cons y ys, Both hxy s, Inl e => rewrite <- e in hxy
  | Cons y ys, Both hxy s, Inr m => trans x y z hxy (List.sortedHeadLe le trans y z ys s m)

-- `rel` holds of each element and every later one.
@[noReceiver]
def List.Pairwise (rel: a → a → Prop): List a → Prop
  | Nil => Unit
  | Cons x xs => And (List.All (y => rel x y) xs) (List.Pairwise rel xs)

-- For a transitive `le`, sorted is pairwise.
theorem List.pairwiseOfSorted (le: a → a → Bool) (trans: (x: a) → (y: a) → (z: a) → le x y = True → le y z = True → le x z = True):
    (xs: List a) → List.Sorted le xs → List.Pairwise (x y => le x y = True) xs
  | Nil, s => Trivial
  | Cons x rest, Both hx s =>
    Both (List.allOfMem (y => le x y = True) rest (z m => List.sortedHeadLe le trans x z rest (Both hx s) m)) (List.pairwiseOfSorted le trans rest s)

-- Sorting a list whose elements all pass `p` needs `le` total only on the
-- values that pass `p`, not on every value: doubles other than the NaN under
-- `Float.ieeeLe`, say (`examples/accept/sort-on-subset.sw`). Merging and
-- the sort's runs keep every element passing, so every comparison the sort
-- makes is between two of them.
theorem List.mergeAll (le: a → a → Bool) (p: a → Prop): (xs: List a) → (ys: List a) →
    List.All p xs → List.All p ys → List.All p (List.merge le xs ys)
  | Nil, ys, ax, ay => ay
  | Cons x xs, Nil, ax, ay => ax
  | Cons x xs, Cons y ys, Both px ax, Both py ay =>
    Bool.inspect (le x y)
      (c => List.All p (if c then Cons x (List.merge le xs (Cons y ys)) else Cons y (List.merge le (Cons x xs) ys)))
      (e => Both px (List.mergeAll le p xs (Cons y ys) ax (Both py ay)))
      (e => Both py (List.mergeAll le p (Cons x xs) ys (Both px ax) ay))

theorem List.mergeSortedOn (le: a → a → Bool) (p: a → Prop) (tot: (x: a) → (y: a) → p x → p y → le x y = False → le y x = True):
    (xs: List a) → (ys: List a) → List.All p xs → List.All p ys → List.Sorted le xs → List.Sorted le ys → List.Sorted le (List.merge le xs ys)
  | Nil, ys, ax, ay, sx, sy => sy
  | Cons x xs, Nil, ax, ay, sx, sy => sx
  | Cons x xs, Cons y ys, Both px ax, Both py ay, Both hx sxs, Both hy sys =>
    Bool.inspect (le x y)
      (c => List.Sorted le (if c then Cons x (List.merge le xs (Cons y ys)) else Cons y (List.merge le (Cons x xs) ys)))
      (e => Both (List.mergeLeHead le x xs (Cons y ys) hx e) (List.mergeSortedOn le p tot xs (Cons y ys) ax (Both py ay) sxs (Both hy sys)))
      (e => Both (List.mergeLeHead le y (Cons x xs) ys (tot x y px py e) hy) (List.mergeSortedOn le p tot (Cons x xs) ys (Both px ax) ay (Both hx sxs) sys))

-- Every run in the counter passes `p`.
@[noReceiver]
def List.RunsAll (p: a → Prop): List (Option (List a)) → Prop
  | Nil => Unit
  | Cons None rest => List.RunsAll p rest
  | Cons (Some r) rest => And (List.All p r) (List.RunsAll p rest)

theorem List.pushRunAll (le: a → a → Bool) (p: a → Prop) (run: List a): (c: List (Option (List a))) →
    List.All p run → List.RunsAll p c → List.RunsAll p (List.pushRun le run c)
  | Nil, a, h => Both a Trivial
  | Cons None rest, a, h => Both a h
  | Cons (Some r) rest, a, Both ar h => List.pushRunAll le p (List.merge le r run) rest (List.mergeAll le p r run ar a) h

theorem List.buildRunsAll (le: a → a → Bool) (p: a → Prop) (c: List (Option (List a))): (xs: List a) →
    List.All p xs → List.RunsAll p c → List.RunsAll p (List.buildRuns le c xs)
  | Nil, a, h => h
  | Cons x xs, Both px a, h =>
    List.buildRunsAll le p (List.pushRun le (Cons x Nil) c) xs a (List.pushRunAll le p (Cons x Nil) c (Both px Trivial) h)

theorem List.mergeRunsAll (le: a → a → Bool) (p: a → Prop) (acc: List a): (c: List (Option (List a))) →
    List.All p acc → List.RunsAll p c → List.All p (List.mergeRuns le acc c)
  | Nil, a, h => a
  | Cons None rest, a, h => List.mergeRunsAll le p acc rest a h
  | Cons (Some r) rest, a, Both ar h => List.mergeRunsAll le p (List.merge le r acc) rest (List.mergeAll le p r acc ar a) h

-- What every element passes, every element of the sorted list passes.
theorem List.allSortWith (le: a → a → Bool) (p: a → Prop) (xs: List a) (a: List.All p xs): List.All p (List.sortWith xs le) :=
  List.mergeRunsAll le p Nil (List.buildRuns le Nil xs) Trivial (List.buildRunsAll le p Nil xs a Trivial)

theorem List.pushRunSortedOn (le: a → a → Bool) (p: a → Prop) (tot: (x: a) → (y: a) → p x → p y → le x y = False → le y x = True)
    (run: List a): (c: List (Option (List a))) → List.All p run → List.RunsAll p c → List.Sorted le run → List.RunsSorted le c →
    List.RunsSorted le (List.pushRun le run c)
  | Nil, a, ha, s, h => Both s Trivial
  | Cons None rest, a, ha, s, h => Both s h
  | Cons (Some r) rest, a, Both ar ha, s, Both sr h =>
    List.pushRunSortedOn le p tot (List.merge le r run) rest (List.mergeAll le p r run ar a) ha (List.mergeSortedOn le p tot r run ar a sr s) h

theorem List.buildRunsSortedOn (le: a → a → Bool) (p: a → Prop) (tot: (x: a) → (y: a) → p x → p y → le x y = False → le y x = True)
    (c: List (Option (List a))): (xs: List a) → List.All p xs → List.RunsAll p c → List.RunsSorted le c → List.RunsSorted le (List.buildRuns le c xs)
  | Nil, a, ha, h => h
  | Cons x xs, Both px a, ha, h =>
    List.buildRunsSortedOn le p tot (List.pushRun le (Cons x Nil) c) xs a
      (List.pushRunAll le p (Cons x Nil) c (Both px Trivial) ha)
      (List.pushRunSortedOn le p tot (Cons x Nil) c (Both px Trivial) ha (Both Trivial Trivial) h)

theorem List.mergeRunsSortedOn (le: a → a → Bool) (p: a → Prop) (tot: (x: a) → (y: a) → p x → p y → le x y = False → le y x = True)
    (acc: List a): (c: List (Option (List a))) → List.All p acc → List.RunsAll p c → List.Sorted le acc → List.RunsSorted le c →
    List.Sorted le (List.mergeRuns le acc c)
  | Nil, a, ha, s, h => s
  | Cons None rest, a, ha, s, h => List.mergeRunsSortedOn le p tot acc rest a ha s h
  | Cons (Some r) rest, a, Both ar ha, s, Both sr h =>
    List.mergeRunsSortedOn le p tot (List.merge le r acc) rest (List.mergeAll le p r acc ar a) ha (List.mergeSortedOn le p tot r acc ar a sr s) h

-- `List.sortWithSorted` for a `le` total only on the values passing `p`.
theorem List.sortWithSortedOn (le: a → a → Bool) (p: a → Prop) (tot: (x: a) → (y: a) → p x → p y → le x y = False → le y x = True)
    (xs: List a) (a: List.All p xs): List.Sorted le (List.sortWith xs le) :=
  List.mergeRunsSortedOn le p tot Nil (List.buildRuns le Nil xs) Trivial (List.buildRunsAll le p Nil xs a Trivial) Trivial
    (List.buildRunsSortedOn le p tot Nil xs a Trivial Trivial)

-- `List.sortedHeadLe` and `List.pairwiseOfSorted` for a `le` transitive only
-- on the values passing `p`.
theorem List.sortedHeadLeOn (le: a → a → Bool) (p: a → Prop)
    (trans: (x: a) → (y: a) → (z: a) → p x → p y → p z → le x y = True → le y z = True → le x z = True)
    (x: a) (z: a) (px: p x): (rest: List a) → List.All p rest → List.Sorted le (Cons x rest) → List.Mem z rest → le x z = True
  | Nil, a, s, m => Void.exfalso m
  | Cons y ys, Both py a, Both hxy s, Inl e => rewrite <- e in hxy
  | Cons y ys, Both py a, Both hxy s, Inr m =>
    trans x y z px py (List.allMem p z ys a m) hxy (List.sortedHeadLeOn le p trans y z py ys a s m)

theorem List.pairwiseOfSortedOn (le: a → a → Bool) (p: a → Prop)
    (trans: (x: a) → (y: a) → (z: a) → p x → p y → p z → le x y = True → le y z = True → le x z = True):
    (xs: List a) → List.All p xs → List.Sorted le xs → List.Pairwise (x y => le x y = True) xs
  | Nil, a, s => Trivial
  | Cons x rest, Both px a, Both hx s =>
    Both (List.allOfMem (y => le x y = True) rest (z m => List.sortedHeadLeOn le p trans x z px rest a (Both hx s) m))
      (List.pairwiseOfSortedOn le p trans rest a s)

-- `Nat.leq` restricted to even numbers is still total there.
theorem List.sortWithSortedOnExample: List.Sorted Nat.leq (List.sortWith [4, 2, 6] Nat.leq) :=
  List.sortWithSortedOn Nat.leq (n => n % 2 = 0) (x y px py h => Nat.leqTotal x y h) [4, 2, 6] (Both rfl (Both rfl (Both rfl Trivial)))

theorem List.pairwiseAppendLeft (rel: a → a → Prop): (xs: List a) → (ys: List a) → List.Pairwise rel (List.append xs ys) → List.Pairwise rel xs
  | Nil, ys, h => Trivial
  | Cons x xs, ys, Both a h => Both (List.allAppendLeft (y => rel x y) xs ys a) (List.pairwiseAppendLeft rel xs ys h)

-- Each element of the front is related to each of the back.
theorem List.pairwiseAppendAcross (rel: a → a → Prop): (xs: List a) → (ys: List a) → List.Pairwise rel (List.append xs ys) →
    (x: a) → List.Mem x xs → (y: a) → List.Mem y ys → rel x y
  | Nil, ys, h, x, mx, y, my => Void.exfalso mx
  | Cons z zs, ys, Both a h, x, Inl e, y, my => rewrite <- e in List.allMem (w => rel z w) y ys (List.allAppendRight (w => rel z w) zs ys a) my
  | Cons z zs, ys, Both a h, x, Inr mx, y, my => List.pairwiseAppendAcross rel zs ys h x mx y my

-- Merging, when everything in the first list may come before everything in
-- the second, joins the lists.
theorem List.mergeAppend (le: a → a → Bool): (xs: List a) → (ys: List a) → ((x: a) → List.Mem x xs → (y: a) → List.Mem y ys → le x y = True) →
    List.merge le xs ys = List.append xs ys
  | Nil, ys, h => rfl
  | Cons x xs, Nil, h => Eq.sym (List.appendNil (Cons x xs))
  | Cons x xs, Cons y ys, h => rewrite h x (Inl rfl) y (Inl rfl), List.mergeAppend le xs (Cons y ys) (z m => h z (Inr m)) in rfl

-- The runs of `List.sortWith`'s counter, oldest first, joined.
def List.runsJoined: List (Option (List a)) → List a
  | Nil => Nil
  | Cons None rest => List.runsJoined rest
  | Cons (Some run) rest => List.append (List.runsJoined rest) run

-- When the runs joined are in order, merging two neighbours joins them.
theorem List.pairwiseRunsMerge (le: a → a → Bool) (front: List a) (older: List a) (newer: List a)
    (h: List.Pairwise (x y => le x y = True) (List.append (List.append front older) newer)):
    List.merge le older newer = List.append older newer :=
  List.mergeAppend le older newer
    (x mx y my => List.pairwiseAppendAcross (x y => le x y = True) (List.append front older) newer h x
      (List.anyAppendRight (w => w = x) front older mx) y my)

theorem List.pushRunJoined (le: a → a → Bool): (run: List a) → (c: List (Option (List a))) →
    List.Pairwise (x y => le x y = True) (List.append (List.runsJoined c) run) →
    List.runsJoined (List.pushRun le run c) = List.append (List.runsJoined c) run
  | run, Nil, h => rfl
  | run, Cons None rest, h => rfl
  | run, Cons (Some older) rest, h =>
    Eq.trans (Eq.cong (r => List.runsJoined (List.pushRun le r rest)) (List.pairwiseRunsMerge le (List.runsJoined rest) older run h))
      (Eq.trans
        (List.pushRunJoined le (List.append older run) rest (rewrite List.appendAssoc (List.runsJoined rest) older run at h))
        (Eq.sym (List.appendAssoc (List.runsJoined rest) older run)))

theorem List.buildRunsJoined (le: a → a → Bool): (c: List (Option (List a))) → (xs: List a) →
    List.Pairwise (x y => le x y = True) (List.append (List.runsJoined c) xs) →
    List.runsJoined (List.buildRuns le c xs) = List.append (List.runsJoined c) xs
  | c, Nil, h => Eq.sym (List.appendNil (List.runsJoined c))
  | c, Cons x xs, h =>
    Eq.trans
      (List.buildRunsJoined le (List.pushRun le (Cons x Nil) c) xs
        (rewrite <- List.pushRunJoined le (Cons x Nil) c
            (List.pairwiseAppendLeft (x y => le x y = True) (List.append (List.runsJoined c) (Cons x Nil)) xs
              (rewrite <- List.appendAssoc (List.runsJoined c) (Cons x Nil) xs at h))
          at (rewrite <- List.appendAssoc (List.runsJoined c) (Cons x Nil) xs at h)))
      (Eq.trans
        (Eq.cong (r => List.append r xs)
          (List.pushRunJoined le (Cons x Nil) c
            (List.pairwiseAppendLeft (x y => le x y = True) (List.append (List.runsJoined c) (Cons x Nil)) xs
              (rewrite <- List.appendAssoc (List.runsJoined c) (Cons x Nil) xs at h))))
        (List.appendAssoc (List.runsJoined c) (Cons x Nil) xs))

theorem List.mergeRunsJoined (le: a → a → Bool): (acc: List a) → (c: List (Option (List a))) →
    List.Pairwise (x y => le x y = True) (List.append (List.runsJoined c) acc) →
    List.mergeRuns le acc c = List.append (List.runsJoined c) acc
  | acc, Nil, h => rfl
  | acc, Cons None rest, h => List.mergeRunsJoined le acc rest h
  | acc, Cons (Some older) rest, h =>
    Eq.trans (Eq.cong (r => List.mergeRuns le r rest) (List.pairwiseRunsMerge le (List.runsJoined rest) older acc h))
      (Eq.trans
        (List.mergeRunsJoined le (List.append older acc) rest (rewrite List.appendAssoc (List.runsJoined rest) older acc at h))
        (Eq.sym (List.appendAssoc (List.runsJoined rest) older acc)))

-- Sorting a list that is already sorted gives it back, for a transitive `le`
-- (D725). No totality is needed: every merge takes the older run whole.
theorem List.sortWithOfSorted (le: a → a → Bool) (trans: (x: a) → (y: a) → (z: a) → le x y = True → le y z = True → le x z = True)
    (xs: List a) (s: List.Sorted le xs): List.sortWith xs le = xs :=
  Eq.trans
    (List.mergeRunsJoined le Nil (List.buildRuns le Nil xs)
      (rewrite <- List.appendNil xs, <- List.buildRunsJoined le Nil xs (List.pairwiseOfSorted le trans xs s) at List.pairwiseOfSorted le trans xs s))
    (Eq.trans (List.appendNil (List.runsJoined (List.buildRuns le Nil xs))) (List.buildRunsJoined le Nil xs (List.pairwiseOfSorted le trans xs s)))

theorem List.sortWithOfSortedExample (xs: List Nat) (s: List.Sorted Nat.leq xs): List.sortWith xs Nat.leq = xs :=
  List.sortWithOfSorted Nat.leq Nat.leTrans xs s

-- Finding by key, and keys that stay distinct when the list is rearranged
-- (SW-363). Here rather than with `List.find` and `List.Distinct` in the
-- toolkit because they decide equality with `DecEq`.

-- Finding by key: what is found has the key, and when some element has the
-- key, something is found.
theorem List.findKey [auto eq: DecEq k] (xs: List a) (key: a → k) (kk: k) (y: a) (h: List.find xs (x => key x == kk) = Some y): key y = kk :=
  match List.findSome xs (x => key x == kk) y h with
    | Both py m => Decidable.toBoolSound (DecEq.decide (key y) kk) py

theorem List.findKeySome [auto eq: DecEq k] (xs: List a) (key: a → k) (kk: k) (m: List.Mem kk (List.map xs key)):
    Not (List.find xs (x => key x == kk) = None) :=
  h => List.anyElim (x => key x = kk) Void xs (List.memMapAny xs key kk m)
    (x inXs e => List.findNoneNotMem xs (z => key z == kk) x (Decidable.toBoolOf (DecEq.decide (key x) kk) e) inXs h)

-- Permutations have the same elements.
theorem List.memPerm [auto eq: DecEq a] (xs: List a) (ys: List a) (h: List.Perm xs ys) (x: a) (m: List.Mem x xs): List.Mem x ys :=
  List.anyTrueElim ys (y => y == x) (List.Mem x ys)
    (Eq.trans (Eq.sym (List.anyPerm xs ys h (y => y == x))) (List.anyOfMem xs (y => y == x) x (Decidable.toBoolOf (DecEq.decide x x) rfl) m))
    (y inYs e => rewrite <- Decidable.toBoolSound (DecEq.decide y x) e in inYs)

-- Counting with a test the first element passes.
theorem List.occurrencesConsTrue (xs: List a) (p: a → Bool) (x: a) (px: p x = True): List.occurrences (Cons x xs) p = Succ (List.occurrences xs p) :=
  rewrite px in rfl

theorem Bool.toNatAddLeOne: (b: Bool) → (n: Nat) → Bool.toNat b + n ≤ 1 → n ≤ 1
  | False, n, h => h
  | True, Zero, h => rfl
  | True, Succ n, h => Void.exfalso (Bool.falseNotTrue h)

-- Distinct keys: at most one element has any key.
theorem List.occurrencesKeyDistinct [auto eq: DecEq k]: (xs: List a) → (key: a → k) → (kk: k) → List.Distinct (List.map xs key) →
    List.occurrences xs (x => key x == kk) ≤ 1
  | Nil, key, kk, d => rfl
  | Cons x xs, key, kk, Both notMem d =>
    Bool.inspect (key x == kk) (c => Bool.toNat c + List.occurrences xs (y => key y == kk) ≤ 1)
      (t =>
        match n: List.occurrences xs (y => key y == kk) with
          | Zero => rfl
          | Succ m =>
            Void.exfalso (List.anyTrueElim xs (y => key y == kk) Void (rewrite List.anyOccurrences xs (y => key y == kk), n in rfl)
              (y inXs py =>
                notMem (rewrite Eq.trans (Decidable.toBoolSound (DecEq.decide (key x) kk) t) (Eq.sym (Decidable.toBoolSound (DecEq.decide (key y) kk) py))
                  in List.memMap xs y inXs key))))
      (f => List.occurrencesKeyDistinct xs key kk d)

-- And back: when at most one element has any key, the keys are distinct.
theorem List.distinctOfOccurrences [auto eq: DecEq k]: (xs: List a) → (key: a → k) → ((kk: k) → List.occurrences xs (x => key x == kk) ≤ 1) →
    List.Distinct (List.map xs key)
  | Nil, key, h => Trivial
  | Cons x xs, key, h =>
    Both
      (m =>
        List.anyElim (y => key y = key x) Void xs (List.memMapAny xs key (key x) m) (y inXs e =>
          match n: List.occurrences xs (z => key z == key x) with
            | Zero =>
              Bool.falseNotTrue (Eq.trans (Eq.sym (rewrite n at List.anyOccurrences xs (z => key z == key x)))
                (List.anyOfMem xs (z => key z == key x) y (Decidable.toBoolOf (DecEq.decide (key y) (key x)) e) inXs))
            | Succ c =>
              Bool.falseNotTrue (rewrite n at Eq.trans (Eq.sym (Eq.cong (t => Nat.leq t 1)
                (List.occurrencesConsTrue xs (z => key z == key x) x (Decidable.toBoolOf (DecEq.decide (key x) (key x)) rfl)))) (h (key x)))))
      (List.distinctOfOccurrences xs key (kk => Bool.toNatAddLeOne (key x == kk) (List.occurrences xs (z => key z == kk)) (h kk)))

-- Rearranging a list keeps its keys distinct.
theorem List.distinctMapPerm [auto eq: DecEq k] (xs: List a) (key: a → k) (ys: List a) (h: List.Perm xs ys) (d: List.Distinct (List.map ys key)):
    List.Distinct (List.map xs key) :=
  List.distinctOfOccurrences xs key (kk => Eq.trans (Eq.cong (n => Nat.leq n 1) (h (x => key x == kk))) (List.occurrencesKeyDistinct ys key kk d))

-- Counting `p`, apart from `v` and at `v`.
theorem List.occurrencesSplit [auto eq: DecEq a]: (xs: List a) → (v: a) → (p: a → Bool) →
    List.occurrences xs p = List.occurrences xs (x => p x ∧ ¬(x == v)) + List.occurrences xs (x => p x ∧ (x == v))
  | Nil, v, p => rfl
  | Cons x xs, v, p =>
    let one: Bool.toNat (p x) = Bool.toNat (p x ∧ ¬(x == v)) + Bool.toNat (p x ∧ (x == v)) :=
      match p x, x == v with
        | True, True => rfl
        | True, False => rfl
        | False, True => rfl
        | False, False => rfl
    Eq.trans (Eq.cong (t => t + List.occurrences xs p) one)
      (Eq.trans (Eq.cong (t => (Bool.toNat (p x ∧ ¬(x == v)) + Bool.toNat (p x ∧ (x == v))) + t) (List.occurrencesSplit xs v p))
        (Nat.addSwap (Bool.toNat (p x ∧ ¬(x == v))) (Bool.toNat (p x ∧ (x == v)))
          (List.occurrences xs (y => p y ∧ ¬(y == v))) (List.occurrences xs (y => p y ∧ (y == v)))))

-- Counting at `x` in a list without `x` finds nothing ...
theorem List.occurrencesAbsent [auto eq: DecEq a]: (xs: List a) → (x: a) → (p: a → Bool) → Not (List.Mem x xs) →
    List.occurrences xs (y => p y ∧ (y == x)) = 0
  | Nil, x, p, n => rfl
  | Cons y ys, x, p, n =>
    match e: y == x with
      | True => Void.exfalso (n (Inl (DecEq.sound y x e)))
      | False => rewrite Bool.andFalse (p y), List.occurrencesAbsent ys x p (m => n (Inr m)) in rfl

-- ... and in a list with `x` once, finds `x` if it passes `p`.
theorem List.occurrencesOnce [auto eq: DecEq a]: (xs: List a) → (x: a) → (p: a → Bool) → List.Distinct xs → List.Mem x xs →
    List.occurrences xs (y => p y ∧ (y == x)) = Bool.toNat (p x)
  | Nil, x, p, d, m => Void.exfalso m
  | Cons y ys, x, p, Both notMem d, Inl e =>
    rewrite e, DecEq.refl x, Bool.andTrue (p x), List.occurrencesAbsent ys x p (rewrite e at notMem) in Nat.addZero (Bool.toNat (p x))
  | Cons y ys, x, p, Both notMem d, Inr m =>
    match e: y == x with
      | True => Void.exfalso (notMem (rewrite DecEq.sound y x e in m))
      | False => rewrite Bool.andFalse (p y), List.occurrencesOnce ys x p d m in rfl

-- Two lists without repeats and with the same members are the same elements
-- in another order.
theorem List.permOfSameMembers [auto eq: DecEq a]: (xs: List a) → (ys: List a) → List.Distinct xs → List.Distinct ys →
    ((x: a) → List.Mem x xs → List.Mem x ys) → ((y: a) → List.Mem y ys → List.Mem y xs) → List.Perm xs ys
  | Nil, Nil, dx, dy, there, back, p => rfl
  | Nil, Cons y ys, dx, dy, there, back, p => Void.exfalso (back y (Inl rfl))
  | Cons x xs, ys, Both notMem dx, dy, there, back, p =>
    let others := List.filter ys (z => ¬(z == x))
    let rest: List.occurrences xs p = List.occurrences others p :=
      List.permOfSameMembers xs others dx (List.distinctFilter ys (z => ¬(z == x)) dy)
        (z m =>
          List.memFilterIntro ys (z => ¬(z == x)) z (there z (Inr m))
            (match e: z == x with
              | True => Void.exfalso (notMem (rewrite <- DecEq.sound z x e in m))
              | False => rfl))
        (z m =>
          match List.memFilter ys (z => ¬(z == x)) z m with
            | Both inYs notX =>
              match back z inYs with
                | Inl e => Void.exfalso (Bool.falseNotTrue (rewrite e, DecEq.refl z at notX))
                | Inr inXs => inXs)
        p
    rewrite List.occurrencesSplit ys x p, List.occurrencesOnce ys x p dy (there x (Inl rfl)), <- List.occurrencesFilter ys (z => ¬(z == x)) p, <- rest
      in Nat.addComm (Bool.toNat (p x)) (List.occurrences xs p)

-- Two lists sorted by the same order, with the same elements, are equal,
-- when the order puts no two different elements both ways round.
theorem List.sortedPermEq [auto eq: DecEq a] (le: a → a → Bool) (trans: (x: a) → (y: a) → (z: a) → le x y = True → le y z = True → le x z = True)
    (antisymm: (x: a) → (y: a) → le x y = True → le y x = True → x = y):
    (xs: List a) → (ys: List a) → List.Sorted le xs → List.Sorted le ys → List.Perm xs ys → xs = ys
  | Nil, Nil, sx, sy, p => rfl
  | Nil, Cons y ys, sx, sy, p => Void.exfalso (Nat.zeroNotSucc (List.length ys) (List.permLength Nil (Cons y ys) p))
  | Cons x xs, Nil, sx, sy, p => Void.exfalso (Nat.succNotZero (List.length xs) (List.permLength (Cons x xs) Nil p))
  | Cons x xs, Cons y ys, Both hx sx, Both hy sy, p =>
    let same: x = y :=
      match List.memPerm (Cons y ys) (Cons x xs) (List.permSym (Cons x xs) (Cons y ys) p) y (Inl rfl) with
        | Inl e => e
        | Inr my =>
          match List.memPerm (Cons x xs) (Cons y ys) p x (Inl rfl) with
            | Inl e => Eq.sym e
            | Inr mx => antisymm x y (List.sortedHeadLe le trans x y xs (Both hx sx) my) (List.sortedHeadLe le trans y x ys (Both hy sy) mx)
    let rest: xs = ys :=
      List.sortedPermEq le trans antisymm xs ys sx sy
        (q => Nat.addCancelLeft (Bool.toNat (q x)) (List.occurrences xs q) (List.occurrences ys q)
          (Eq.trans (p q) (Eq.cong (t => Bool.toNat (q t) + List.occurrences ys q) (Eq.sym same))))
    rewrite same, rest in rfl

-- A list sorted by an `Ord` is the sort of any list with the same elements.
theorem List.sortOfSorted [auto ord: Ord a] (xs: List a) (ys: List a)
    (sorted: List.Sorted (x y => Ordering.isLessEq (Ord.compare x y)) ys) (same: List.Perm ys xs): ys = xs.sort :=
  List.sortedPermEq (x y => Ordering.isLessEq (Ord.compare x y)) Ord.isLessEqTrans Ord.isLessEqAntisymm ys xs.sort sorted (List.sortSorted xs)
    (List.permTrans ys xs xs.sort same (List.permSym xs.sort xs (List.sortPerm xs)))

-- Lists with the same elements sort to the same list.
theorem List.sortEqOfPerm [auto ord: Ord a] (xs: List a) (ys: List a) (same: List.Perm xs ys): xs.sort = ys.sort :=
  List.sortOfSorted ys xs.sort (List.sortSorted xs) (List.permTrans xs.sort xs ys (List.sortPerm xs) same)

test "List.sort by Ord.reverse" := List.sort [ord := Ord.reverse] [1, 3, 2, 3] == [3, 3, 2, 1]

-- For numbers, sorted by `Nat.leq`.
theorem List.sortOfSortedNat (xs: List Nat) (ys: List Nat) (sorted: List.Sorted Nat.leq ys) (same: List.Perm ys xs): ys = xs.sort :=
  List.sortOfSorted xs ys (List.sortedCong Nat.leq (x y => Ordering.isLessEq (Nat.compare x y)) (x y => Eq.sym (Nat.compareLeq x y)) ys sorted) same

-- The list without its first `x`, or the list itself if `x` isn't in it
-- (Haskell's `Data.List.delete`).
def List.removeFirst [auto eq: DecEq a]: List a → a → List a
  | Nil, x => Nil
  | Cons y ys, x => if y == x then ys else Cons y (ys.removeFirst x)

test "List.removeFirst" := [1, 2, 1].removeFirst 1 == [2, 1] ∧ [1, 2].removeFirst 3 == [1, 2] ∧ [3, 1, 2].removeFirst 2 == [3, 1]

-- Without `x` in the list, nothing is taken out.
theorem List.removeFirstAbsent [auto eq: DecEq a]: (xs: List a) → (x: a) → Not (List.Mem x xs) → xs.removeFirst x = xs
  | Nil, x, n => rfl
  | Cons y ys, x, n =>
    match e: y == x with
      | True => Void.exfalso (n (Inl (DecEq.sound y x e)))
      | False => rewrite List.removeFirstAbsent ys x (m => n (Inr m)) in rfl

-- With `x` in the list, `x` and the rest are the list in another order.
theorem List.occurrencesRemoveFirst [auto eq: DecEq a]: (ys: List a) → (x: a) → List.Mem x ys → (p: a → Bool) →
    List.occurrences ys p = Bool.toNat (p x) + List.occurrences (ys.removeFirst x) p
  | Nil, x, m, p => Void.exfalso m
  | Cons y ys, x, m, p =>
    match e: y == x with
      | True => rewrite DecEq.sound y x e in rfl
      | False =>
        let later: List.Mem x ys :=
          match m with
            | Inl same => Void.exfalso (DecEq.soundFalse y x e same)
            | Inr rest => rest
        rewrite List.occurrencesRemoveFirst ys x later p in Nat.addLeftComm (Bool.toNat (p y)) (Bool.toNat (p x)) _

theorem List.permRemoveFirst [auto eq: DecEq a] (ys: List a) (x: a) (m: List.Mem x ys): List.Perm (Cons x (ys.removeFirst x)) ys :=
  p => Eq.sym (List.occurrencesRemoveFirst ys x m p)

theorem List.lengthRemoveFirst [auto eq: DecEq a] (ys: List a) (x: a) (m: List.Mem x ys): List.length ys = Succ (List.length (ys.removeFirst x)) :=
  Eq.sym (List.permLength (Cons x (ys.removeFirst x)) ys (List.permRemoveFirst ys x m))

-- Taking the same element off the front of one list and out of the other
-- leaves a permutation.
theorem List.permRemoveFirstOfCons [auto eq: DecEq a] (x: a) (xs: List a) (ys: List a) (same: List.Perm (Cons x xs) ys):
    List.Perm xs (ys.removeFirst x) :=
  p =>
    Nat.addCancelLeft (Bool.toNat (p x)) (List.occurrences xs p) (List.occurrences (ys.removeFirst x) p)
      (Eq.trans (same p) (List.occurrencesRemoveFirst ys x (List.memPerm (Cons x xs) ys same x (Inl rfl)) p))

theorem List.sumByRemoveFirst [auto eq: DecEq a] [auto add: Add b]: (ys: List a) → (x: a) → List.Mem x ys → (f: a → b) →
    List.sumBy ys f = f x + List.sumBy (ys.removeFirst x) f
  | Nil, x, m, f => Void.exfalso m
  | Cons y ys, x, m, f =>
    match e: y == x with
      | True => rewrite List.sumByCons ys y f, DecEq.sound y x e in rfl
      | False =>
        let later: List.Mem x ys :=
          match m with
            | Inl same => Void.exfalso (DecEq.soundFalse y x e same)
            | Inr rest => rest
        rewrite List.sumByCons ys y f, List.sumByCons (ys.removeFirst x) y f, List.sumByRemoveFirst ys x later f in Add.addLeftComm (f y) (f x) _

-- Sums and counts are the same in any order.
theorem List.sumByPerm [auto eq: DecEq a] [auto add: Add b]: (xs: List a) → (ys: List a) → List.Perm xs ys → (f: a → b) →
    List.sumBy xs f = List.sumBy ys f
  | Nil, Nil, same, f => rfl
  | Nil, Cons y ys, same, f => Void.exfalso (Nat.zeroNotSucc (List.length ys) (List.permLength Nil (Cons y ys) same))
  | Cons x xs, ys, same, f =>
    let found: List.Mem x ys := List.memPerm (Cons x xs) ys same x (Inl rfl)
    rewrite List.sumByCons xs x f, List.sumByPerm xs (ys.removeFirst x) (List.permRemoveFirstOfCons x xs ys same) f, List.sumByRemoveFirst ys x found f
      in rfl

theorem List.sumPerm [auto eq: DecEq a] [auto add: Add a] (xs: List a) (ys: List a) (same: List.Perm xs ys): List.sum xs = List.sum ys :=
  List.sumByPerm xs ys same (x => x)

theorem List.countPerm (xs: List a) (ys: List a) (same: List.Perm xs ys) (p: a → Bool): List.count xs p = List.count ys p :=
  rewrite List.countOccurrences xs p, List.countOccurrences ys p in same p

theorem List.findKeyExample: List.find [MkPair "a" 1, MkPair "b" 2, MkPair "b" 3] (x => Pair.fst x == "b") = Some (MkPair "b" 2) := rfl

-- Adding an element in front keeps every subsequence.
theorem List.subsequenceCons (x: a): (s: List a) → (ys: List a) → List.Subsequence s ys → List.Subsequence s (Cons x ys)
  | Nil, ys, h => Trivial
  | Cons y s, ys, h => Inr h

theorem List.subsequenceRefl: (xs: List a) → List.Subsequence xs xs
  | Nil => Trivial
  | Cons x xs => Inl (Both rfl (List.subsequenceRefl xs))

theorem List.subsequenceLength: (s: List a) → (ys: List a) → List.Subsequence s ys → List.length s ≤ List.length ys
  | Nil, ys, h => rfl
  | Cons x xs, Nil, h => Void.exfalso h
  | Cons x xs, Cons y ys, Inl (Both e h) => List.subsequenceLength xs ys h
  | Cons x xs, Cons y ys, Inr h =>
    Nat.leTrans (List.length (Cons x xs)) (List.length ys) (Succ (List.length ys)) (List.subsequenceLength (Cons x xs) ys h) (Nat.leSucc (List.length ys))

-- Dropping the first element keeps a subsequence.
theorem List.subsequenceTail (x: a): (s: List a) → (ys: List a) → List.Subsequence (Cons x s) ys → List.Subsequence s ys
  | s, Nil, h => Void.exfalso h
  | s, Cons y ys, Inl (Both e h) => List.subsequenceCons y s ys h
  | s, Cons y ys, Inr h => List.subsequenceCons y s ys (List.subsequenceTail x s ys h)

-- A subsequence of a subsequence is a subsequence.
theorem List.subsequenceTrans: (xs: List a) → (ys: List a) → (zs: List a) →
    List.Subsequence xs ys → List.Subsequence ys zs → List.Subsequence xs zs
  | Nil, ys, zs, h1, h2 => Trivial
  | Cons x xs, Nil, zs, h1, h2 => Void.exfalso h1
  | Cons x xs, Cons y ys, Nil, h1, h2 => Void.exfalso h2
  | Cons x xs, Cons y ys, Cons z zs, h1, Inr h2 => Inr (List.subsequenceTrans (Cons x xs) (Cons y ys) zs h1 h2)
  | Cons x xs, Cons y ys, Cons z zs, Inl (Both e1 h1), Inl (Both e2 h2) =>
    Inl (Both (Eq.trans e1 e2) (List.subsequenceTrans xs ys zs h1 h2))
  | Cons x xs, Cons y ys, Cons z zs, Inr h1, Inl (Both e2 h2) => Inr (List.subsequenceTrans (Cons x xs) ys zs h1 h2)

theorem List.mergeCount: (xs: List a) → (ys: List a) → (le: a → a → Bool) → (p: a → Bool) →
    List.occurrences (List.merge le xs ys) p = List.occurrences xs p + List.occurrences ys p
  | Nil, ys, le, p => rfl
  | Cons x xs, Nil, le, p => ring
  | Cons x xs, Cons y ys, le, p =>
    Bool.inspect (le x y)
      (c => List.occurrences (if c then Cons x (List.merge le xs (Cons y ys)) else Cons y (List.merge le (Cons x xs) ys)) p
        = List.occurrences (Cons x xs) p + List.occurrences (Cons y ys) p)
      (e => ring [List.mergeCount xs (Cons y ys) le p])
      (e => ring [List.mergeCount (Cons x xs) ys le p])

-- How many elements of all the runs satisfy `p`.
@[noReceiver]
def List.runsCount (p: a → Bool): List (Option (List a)) → Nat
  | Nil => 0
  | Cons None rest => List.runsCount p rest
  | Cons (Some r) rest => List.occurrences r p + List.runsCount p rest

theorem List.pushRunCount (run: List a): (c: List (Option (List a))) → (le: a → a → Bool) → (p: a → Bool) →
    List.runsCount p (List.pushRun le run c) = List.occurrences run p + List.runsCount p c
  | Nil, le, p => rfl
  | Cons None rest, le, p => rfl
  | Cons (Some r) rest, le, p => ring [List.pushRunCount (List.merge le r run) rest le p, List.mergeCount r run le p]

theorem List.buildRunsCount (c: List (Option (List a))): (xs: List a) → (le: a → a → Bool) → (p: a → Bool) →
    List.runsCount p (List.buildRuns le c xs) = List.runsCount p c + List.occurrences xs p
  | Nil, le, p => ring
  | Cons x xs, le, p => ring [List.buildRunsCount (List.pushRun le (Cons x Nil) c) xs le p, List.pushRunCount (Cons x Nil) c le p]

theorem List.mergeRunsCount (acc: List a): (c: List (Option (List a))) → (le: a → a → Bool) → (p: a → Bool) →
    List.occurrences (List.mergeRuns le acc c) p = List.occurrences acc p + List.runsCount p c
  | Nil, le, p => ring
  | Cons None rest, le, p => List.mergeRunsCount acc rest le p
  | Cons (Some r) rest, le, p => ring [List.mergeRunsCount (List.merge le r acc) rest le p, List.mergeCount r acc le p]

theorem List.sortWithPerm (xs: List a) (le: a → a → Bool): List.Perm (List.sortWith xs le) xs := p =>
  Eq.trans (List.mergeRunsCount Nil (List.buildRuns le Nil xs) le p) (List.buildRunsCount Nil xs le p)

theorem List.sortByPerm (xs: List a) (cmp: a → a → Ordering): List.Perm (List.sortBy xs cmp) xs := List.sortWithPerm xs (x y => Ordering.isLessEq (cmp x y))

theorem List.sortPerm [auto ord: Ord a] (xs: List a): List.Perm (List.sort xs) xs := List.sortByPerm xs Ord.compare

theorem List.sortLength [auto ord: Ord a] (xs: List a): List.length (List.sort xs) = List.length xs := List.permLength (List.sort xs) xs (List.sortPerm xs)

-- Splitting a run of positions at the separators.

theorem Bool.andFalse: (b: Bool) → (b ∧ False) = False
  | True => rfl
  | False => rfl

theorem Bool.andTrue: (b: Bool) → (b ∧ True) = b
  | True => rfl
  | False => rfl

theorem List.splitStepSep (x: a): (st: Pair (List a) (List (List a))) → List.splitStep x True st = MkPair Nil (List.closeGroup (Pair.fst st) (Pair.snd st))
  | MkPair cur done => rfl

theorem List.splitStepJoin (x: a): (st: Pair (List a) (List (List a))) → List.splitStep x False st = MkPair (Cons x (Pair.fst st)) (Pair.snd st)
  | MkPair cur done => rfl

theorem List.finishGroupsClose: (st: Pair (List a) (List (List a))) → List.finishGroups st = List.closeGroup (Pair.fst st) (Pair.snd st)
  | MkPair cur done => rfl

-- The run from `s` up to the first separator (looking as far as `s + m`).
theorem List.runStop (sep: Nat → Bool) (m: Nat) (s: Nat) (h: sep s = True): Nat.firstFrom sep (Succ m) s - s = 0 :=
  rewrite Nat.firstFromStop sep m s h, Nat.subSelf s

-- The group still open after reading positions s .. s + m - 1 (from the
-- right) is the run from s to the first separator; s + m is a separator.
theorem List.splitGroupsOpen (p: a → Bool) (f: Nat → a) (sep: Nat → Bool) (hsep: (c: Nat) → p (f c) = sep c):
    (m: Nat) → (s: Nat) → sep (s + m) = True →
    Pair.fst (List.splitGroups (List.map (List.rangeFrom m s) f) p) = List.map (List.rangeFrom (Nat.firstFrom sep (Succ m) s - s) s) f
  | Zero, s, e => rewrite List.runStop sep 0 s (rewrite <- Nat.addZero s in e)
  | Succ m, s, e =>
    calc Pair.fst (List.splitGroups (List.map (List.rangeFrom (Succ m) s) f) p)
      _ = Pair.fst (List.splitStep (f s) (p (f s)) (List.splitGroups (List.map (List.rangeFrom m (Succ s)) f) p))
        := Eq.cong Pair.fst (List.splitGroupsCons (List.map (List.rangeFrom m (Succ s)) f) (f s) p)
      _ = Pair.fst (List.splitStep (f s) (sep s) (List.splitGroups (List.map (List.rangeFrom m (Succ s)) f) p)) := rewrite hsep s
      _ = List.map (List.rangeFrom (Nat.firstFrom sep (Succ (Succ m)) s - s) s) f :=
        match h: sep s with
          | True => rewrite List.splitStepSep (f s) (List.splitGroups (List.map (List.rangeFrom m (Succ s)) f) p), Nat.subSelf s
          | False =>
            rewrite List.splitStepJoin (f s) (List.splitGroups (List.map (List.rangeFrom m (Succ s)) f) p), Nat.subSuccRight s (Nat.firstFrom sep (Succ m) (Succ s)) (Nat.firstFromAtLeast sep (Succ m) (Succ s)),
              List.splitGroupsOpen p f sep hsep m (Succ s) (rewrite <- Nat.addSucc s m in e)

theorem Nat.addSubLeft (s: Nat) (m: Nat): (s + m) - s = m := rewrite Nat.addComm s m in Nat.addSub m s

-- The run of positions from `lo` up to the first separator, looking no
-- further than `n`.
def List.runAt (f: Nat → a) (sep: Nat → Bool) (n: Nat) (lo: Nat): List a :=
  List.map (List.rangeFrom (Nat.firstFrom sep (Succ (n - lo)) lo - lo) lo) f

-- Closing the open group adds its term, unless it is empty.
theorem List.closeRunSum (g: List a → Nat) (done: List (List a)) (m: Nat) (s: Nat) (f: Nat → a) (sep: Nat → Bool):
    List.sumBy (List.closeGroup (List.map (List.rangeFrom (Nat.firstFrom sep (Succ m) s - s) s) f) done) g
      = Nat.keepIf (g (List.map (List.rangeFrom (Nat.firstFrom sep (Succ m) s - s) s) f)) (¬(sep s)) + List.sumBy done g :=
  match h: sep s with
    | True => rewrite Nat.subSelf s
    | False =>
      rewrite Nat.subSuccRight s (Nat.firstFrom sep m (Succ s)) (Nat.firstFromAtLeast sep m (Succ s)) in
        List.sumByCons done (Cons (f s) (List.map (List.rangeFrom (Nat.firstFrom sep m (Succ s) - Succ s) (Succ s)) f)) g

-- The groups closed after reading positions s .. s + m - 1: one for every
-- separator c followed by a position c + 1 that isn't one.
theorem List.splitGroupsDone (p: a → Bool) (f: Nat → a) (sep: Nat → Bool) (hsep: (c: Nat) → p (f c) = sep c) (g: List a → Nat):
    (m: Nat) → (s: Nat) → sep (s + m) = True →
    List.sumBy (Pair.snd (List.splitGroups (List.map (List.rangeFrom m s) f) p)) g
      = List.sumBy (List.rangeFrom m s) (c => Nat.keepIf (g (List.runAt f sep (s + m) (Succ c))) (¬(sep (Succ c)) ∧ sep c))
  | Zero, s, e => rfl
  | Succ m, s, e =>
    calc List.sumBy (Pair.snd (List.splitGroups (List.map (List.rangeFrom (Succ m) s) f) p)) g
      _ = List.sumBy (Pair.snd (List.splitStep (f s) (p (f s)) (List.splitGroups (List.map (List.rangeFrom m (Succ s)) f) p))) g
        := Eq.cong (st => List.sumBy (Pair.snd st) g) (List.splitGroupsCons (List.map (List.rangeFrom m (Succ s)) f) (f s) p)
      _ = List.sumBy (Pair.snd (List.splitStep (f s) (sep s) (List.splitGroups (List.map (List.rangeFrom m (Succ s)) f) p))) g := rewrite hsep s
      _ = Nat.keepIf (g (List.runAt f sep (Succ (s + m)) (Succ s))) (¬(sep (Succ s)) ∧ sep s)
          + List.sumBy (List.rangeFrom m (Succ s)) (c => Nat.keepIf (g (List.runAt f sep (Succ (s + m)) (Succ c))) (¬(sep (Succ c)) ∧ sep c)) :=
        match h: sep s with
          | True =>
            rewrite List.splitStepSep (f s) (List.splitGroups (List.map (List.rangeFrom m (Succ s)) f) p),
              List.splitGroupsOpen p f sep hsep m (Succ s) (rewrite <- Nat.addSucc s m in e),
              List.closeRunSum g (Pair.snd (List.splitGroups (List.map (List.rangeFrom m (Succ s)) f) p)) m (Succ s) f sep,
              List.splitGroupsDone p f sep hsep g m (Succ s) (rewrite <- Nat.addSucc s m in e),
              Bool.andTrue (¬(sep (Succ s))), Nat.addSubLeft s m
          | False =>
            rewrite List.splitStepJoin (f s) (List.splitGroups (List.map (List.rangeFrom m (Succ s)) f) p),
              List.splitGroupsDone p f sep hsep g m (Succ s) (rewrite <- Nat.addSucc s m in e),
              Bool.andFalse (¬(sep (Succ s)))
      _ = List.sumBy (List.rangeFrom (Succ m) s) (c => Nat.keepIf (g (List.runAt f sep (s + Succ m) (Succ c))) (¬(sep (Succ c)) ∧ sep c)) :=
        rewrite Nat.addSucc s m in
          Eq.sym (List.sumByCons (List.rangeFrom m (Succ s)) s (c => Nat.keepIf (g (List.runAt f sep (Succ (s + m)) (Succ c))) (¬(sep (Succ c)) ∧ sep c)))

-- All the groups: the run from 0, then one for every separator followed by
-- a position that isn't one.
theorem List.splitByStarts (p: a → Bool) (f: Nat → a) (sep: Nat → Bool) (hsep: (c: Nat) → p (f c) = sep c) (g: List a → Nat) (n: Nat) (end: sep n = True):
    List.sumBy (List.splitBy (List.map (List.range n) f) p) g
      = Nat.keepIf (g (List.runAt f sep n 0)) (¬(sep 0))
        + List.sumBy (List.range n) (c => Nat.keepIf (g (List.runAt f sep n (Succ c))) (¬(sep (Succ c)) ∧ sep c)) :=
  rewrite List.finishGroupsClose (List.splitGroups (List.map (List.rangeFrom n 0) f) p),
    List.splitGroupsOpen p f sep hsep n 0 end,
    List.closeRunSum g (Pair.snd (List.splitGroups (List.map (List.rangeFrom n 0) f) p)) n 0 f sep,
    List.splitGroupsDone p f sep hsep g n 0 end

-- `lo .. hi - 1` is a maximal run of positions that aren't separators: the
-- one before it is a separator (or lo is 0), it isn't empty, none in it is a
-- separator, and hi is one.
@[noReceiver]
def Nat.isRun (sep: Nat → Bool) (lo: Nat) (hi: Nat): Bool :=
  (lo == 0 ∨ sep (lo - 1)) ∧ (lo < hi ∧ (List.all (List.rangeFrom (hi - lo) lo) (i => ¬(sep i)) ∧ sep hi))

theorem List.isRunNoEdge (sep: Nat → Bool) (lo: Nat) (hi: Nat) (h: (lo == 0 ∨ sep (lo - 1)) = False): Nat.isRun sep lo hi = False :=
  calc Nat.isRun sep lo hi
    _ = ((lo == 0 ∨ sep (lo - 1)) ∧ (lo < hi ∧ (List.all (List.rangeFrom (hi - lo) lo) (c => ¬(sep c)) ∧ sep hi)))
    _ = False := rewrite h

theorem List.isRunSepStart (sep: Nat → Bool) (lo: Nat) (hi: Nat) (h: sep lo = True): Nat.isRun sep lo hi = False :=
  calc Nat.isRun sep lo hi
    _ = ((lo == 0 ∨ sep (lo - 1)) ∧ (lo < hi ∧ (List.all (List.rangeFrom (hi - lo) lo) (c => ¬(sep c)) ∧ sep hi)))
    _ = ((lo == 0 ∨ sep (lo - 1)) ∧ False) :=
      match e: Nat.leq (Succ lo) hi with
        | False => rfl
        | True => rewrite Nat.subSuccRight lo hi e, h
    _ = False := Bool.andFalse (lo == 0 ∨ sep (lo - 1))

-- A run that starts at lo ends at the first separator after it.
theorem List.isRunEnd (sep: Nat → Bool) (n: Nat) (lo: Nat) (hlo: lo < n) (end: sep n = True) (hi: Nat) (h: Nat.isRun sep lo hi = True):
    hi = Nat.firstFrom sep (Succ (n - lo)) lo :=
  let rest := Bool.andRight (lo == 0 ∨ sep (lo - 1)) (lo < hi ∧ (List.all (List.rangeFrom (hi - lo) lo) (c => ¬(sep c)) ∧ sep hi)) h
  let long: Succ lo ≤ hi :=
    Bool.andLeft (lo < hi) (List.all (List.rangeFrom (hi - lo) lo) (c => ¬(sep c)) ∧ sep hi) rest
  let inner := Bool.andRight (lo < hi) (List.all (List.rangeFrom (hi - lo) lo) (c => ¬(sep c)) ∧ sep hi) rest
  let none := Bool.andLeft (List.all (List.rangeFrom (hi - lo) lo) (c => ¬(sep c))) (sep hi) inner
  let stop := Bool.andRight (List.all (List.rangeFrom (hi - lo) lo) (c => ¬(sep c))) (sep hi) inner
  let found := Nat.firstFromFound sep (Succ (n - lo)) lo n (Nat.lessLe lo n hlo)
    (rewrite Nat.addSucc lo (n - lo), Nat.addSubCancel lo n (Nat.lessLe lo n hlo) in Nat.leRefl (Succ n)) end
  match e: Nat.leq hi (Nat.firstFrom sep (Succ (n - lo)) lo) with
    | True => Nat.leAntisym hi (Nat.firstFrom sep (Succ (n - lo)) lo) e (Nat.firstFromLe sep (Succ (n - lo)) lo hi (Nat.lessLe lo hi long) stop)
    | False =>
      Void.exfalso (Bool.trueNotFalse (Eq.trans (Eq.sym found)
        (calc sep (Nat.firstFrom sep (Succ (n - lo)) lo)
          _ = ¬(¬(sep (Nat.firstFrom sep (Succ (n - lo)) lo))) := match sep (Nat.firstFrom sep (Succ (n - lo)) lo) with | True => rfl | False => rfl
          _ = False := rewrite List.allRangeElim (c => ¬(sep c)) (hi - lo) lo none (Nat.firstFrom sep (Succ (n - lo)) lo)
            (Nat.firstFromAtLeast sep (Succ (n - lo)) lo)
            (rewrite Nat.addSubCancel lo hi (Nat.lessLe lo hi long) in Nat.leqFalse hi (Nat.firstFrom sep (Succ (n - lo)) lo) e))))

-- The run that starts at lo (it does start there) is a maximal run.
theorem List.isRunRun (sep: Nat → Bool) (n: Nat) (lo: Nat) (hlo: lo < n) (end: sep n = True)
    (h1: sep lo = False) (h2: (lo == 0 ∨ sep (lo - 1)) = True): Nat.isRun sep lo (Nat.firstFrom sep (Succ (n - lo)) lo) = True :=
  let v := Nat.firstFrom sep (Succ (n - lo)) lo
  let found: sep v = True := Nat.firstFromFound sep (Succ (n - lo)) lo n (Nat.lessLe lo n hlo)
    (rewrite Nat.addSucc lo (n - lo), Nat.addSubCancel lo n (Nat.lessLe lo n hlo) in Nat.leRefl (Succ n)) end
  let atLeast: lo ≤ v := Nat.firstFromAtLeast sep (Succ (n - lo)) lo
  let long: Succ lo ≤ v := Nat.leNeSucc lo v atLeast (e => Bool.falseNotTrue (Eq.trans (Eq.sym h1) (rewrite e in found)))
  Bool.andIntro (lo == 0 ∨ sep (lo - 1)) (lo < v ∧ (List.all (List.rangeFrom (v - lo) lo) (c => ¬(sep c)) ∧ sep v)) h2
    (Bool.andIntro (lo < v) (List.all (List.rangeFrom (v - lo) lo) (c => ¬(sep c)) ∧ sep v) long
      (Bool.andIntro (List.all (List.rangeFrom (v - lo) lo) (c => ¬(sep c))) (sep v)
        (List.allRangeIntro (c => ¬(sep c)) (v - lo) lo (k k1 k2 =>
          rewrite Nat.firstFromBefore sep (Succ (n - lo)) lo k k1 (rewrite <- Nat.addSubCancel lo v atLeast in k2)))
        found))

theorem List.runsFromEdge (sep: Nat → Bool) (f: Nat → a) (g: List a → Nat) (n: Nat) (end: sep n = True) (lo: Nat) (hlo: lo < n) (h1: sep lo = False):
    (b: Bool) → (lo == 0 ∨ sep (lo - 1)) = b →
    List.sumBy (List.range (Succ n)) (hi => Nat.keepIf (g (List.map (List.rangeFrom (hi - lo) lo) f)) (Nat.isRun sep lo hi))
      = Nat.keepIf (g (List.runAt f sep n lo)) b
  | False, h2 => List.sumRangeNone (hi => Nat.isRun sep lo hi) (hi => g (List.map (List.rangeFrom (hi - lo) lo) f)) (Succ n) 0
    (b b1 b2 => List.isRunNoEdge sep lo b h2)
  | True, h2 =>
    List.sumRangeOne (hi => Nat.isRun sep lo hi) (hi => g (List.map (List.rangeFrom (hi - lo) lo) f))
      (Nat.firstFrom sep (Succ (n - lo)) lo) (List.isRunRun sep n lo hlo end h1 h2)
      (List.isRunEnd sep n lo hlo end) (Succ n) 0 (Nat.zeroLe (Nat.firstFrom sep (Succ (n - lo)) lo))
      (Nat.firstFromLe sep (Succ (n - lo)) lo n (Nat.lessLe lo n hlo) end)

-- For each lo, the maximal runs starting there: one if a run starts at lo, none otherwise.
theorem List.runsFrom (sep: Nat → Bool) (f: Nat → a) (g: List a → Nat) (n: Nat) (end: sep n = True) (lo: Nat) (hlo: lo < n):
    List.sumBy (List.range (Succ n)) (hi => Nat.keepIf (g (List.map (List.rangeFrom (hi - lo) lo) f)) (Nat.isRun sep lo hi))
      = Nat.keepIf (g (List.runAt f sep n lo)) (¬(sep lo) ∧ (lo == 0 ∨ sep (lo - 1))) :=
  List.runsFromStart sep f g n end lo hlo (sep lo) rfl

theorem List.runsFromStart (sep: Nat → Bool) (f: Nat → a) (g: List a → Nat) (n: Nat) (end: sep n = True) (lo: Nat) (hlo: lo < n):
    (b: Bool) → sep lo = b →
    List.sumBy (List.range (Succ n)) (hi => Nat.keepIf (g (List.map (List.rangeFrom (hi - lo) lo) f)) (Nat.isRun sep lo hi))
      = Nat.keepIf (g (List.runAt f sep n lo)) (¬b ∧ (lo == 0 ∨ sep (lo - 1)))
  | True, h1 => List.sumRangeNone (hi => Nat.isRun sep lo hi) (hi => g (List.map (List.rangeFrom (hi - lo) lo) f)) (Succ n) 0
    (b b1 b2 => List.isRunSepStart sep lo b h1)
  | False, h1 => List.runsFromEdge sep f g n end lo hlo h1 (lo == 0 ∨ sep (lo - 1)) rfl

theorem List.sumRangeLast (f: Nat → Nat) (n: Nat): List.sumBy (List.range (Succ n)) f = List.sumBy (List.range n) f + f n :=
  calc List.sumBy (List.rangeFrom (Succ n) 0) f
    _ = List.sumBy (List.append (List.rangeFrom n 0) (List.rangeFrom 1 (0 + n))) f := rewrite <- List.rangeFromAppend n 1 0, Nat.addOne n
    _ = List.sumBy (List.range n) f + f n := List.sumByAppend (List.rangeFrom n 0) (List.rangeFrom 1 n) f

-- The runs by where they start: at 0, or just after a separator.
theorem List.runStarts (sep: Nat → Bool) (r: Nat → Nat): (n: Nat) → sep n = True →
    List.sumBy (List.range n) (lo => Nat.keepIf (r lo) (¬(sep lo) ∧ (lo == 0 ∨ sep (lo - 1))))
      = Nat.keepIf (r 0) (¬(sep 0)) + List.sumBy (List.range n) (c => Nat.keepIf (r (Succ c)) (¬(sep (Succ c)) ∧ sep c))
  | Zero, end => rewrite end
  | Succ n, end =>
    calc List.sumBy (List.rangeFrom (Succ n) 0) (lo => Nat.keepIf (r lo) (¬(sep lo) ∧ (lo == 0 ∨ sep (lo - 1))))
      _ = Nat.keepIf (r 0) (¬(sep 0) ∧ True)
          + List.sumBy (List.rangeFrom n 1) (lo => Nat.keepIf (r lo) (¬(sep lo) ∧ (lo == 0 ∨ sep (lo - 1))))
        := List.sumByCons (List.rangeFrom n 1) 0 (lo => Nat.keepIf (r lo) (¬(sep lo) ∧ (lo == 0 ∨ sep (lo - 1))))
      _ = Nat.keepIf (r 0) (¬(sep 0)) + List.sumBy (List.range n) (c => Nat.keepIf (r (Succ c)) (¬(sep (Succ c)) ∧ sep c))
        := rewrite Bool.andTrue (¬(sep 0)), List.sumByRangeShift (lo => Nat.keepIf (r lo) (¬(sep lo) ∧ (lo == 0 ∨ sep (lo - 1)))) n 0
      _ = Nat.keepIf (r 0) (¬(sep 0)) + (List.sumBy (List.range n) (c => Nat.keepIf (r (Succ c)) (¬(sep (Succ c)) ∧ sep c)) + 0)
        := rewrite Nat.addZero (List.sumBy (List.range n) (c => Nat.keepIf (r (Succ c)) (¬(sep (Succ c)) ∧ sep c)))
      _ = Nat.keepIf (r 0) (¬(sep 0)) + List.sumBy (List.range (Succ n)) (c => Nat.keepIf (r (Succ c)) (¬(sep (Succ c)) ∧ sep c))
        := rewrite List.sumRangeLast (c => Nat.keepIf (r (Succ c)) (¬(sep (Succ c)) ∧ sep c)) n, end

-- Splitting the positions 0 .. n - 1 at the separators gives exactly the
-- maximal runs `lo .. hi - 1` (`Nat.isRun`), when position n is a separator.
theorem List.splitByRuns (p: a → Bool) (f: Nat → a) (sep: Nat → Bool) (hsep: (c: Nat) → p (f c) = sep c) (g: List a → Nat) (n: Nat) (end: sep n = True):
    List.sumBy (List.splitBy (List.map (List.range n) f) p) g
      = List.sumBy (List.range n) (lo => List.sumBy (List.range (Succ n)) (hi => Nat.keepIf (g (List.map (List.rangeFrom (hi - lo) lo) f)) (Nat.isRun sep lo hi))) :=
  calc List.sumBy (List.splitBy (List.map (List.range n) f) p) g
    _ = Nat.keepIf (g (List.runAt f sep n 0)) (¬(sep 0))
        + List.sumBy (List.range n) (c => Nat.keepIf (g (List.runAt f sep n (Succ c))) (¬(sep (Succ c)) ∧ sep c))
      := List.splitByStarts p f sep hsep g n end
    _ = List.sumBy (List.range n) (lo => Nat.keepIf (g (List.runAt f sep n lo)) (¬(sep lo) ∧ (lo == 0 ∨ sep (lo - 1))))
      := Eq.sym (List.runStarts sep (lo => g (List.runAt f sep n lo)) n end)
    _ = List.sumBy (List.range n) (lo => List.sumBy (List.range (Succ n)) (hi => Nat.keepIf (g (List.map (List.rangeFrom (hi - lo) lo) f)) (Nat.isRun sep lo hi)))
      := List.sumByCongRange (lo => Nat.keepIf (g (List.runAt f sep n lo)) (¬(sep lo) ∧ (lo == 0 ∨ sep (lo - 1))))
        (lo => List.sumBy (List.range (Succ n)) (hi => Nat.keepIf (g (List.map (List.rangeFrom (hi - lo) lo) f)) (Nat.isRun sep lo hi))) n 0
        (lo l1 l2 => Eq.sym (List.runsFrom sep f g n end lo l2))

-- Sums and products don't mind the order.
theorem List.sumReverse (xs: List Nat): List.sum (List.reverse xs) = List.sum xs := List.sumByReverse xs (x => x)

theorem List.productFrom [auto mul: Mul a]: (xs: List a) → (z: a) → List.foldLeft xs z Mul.mul = z * List.product xs
  | Nil, z => Eq.sym (mul.mulOne z)
  | Cons x xs, z =>
    calc List.foldLeft xs (z * x) Mul.mul
      _ = (z * x) * List.product xs := List.productFrom xs (z * x)
      _ = z * (x * List.product xs) := mul.assoc z x (List.product xs)
      _ = z * List.foldLeft xs x Mul.mul := Eq.cong (t => z * t) (Eq.sym (List.productFrom xs x))
      _ = z * List.product (Cons x xs) := Eq.cong (t => z * List.foldLeft xs t Mul.mul) (Eq.sym (mul.oneMul x))

theorem List.productCons [auto mul: Mul a] (x: a) (xs: List a): List.product (Cons x xs) = x * List.product xs :=
  Eq.trans (Eq.cong (t => List.foldLeft xs t Mul.mul) (mul.oneMul x)) (List.productFrom xs x)

theorem List.productReverseOnto: (xs: List Nat) → (acc: List Nat) → List.product (List.reverseOnto xs acc) = List.product xs * List.product acc
  | Nil, acc => ring
  | Cons x xs, acc =>
    rewrite List.productReverseOnto xs (Cons x acc), List.productCons x acc, List.productCons x xs in ring

theorem List.productReverse (xs: List Nat): List.product (List.reverse xs) = List.product xs :=
  rewrite List.productReverseOnto xs Nil in ring

-- Taking away a smaller sum term by term.
theorem List.sumBySplit (xs: List a) (f: a → Nat) (g: a → Nat) (h: (x: a) → g x ≤ f x):
    List.sumBy xs f = List.sumBy xs g + List.sumBy xs (x => f x - g x) :=
  calc List.sumBy xs f
    _ = List.sumBy xs (x => g x + (f x - g x)) := List.sumByCong xs f (x => g x + (f x - g x)) (x => Eq.sym (Nat.addSubCancel (g x) (f x) (h x)))
    _ = List.sumBy xs g + List.sumBy xs (x => f x - g x) := List.sumByAdd xs g (x => f x - g x)

theorem List.sumByLe (xs: List a) (f: a → Nat) (g: a → Nat) (h: (x: a) → g x ≤ f x): List.sumBy xs g ≤ List.sumBy xs f :=
  rewrite List.sumBySplit xs f g h in Nat.leAddRight (List.sumBy xs g) (List.sumBy xs (x => f x - g x))

theorem List.sumBySub (xs: List a) (f: a → Nat) (g: a → Nat) (h: (x: a) → g x ≤ f x):
    List.sumBy xs f - List.sumBy xs g = List.sumBy xs (x => f x - g x) :=
  rewrite List.sumBySplit xs f g h in Nat.addSubLeft (List.sumBy xs g) (List.sumBy xs (x => f x - g x))

-- Counting with tests that agree on the list's elements (SW-198, day 8).
theorem List.countCongMem (xs: List a) (p1: a → Bool) (p2: a → Bool) (ep: (x: a) → (m: List.Mem x xs) → p1 x = p2 x): List.count xs p1 = List.count xs p2 :=
  rewrite List.countOccurrences xs p1, List.countOccurrences xs p2 in List.occurrencesCongMem xs p1 p2 ep

-- Counting with a test that passes wherever another does, on the list's
-- elements, counts at least as many.
theorem List.countLeMem: (xs: List a) → (p: a → Bool) → (q: a → Bool) → ((x: a) → (m: List.Mem x xs) → p x = True → q x = True) →
    List.count xs p ≤ List.count xs q
  | Nil, p, q, weaker => Nat.leRefl 0
  | Cons x rest, p, q, weaker =>
    let below := List.countLeMem rest p q (y m => weaker y (Inr m))
    rewrite List.countCons rest x p, List.countCons rest x q in
    match passes: p x with
      | True => rewrite weaker x (Inl rfl) passes in omega
      | False => omega

-- `all` is "no element fails", so a permutation keeps it.
theorem List.allNotAny: (xs: List a) → (p: a → Bool) → List.all xs p = ¬(List.any xs (x => ¬(p x)))
  | Nil, p => rfl
  | Cons x xs, p =>
    match e: p x with
      | True => List.allNotAny xs p
      | False => rfl

-- "No x is related to any y" read either way round.
theorem List.allNotAnyComm (related: a → b → Bool): (xs: List a) → (ys: List b) →
    List.all xs (x => ¬(List.any ys (y => related x y))) = List.all ys (y => ¬(List.any xs (x => related x y)))
  | Nil, ys => Eq.sym (List.allTrue ys (y => True) (y => rfl))
  | Cons x xs, ys =>
    let unfolded := List.allCong ys (y => ¬(List.any (Cons x xs) (x2 => related x2 y))) (y => ¬(related x y) ∧ ¬(List.any xs (x2 => related x2 y)))
      (y =>
        match r: related x y with
          | True => rfl
          | False => rfl)
    rewrite unfolded, List.allAnd ys (y => ¬(related x y)) (y => ¬(List.any xs (x2 => related x2 y))), <- List.allNotAnyComm related xs ys,
      List.allNotAny ys (y => ¬(related x y))
      in rewrite List.anyCong ys (y => ¬(¬(related x y))) (y => related x y) (y => cases) in rfl

theorem List.allPerm (xs: List a) (ys: List a) (h: List.Perm xs ys) (p: a → Bool): List.all xs p = List.all ys p :=
  rewrite List.allNotAny xs p, List.allNotAny ys p, List.anyPerm xs ys h (x => ¬(p x)) in rfl

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

theorem List.sortOnEq [auto ord: Ord k] (xs: List a) (key: a → k):
    List.sortOn xs key = List.sortBy xs (x y => Ord.compare (key x) (key y)) := rfl

theorem List.sortOnPerm [auto ord: Ord k] (xs: List a) (key: a → k): List.Perm (List.sortOn xs key) xs :=
  List.sortByPerm xs (x y => Ord.compare (key x) (key y))

-- The keys of the sorted list are the sorted keys.
theorem List.sortOnMap [auto ord: Ord k] (xs: List a) (key: a → k):
    List.map (List.sortOn xs key) key = List.sort (List.map xs key) :=
  List.sortByMap xs key Ord.compare (x y => Ord.compare (key x) (key y)) (x y => rfl)

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

-- dedup ---------------------------------------------------------------------

-- What `List.dedupAfter` keeps was in the list.
theorem List.memDedupAfter [auto eq: DecEq a] (x: a): (previous: a) → (xs: List a) → List.Mem x (List.dedupAfter previous xs) → List.Mem x xs
  | previous, Nil, m => m
  | previous, Cons y ys, m =>
    match e: y == previous with
      | True => Inr (List.memDedupAfter x previous ys m)
      | False =>
        match m with
          | Inl q => Inl q
          | Inr rest => Inr (List.memDedupAfter x y ys rest)

-- And it drops only elements equal to the one before.
theorem List.memDedupAfterIntro [auto eq: DecEq a] (x: a): (previous: a) → (xs: List a) → List.Mem x xs →
    Or (previous = x) (List.Mem x (List.dedupAfter previous xs))
  | previous, Nil, m => Void.exfalso m
  | previous, Cons y ys, m =>
    match e: y == previous with
      | True =>
        match m with
          | Inl q => Inl (Eq.trans (Eq.sym (DecEq.sound y previous e)) q)
          | Inr rest => List.memDedupAfterIntro x previous ys rest
      | False =>
        match m with
          | Inl q => Inr (Inl q)
          | Inr rest =>
            match List.memDedupAfterIntro x y ys rest with
              | Inl q => Inr (Inl q)
              | Inr later => Inr (Inr later)

-- What `List.dedup` keeps was in the list.
theorem List.memDedupElim [auto eq: DecEq a] (x: a): (xs: List a) → List.Mem x (List.dedup xs) → List.Mem x xs
  | Nil, m => m
  | Cons y ys, Inl q => Inl q
  | Cons y ys, Inr rest => Inr (List.memDedupAfter x y ys rest)

-- `List.dedup` keeps every value.
theorem List.memDedupIntro [auto eq: DecEq a] (x: a): (xs: List a) → List.Mem x xs → List.Mem x (List.dedup xs)
  | Nil, m => m
  | Cons y ys, Inl q => Inl q
  | Cons y ys, Inr rest =>
    match List.memDedupAfterIntro x y ys rest with
      | Inl q => Inl q
      | Inr later => Inr later

-- `List.dedup` keeps a list sorted.
theorem List.sortedDedupAfter [auto eq: DecEq a] (le: a → a → Bool): (previous: a) → (xs: List a) → List.Sorted le (Cons previous xs) →
    List.Sorted le (Cons previous (List.dedupAfter previous xs))
  | previous, Nil, s => s
  | previous, Cons y ys, Both first rest =>
    match e: y == previous with
      | True => List.sortedDedupAfter le previous ys (rewrite DecEq.sound y previous e at rest)
      | False => Both first (List.sortedDedupAfter le y ys rest)

theorem List.sortedDedup [auto eq: DecEq a] (le: a → a → Bool): (xs: List a) → List.Sorted le xs → List.Sorted le (List.dedup xs)
  | Nil, s => s
  | Cons y ys, s => List.sortedDedupAfter le y ys s

-- A sum over the first n + 1 numbers is the first term and the sum over the rest.
theorem List.sumByRangeSucc (f: Nat → Nat) (n: Nat): List.sumBy (List.range (Succ n)) f = f 0 + List.sumBy (List.range n) (i => f (Succ i)) :=
  rewrite List.sumByCons (List.rangeFrom n 1) 0 f, List.sumByRangeShift f n 0 in rfl
