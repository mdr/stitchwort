-- Sorting: merge sort and its proofs (sorted, a permutation, the same length),
-- with the Bool, Nat and List lemmas around them (sums of lists, Gauss, counting
-- occurrences). This file was the prelude's "Sorting" section; the declarations
-- that the core or a later section of the prelude uses stayed there.
--
-- A library file is written like the prelude: names are as they are in the
-- namespaces they go in (`List.sort` is `Std.List.sort`), so one file can add
-- to several namespaces. It is checked when a program uses something in it.

-- `||` on `Bool`s: `False` is its unit, `True` absorbs, and it groups and
-- commutes.
theorem Bool.orFalse: (b: Bool) -> (b || False) = b
  | True  => rfl
  | False => rfl

theorem Bool.orTrue: (b: Bool) -> (b || True) = True
  | True  => rfl
  | False => rfl

theorem Bool.orAssoc: (a: Bool) -> (b: Bool) -> (c: Bool) -> ((a || b) || c) = (a || (b || c))
  | True,  b, c => rfl
  | False, b, c => rfl

theorem Bool.orComm: (a: Bool) -> (b: Bool) -> (a || b) = (b || a)
  | True,  True  => rfl
  | True,  False => rfl
  | False, True  => rfl
  | False, False => rfl

-- `&&` from its sides and back; `not a || b` as "a implies b"; two booleans
-- are equal when each implies the other.
theorem Bool.andIntro: (a: Bool) -> (b: Bool) -> a = True -> b = True -> (a && b) = True
  | True,  b, ha, hb => hb
  | False, b, ha, hb => Void.exfalso (Bool.falseNotTrue ha)

theorem Bool.andLeft: (a: Bool) -> (b: Bool) -> (a && b) = True -> a = True
  | True,  b, h => rfl
  | False, b, h => Void.exfalso (Bool.falseNotTrue h)

theorem Bool.andRight: (a: Bool) -> (b: Bool) -> (a && b) = True -> b = True
  | True,  b, h => h
  | False, b, h => Void.exfalso (Bool.falseNotTrue h)

theorem Bool.impIntro: (a: Bool) -> (b: Bool) -> (a = True -> b = True) -> (Bool.not a || b) = True
  | True,  b, h => h rfl
  | False, b, h => rfl

theorem Bool.impElim: (a: Bool) -> (b: Bool) -> (Bool.not a || b) = True -> a = True -> b = True
  | True,  b, h, ha => h
  | False, b, h, ha => Void.exfalso (Bool.falseNotTrue ha)

theorem Bool.eqOf: (a: Bool) -> (b: Bool) -> (a = True -> b = True) -> (b = True -> a = True) -> a = b
  | True,  True,  f, g => rfl
  | True,  False, f, g => Void.exfalso (Bool.falseNotTrue (f rfl))
  | False, True,  f, g => Void.exfalso (Bool.falseNotTrue (g rfl))
  | False, False, f, g => rfl

theorem Nat.addRotate (a: Nat) (b: Nat) (c: Nat): (a + b) + c = b + (a + c) := Eq.trans (Eq.cong (\t => t + c) (Nat.addComm a b)) (Nat.addAssoc b a c)

theorem Nat.addLeftComm (a: Nat) (b: Nat) (c: Nat): a + (b + c) = b + (a + c) := Eq.trans (Eq.sym (Nat.addAssoc a b c)) (Nat.addRotate a b c)

-- `<=` is total: if `m <= n` is false, then `n <= m`.
theorem Nat.leqTotal (m: Nat) (n: Nat) (h: Nat.leq m n = False): Nat.leq n m = True := Nat.lessLe n m (Nat.leqFalse m n h)

-- Sums of lists: one element at a time, sums of intervals (Gauss), and
-- rewriting under `map`, `filter` and `foldLeft`.
theorem Nat.addSwap (a: Nat) (b: Nat) (c: Nat) (d: Nat): (a + b) + (c + d) = (a + c) + (b + d) :=
  Eq.trans (Nat.addAssoc a b (c + d))
    (Eq.trans (Eq.cong (\t => a + t) (Nat.addLeftComm b c d)) (Eq.sym (Nat.addAssoc a c (b + d))))

theorem List.sumFrom: (a: Nat) -> (xs: List Nat) -> List.foldLeft Nat.add a xs = a + List.sum xs
  | a, Nil       => Eq.sym (Nat.addZero a)
  | a, Cons x xs =>
    Eq.trans (List.sumFrom (a + x) xs)
      (Eq.trans (Nat.addAssoc a x (List.sum xs)) (Eq.cong (\t => a + t) (Eq.sym (List.sumFrom x xs))))

theorem List.sumCons (x: Nat) (xs: List Nat): List.sum (Cons x xs) = x + List.sum xs := List.sumFrom x xs

theorem List.sumByCongr (f: a -> Nat) (g: a -> Nat) (h: (x: a) -> f x = g x): (xs: List a) -> List.sumBy f xs = List.sumBy g xs
  | Nil       => rfl
  | Cons x xs =>
    Eq.trans (List.sumByCons f x xs)
      (Eq.trans (Eq.cong (\t => t + List.sumBy f xs) (h x))
        (Eq.trans (Eq.cong (\t => g x + t) (List.sumByCongr f g h xs)) (Eq.sym (List.sumByCons g x xs))))

theorem List.sumByMulLeft (c: Nat) (f: a -> Nat): (xs: List a) -> List.sumBy (\x => c * f x) xs = c * List.sumBy f xs
  | Nil       => Eq.sym (Nat.mulZero c)
  | Cons x xs =>
    Eq.trans (List.sumByCons (\y => c * f y) x xs)
      (Eq.trans (Eq.cong (\t => c * f x + t) (List.sumByMulLeft c f xs))
        (Eq.sym (Eq.trans (Eq.cong (\t => c * t) (List.sumByCons f x xs)) (Nat.mulDistribLeft c (f x) (List.sumBy f xs)))))

theorem List.sumByRangeShift (f: Nat -> Nat): (n: Nat) -> (s: Nat) ->
    List.sumBy f (List.rangeFrom n (Succ s)) = List.sumBy (\i => f (Succ i)) (List.rangeFrom n s)
  | Zero,   s => rfl
  | Succ n, s =>
    Eq.trans (List.sumByCons f (Succ s) (List.rangeFrom n (Succ (Succ s))))
      (Eq.trans (Eq.cong (\t => f (Succ s) + t) (List.sumByRangeShift f n (Succ s)))
        (Eq.sym (List.sumByCons (\i => f (Succ i)) s (List.rangeFrom n (Succ s)))))

-- Gauss: twice the sum of `x, x + 1, ..., x + d` is `(d + 1) * (x + (x + d))`.
theorem List.gaussSum: (d: Nat) -> (x: Nat) ->
    List.sum (List.rangeFrom (Succ d) x) + List.sum (List.rangeFrom (Succ d) x) = Succ d * (x + (x + d))
  | Zero,   x => Eq.sym (Eq.trans (Nat.addZero (x + (x + 0))) (Eq.cong (\t => x + t) (Nat.addZero x)))
  | Succ d, x =>
    Eq.trans (Eq.cong (\t => t + t) (List.sumCons x (List.rangeFrom (Succ d) (Succ x))))
      (Eq.trans (Nat.addSwap x (List.sum (List.rangeFrom (Succ d) (Succ x))) x (List.sum (List.rangeFrom (Succ d) (Succ x))))
        (Eq.trans (Eq.cong (\t => (x + x) + t) (List.gaussSum d (Succ x)))
          (Eq.trans (Eq.cong (\t => (x + x) + Succ d * Succ (x + t)) (Eq.sym (Nat.addSucc x d)))
            (Eq.trans (Eq.cong (\t => (x + x) + t) (Nat.mulSucc (Succ d) (x + (x + Succ d))))
              (Eq.trans (Eq.sym (Nat.addAssoc (x + x) (Succ d) (Succ d * (x + (x + Succ d)))))
                (Eq.cong (\t => t + Succ d * (x + (x + Succ d))) (Nat.addAssoc x x (Succ d))))))))

-- `x + (x + 1) + ... + (y - 1)`
def Nat.span (x: Nat) (y: Nat): Nat := List.sum (List.rangeFrom (y - x) x)

theorem Nat.spanEmpty (x: Nat) (y: Nat) (h: y <= x): Nat.span x y = 0 := Eq.cong (\t => List.sum (List.rangeFrom t x)) (Nat.subEqZero y x h)

theorem Nat.spanStep (s: Nat) (y: Nat) (h: Succ s <= y): Nat.span s y = s + Nat.span (Succ s) y :=
  Eq.trans (Eq.cong (\t => List.sum (List.rangeFrom t s)) (Nat.subSuccRight s y h)) (List.sumCons s (List.rangeFrom (y - Succ s) (Succ s)))

-- The closed form is the sum of `lo..hi`.
theorem Nat.gaussSpan (d: Nat) (lo: Nat) (hi: Nat) (h: lo <= hi): d * ((lo + hi) * (hi - lo + 1) / 2) = d * Nat.span lo (Succ hi) :=
  Eq.trans
    (Eq.cong (\t => d * (t / 2))
      (Eq.trans (Eq.cong (\t => (lo + t) * (hi - lo + 1)) (Eq.sym (Nat.addSubCancel lo hi h)))
        (Eq.trans (Eq.cong (\t => (lo + (lo + (hi - lo))) * t) (Nat.addOne (hi - lo)))
          (Eq.trans (Nat.mulComm (lo + (lo + (hi - lo))) (Succ (hi - lo))) (Eq.sym (List.gaussSum (hi - lo) lo))))))
    (Eq.trans (Eq.cong (\t => d * t) (Nat.halfDouble (List.sum (List.rangeFrom (Succ (hi - lo)) lo))))
      (Eq.sym (Eq.cong (\t => d * List.sum (List.rangeFrom t lo)) (Nat.subSuccRight lo (Succ hi) h))))

theorem List.mapCongr (f: a -> b) (g: a -> b) (h: (x: a) -> f x = g x): (xs: List a) -> List.map f xs = List.map g xs
  | Nil       => rfl
  | Cons x xs => Eq.trans (Eq.cong (\y => Cons y (List.map f xs)) (h x)) (Eq.cong (\ys => Cons (g x) ys) (List.mapCongr f g h xs))

-- `p` written n times: n times as long, and one more copy goes on the end.
theorem List.lengthConcatReplicate (p: List a): (n: Nat) -> List.length (List.concat (List.replicate n p)) = n * List.length p
  | Zero   => rfl
  | Succ n => Eq.trans (List.lengthAppend p (List.concat (List.replicate n p))) (Eq.cong (\t => List.length p + t) (List.lengthConcatReplicate p n))

theorem List.concatReplicateSnoc (p: List a): (n: Nat) -> List.concat (List.replicate (Succ n) p) = List.append (List.concat (List.replicate n p)) p
  | Zero   => List.appendNil p
  | Succ n =>
    calc List.append p (List.concat (List.replicate (Succ n) p))
      _ = List.append p (List.append (List.concat (List.replicate n p)) p) := Eq.cong (List.append p) (List.concatReplicateSnoc p n)
      _ = List.append (List.append p (List.concat (List.replicate n p))) p := Eq.sym (List.appendAssoc p (List.concat (List.replicate n p)) p)

theorem List.lengthTake: (k: Nat) -> (xs: List a) -> k <= List.length xs -> List.length (List.take k xs) = k
  | Zero,   xs,        h => rfl
  | Succ k, Nil,       h => Void.exfalso (Bool.falseNotTrue h)
  | Succ k, Cons x xs, h => Eq.cong Succ (List.lengthTake k xs h)

theorem List.takeAll: (k: Nat) -> (xs: List a) -> List.length xs <= k -> List.take k xs = xs
  | Zero,   Nil,       h => rfl
  | Zero,   Cons x xs, h => Void.exfalso (Bool.falseNotTrue h)
  | Succ k, Nil,       h => rfl
  | Succ k, Cons x xs, h => Eq.cong (Cons x) (List.takeAll k xs h)

theorem List.takeAppend: (xs: List a) -> (ys: List a) -> List.take (List.length xs) (List.append xs ys) = xs
  | Nil,       ys => rfl
  | Cons x xs, ys => Eq.cong (Cons x) (List.takeAppend xs ys)

theorem List.headTake (d: a): (k: Nat) -> (xs: List a) -> 1 <= k -> List.headOr d (List.take k xs) = List.headOr d xs
  | Zero,   xs,        h => Void.exfalso (Bool.falseNotTrue h)
  | Succ k, Nil,       h => rfl
  | Succ k, Cons x xs, h => rfl

-- `x` when the condition holds, else 0: a term a sum may leave out.
def Nat.keepIf (x: Nat): Bool -> Nat
  | True  => x
  | False => 0

-- `if b then x else 0` is `keepIf x b`.
theorem Nat.ifKeep (x: Nat): (b: Bool) -> (if b then x else 0) = Nat.keepIf x b
  | True  => rfl
  | False => rfl

theorem List.sumByZero: (xs: List a) -> List.sumBy (\x => 0) xs = 0
  | Nil       => rfl
  | Cons x xs => Eq.trans (List.sumByCons (\x => 0) x xs) (List.sumByZero xs)

theorem Nat.keepIfZero: (b: Bool) -> Nat.keepIf 0 b = 0
  | True  => rfl
  | False => rfl

-- Keeping a sum is keeping each term.
theorem Nat.keepIfSumBy (g: a -> Nat) (xs: List a): (b: Bool) -> Nat.keepIf (List.sumBy g xs) b = List.sumBy (\x => Nat.keepIf (g x) b) xs
  | True  => rfl
  | False => Eq.sym (List.sumByZero xs)

-- `keepIf` as multiplying by 1 or 0.
theorem Nat.mulToNat (x: Nat): (a: Bool) -> x * Bool.toNat a = Nat.keepIf x a
  | True  => Nat.mulOne x
  | False => Nat.mulZero x

theorem Nat.keepIfKeepIf (x: Nat): (a: Bool) -> (b: Bool) -> Nat.keepIf (Nat.keepIf x a) b = x * Bool.toNat (a && b)
  | True,  True  => Eq.sym (Nat.mulOne x)
  | True,  False => Eq.sym (Nat.mulZero x)
  | False, True  => Eq.sym (Nat.mulZero x)
  | False, False => Eq.sym (Nat.mulZero x)

theorem List.sumByAdd (f: a -> Nat) (g: a -> Nat): (xs: List a) -> List.sumBy (\x => f x + g x) xs = List.sumBy f xs + List.sumBy g xs
  | Nil       => rfl
  | Cons x xs =>
    Eq.trans (List.sumByCons (\y => f y + g y) x xs)
      (Eq.trans (Eq.cong (\t => (f x + g x) + t) (List.sumByAdd f g xs))
        (Eq.trans (Nat.addSwap (f x) (g x) (List.sumBy f xs) (List.sumBy g xs))
          (Eq.sym (Eq.trans (Eq.cong (\t => t + List.sumBy g (Cons x xs)) (List.sumByCons f x xs))
            (Eq.cong (\t => (f x + List.sumBy f xs) + t) (List.sumByCons g x xs))))))

theorem List.sumBySwap (h: a -> b -> Nat) (ys: List b): (xs: List a) ->
    List.sumBy (\x => List.sumBy (\y => h x y) ys) xs = List.sumBy (\y => List.sumBy (\x => h x y) xs) ys
  | Nil       => Eq.sym (List.sumByZero ys)
  | Cons x xs =>
    Eq.trans (List.sumByCons (\x => List.sumBy (\y => h x y) ys) x xs)
      (Eq.trans (Eq.cong (\t => List.sumBy (\y => h x y) ys + t) (List.sumBySwap h ys xs))
        (Eq.trans (Eq.sym (List.sumByAdd (\y => h x y) (\y => List.sumBy (\x => h x y) xs) ys))
          (List.sumByCongr (\y => h x y + List.sumBy (\x => h x y) xs) (\y => List.sumBy (\x => h x y) (Cons x xs))
            (\y => Eq.sym (List.sumByCons (\x => h x y) x xs)) ys)))

theorem List.sumByMap (g: b -> Nat) (f: a -> b): (xs: List a) -> List.sumBy g (List.map f xs) = List.sumBy (\x => g (f x)) xs
  | Nil       => rfl
  | Cons x xs =>
    Eq.trans (List.sumByCons g (f x) (List.map f xs))
      (Eq.trans (Eq.cong (\t => g (f x) + t) (List.sumByMap g f xs)) (Eq.sym (List.sumByCons (\x => g (f x)) x xs)))

theorem List.sumFilter (p: Nat -> Bool): (xs: List Nat) -> List.sum (List.filter p xs) = List.sumBy (\x => Nat.keepIf x (p x)) xs
  | Nil       => rfl
  | Cons x xs =>
    Bool.inspect (p x) (\c => List.sum (List.filter p (Cons x xs)) = List.sumBy (\x => Nat.keepIf x (p x)) (Cons x xs))
      (\h => Eq.trans (Eq.cong List.sum (List.filterKeep p x xs h))
        (Eq.trans (List.sumCons x (List.filter p xs))
          (Eq.trans (Eq.cong (\t => Nat.keepIf x t + List.sum (List.filter p xs)) (Eq.sym h))
            (Eq.trans (Eq.cong (\t => Nat.keepIf x (p x) + t) (List.sumFilter p xs))
              (Eq.sym (List.sumByCons (\x => Nat.keepIf x (p x)) x xs))))))
      (\h => Eq.trans (Eq.cong List.sum (List.filterSkip p x xs h))
        (Eq.trans (Eq.cong (\t => Nat.keepIf x t + List.sum (List.filter p xs)) (Eq.sym h))
          (Eq.trans (Eq.cong (\t => Nat.keepIf x (p x) + t) (List.sumFilter p xs))
            (Eq.sym (List.sumByCons (\x => Nat.keepIf x (p x)) x xs)))))

-- Sums over a run of numbers that pick nothing, or pick one.
theorem List.sumRangeNone (q: Nat -> Bool) (g: Nat -> Nat): (c: Nat) -> (s: Nat) ->
    ((b: Nat) -> s <= b -> b < s + c -> q b = False) ->
    List.sumBy (\b => Nat.keepIf (g b) (q b)) (List.rangeFrom c s) = 0
  | Zero,   s, h => rfl
  | Succ c, s, h =>
    Eq.trans (List.sumByCons (\b => Nat.keepIf (g b) (q b)) s (List.rangeFrom c (Succ s)))
      (Eq.trans (Eq.cong (\t => Nat.keepIf (g s) t + List.sumBy (\b => Nat.keepIf (g b) (q b)) (List.rangeFrom c (Succ s))) (h s (Nat.leRefl s) (Nat.ltAddSuccSelf s c)))
        (List.sumRangeNone q g c (Succ s) (\b hb1 hb2 => h b (Nat.leTrans s (Succ s) b (Nat.leSucc s) hb1) (Nat.ltAddSucc s c b hb2))))

theorem List.sumRangeOne (q: Nat -> Bool) (g: Nat -> Nat) (v: Nat) (hv: q v = True) (uniq: (b: Nat) -> q b = True -> b = v):
    (c: Nat) -> (s: Nat) -> s <= v -> v < s + c -> List.sumBy (\b => Nat.keepIf (g b) (q b)) (List.rangeFrom c s) = g v
  | Zero,   s, h1, h2 => Void.exfalso (Nat.lessIrrefl v (Nat.leTrans (Succ v) s v (Nat.ltCongRight v (s + 0) s (Nat.addZero s) h2) h1))
  | Succ c, s, h1, h2 =>
    Bool.inspect (q s) (\u => List.sumBy (\b => Nat.keepIf (g b) (q b)) (List.rangeFrom (Succ c) s) = g v)
      (\hs => Eq.trans (List.sumByCons (\b => Nat.keepIf (g b) (q b)) s (List.rangeFrom c (Succ s)))
        (Eq.trans (Eq.cong (\t => Nat.keepIf (g s) t + List.sumBy (\b => Nat.keepIf (g b) (q b)) (List.rangeFrom c (Succ s))) hs)
          (Eq.trans (Eq.cong (\t => g s + t)
              (List.sumRangeNone q g c (Succ s) (\b hb1 hb2 =>
                Bool.inspect (q b) (\u => u = False)
                  (\t => Void.exfalso (Nat.lessIrrefl s (Nat.leCongRight (Succ s) b s (Eq.trans (uniq b t) (Eq.sym (uniq s hs))) hb1)))
                  (\f => rfl))))
            (Eq.trans (Nat.addZero (g s)) (Eq.cong g (uniq s hs))))))
      (\hs => Eq.trans (List.sumByCons (\b => Nat.keepIf (g b) (q b)) s (List.rangeFrom c (Succ s)))
        (Eq.trans (Eq.cong (\t => Nat.keepIf (g s) t + List.sumBy (\b => Nat.keepIf (g b) (q b)) (List.rangeFrom c (Succ s))) hs)
          (List.sumRangeOne q g v hv uniq c (Succ s)
            (Nat.leNeSucc s v h1 (\e => Bool.trueNotFalse (Eq.trans (Eq.sym hv) (Eq.trans (Eq.cong q (Eq.sym e)) hs))))
            (Nat.ltSuccAdd s c v h2))))

theorem List.sumRangeCongr (f: Nat -> Nat) (g: Nat -> Nat): (c: Nat) -> (s: Nat) -> ((x: Nat) -> s <= x -> x < s + c -> f x = g x) ->
    List.sumBy f (List.rangeFrom c s) = List.sumBy g (List.rangeFrom c s)
  | Zero,   s, h => rfl
  | Succ c, s, h =>
    Eq.trans (List.sumByCons f s (List.rangeFrom c (Succ s)))
      (Eq.trans (Eq.cong (\t => t + List.sumBy f (List.rangeFrom c (Succ s))) (h s (Nat.leRefl s) (Nat.ltAddSuccSelf s c)))
        (Eq.trans (Eq.cong (\t => g s + t) (List.sumRangeCongr f g c (Succ s) (\x hx1 hx2 => h x (Nat.leTrans s (Succ s) x (Nat.leSucc s) hx1) (Nat.ltAddSucc s c x hx2))))
          (Eq.sym (List.sumByCons g s (List.rangeFrom c (Succ s))))))

-- Sums over the ids of a run that pick out `y`.
theorem List.sumRangeEq (y: Nat) (c: Nat) (s: Nat) (h1: s <= y) (h2: y < s + c): List.sumBy (\x => Nat.keepIf x (y == x)) (List.rangeFrom c s) = y :=
  List.sumRangeOne (\x => y == x) (\x => x) y (Decidable.toBoolOf (Nat.decEq y y) rfl) (\b h => Eq.sym (Decidable.toBoolSound (Nat.decEq y b) h)) c s h1 h2

theorem List.sumRangeEqNone (y: Nat) (c: Nat) (s: Nat) (h: (x: Nat) -> s <= x -> x < s + c -> Not (y = x)): List.sumBy (\x => Nat.keepIf x (y == x)) (List.rangeFrom c s) = 0 :=
  List.sumRangeNone (\x => y == x) (\x => x) c s (\b h1 h2 => Decidable.toBoolOfNot (Nat.decEq y b) (h b h1 h2))

-- `any` over a run of numbers: a witness out, a witness in.
theorem List.anyRangeElim (q: Nat -> Bool) (goal: Prop): (c: Nat) -> (s: Nat) -> List.any q (List.rangeFrom c s) = True ->
    ((k: Nat) -> s <= k -> k < s + c -> q k = True -> goal) -> goal
  | Zero,   s, h, k => Void.exfalso (Bool.falseNotTrue h)
  | Succ c, s, h, k =>
    Bool.inspect (q s) (\u => goal)
      (\t => k s (Nat.leRefl s) (Nat.ltAddSuccSelf s c) t)
      (\f => List.anyRangeElim q goal c (Succ s)
        (Eq.trans (Eq.cong (\b => Bool.ifThenElse b (\u => True) (\u => List.any q (List.rangeFrom c (Succ s)))) (Eq.sym f)) h)
        (\j h1 h2 hj => k j (Nat.leTrans s (Succ s) j (Nat.leSucc s) h1) (Nat.ltAddSucc s c j h2) hj))

theorem List.anyRangeIntro (q: Nat -> Bool): (c: Nat) -> (s: Nat) -> (k: Nat) -> s <= k -> k < s + c -> q k = True -> List.any q (List.rangeFrom c s) = True
  | Zero,   s, k, h1, h2, hk => Void.exfalso (Nat.lessIrrefl k (Nat.leTrans (Succ k) s k (Nat.ltCongRight k (s + 0) s (Nat.addZero s) h2) h1))
  | Succ c, s, k, h1, h2, hk =>
    Bool.inspect (q s) (\u => List.any q (List.rangeFrom (Succ c) s) = True)
      (\t => Eq.cong (\b => Bool.ifThenElse b (\u => True) (\u => List.any q (List.rangeFrom c (Succ s)))) t)
      (\f => Eq.trans (Eq.cong (\b => Bool.ifThenElse b (\u => True) (\u => List.any q (List.rangeFrom c (Succ s)))) f)
        (List.anyRangeIntro q c (Succ s) k (Nat.leNeSucc s k h1 (\e => Bool.trueNotFalse (Eq.trans (Eq.sym hk) (Eq.trans (Eq.cong q (Eq.sym e)) f)))) (Nat.ltSuccAdd s c k h2) hk))

-- `all` over a run of numbers: each element passes, and back. With a check
-- that computes to `True`, the first turns a finite computation into a fact
-- about every number of the run.
theorem List.allRangeElim (q: Nat -> Bool): (c: Nat) -> (s: Nat) -> List.all q (List.rangeFrom c s) = True ->
    (k: Nat) -> s <= k -> k < s + c -> q k = True
  | Zero,   s, h, k, h1, h2 => Void.exfalso (Nat.lessIrrefl k (Nat.leTrans (Succ k) s k (Nat.ltCongRight k (s + 0) s (Nat.addZero s) h2) h1))
  | Succ c, s, h, k, h1, h2 =>
    Bool.inspect (q s) (\u => q k = True)
      (\t => Bool.inspect (k == s) (\u => q k = True)
        (\e => J (\z p => q z = True) t (Eq.sym (Decidable.toBoolSound (Nat.decEq k s) e)))
        (\ne => List.allRangeElim q c (Succ s)
          (Eq.trans (Eq.cong (\b => Bool.ifThenElse b (\u => List.all q (List.rangeFrom c (Succ s))) (\u => False)) (Eq.sym t)) h)
          k (Nat.leNeSucc s k h1 (\e => Bool.trueNotFalse (Eq.trans (Eq.sym (Decidable.toBoolOf (Nat.decEq k s) (Eq.sym e))) ne))) (Nat.ltSuccAdd s c k h2)))
      (\f => Void.exfalso (Bool.trueNotFalse (Eq.trans (Eq.sym h) (Eq.cong (\b => Bool.ifThenElse b (\u => List.all q (List.rangeFrom c (Succ s))) (\u => False)) f))))

theorem List.allRangeIntro (q: Nat -> Bool): (c: Nat) -> (s: Nat) -> ((k: Nat) -> s <= k -> k < s + c -> q k = True) -> List.all q (List.rangeFrom c s) = True
  | Zero,   s, h => rfl
  | Succ c, s, h =>
    Eq.trans (Eq.cong (\b => Bool.ifThenElse b (\u => List.all q (List.rangeFrom c (Succ s))) (\u => False)) (h s (Nat.leRefl s) (Nat.ltAddSuccSelf s c)))
      (List.allRangeIntro q c (Succ s) (\k h1 h2 => h k (Nat.leTrans s (Succ s) k (Nat.leSucc s) h1) (Nat.ltAddSucc s c k h2)))

theorem List.allRangeExample: List.all (\k => k * k != 2) (List.rangeFrom 100 0) = True := rfl

-- The first number of the run `s .. s + c - 1` that passes `q` (`s + c` if
-- none does): a least witness, found by computation. Nothing before it passes,
-- and if some `k` of the run passes, so does it, and it is at most `k`.
def Nat.firstFrom (q: Nat -> Bool): Nat -> Nat -> Nat
  | Zero,   s => s
  | Succ c, s => if q s then s else Nat.firstFrom q c (Succ s)

theorem Nat.firstFromExample: Nat.firstFrom (\k => Nat.leq 11 (k * k)) 9 1 = 4 := rfl

theorem Nat.firstFromStop (q: Nat -> Bool) (c: Nat) (s: Nat) (h: q s = True): Nat.firstFrom q (Succ c) s = s :=
  Eq.cong (\b => Bool.ifThenElse b (\u => s) (\u => Nat.firstFrom q c (Succ s))) h

theorem Nat.firstFromSkip (q: Nat -> Bool) (c: Nat) (s: Nat) (h: q s = False): Nat.firstFrom q (Succ c) s = Nat.firstFrom q c (Succ s) :=
  Eq.cong (\b => Bool.ifThenElse b (\u => s) (\u => Nat.firstFrom q c (Succ s))) h

theorem Nat.firstFromAtLeast (q: Nat -> Bool): (c: Nat) -> (s: Nat) -> s <= Nat.firstFrom q c s
  | Zero,   s => Nat.leRefl s
  | Succ c, s =>
    Bool.inspect (q s) (\u => s <= Nat.firstFrom q (Succ c) s)
      (\t => J (\z p => s <= z) (Nat.leRefl s) (Eq.sym (Nat.firstFromStop q c s t)))
      (\f => J (\z p => s <= z) (Nat.leTrans s (Succ s) (Nat.firstFrom q c (Succ s)) (Nat.leSucc s) (Nat.firstFromAtLeast q c (Succ s))) (Eq.sym (Nat.firstFromSkip q c s f)))

theorem Nat.firstFromBefore (q: Nat -> Bool): (c: Nat) -> (s: Nat) -> (j: Nat) -> s <= j -> j < Nat.firstFrom q c s -> q j = False
  | Zero,   s, j, h1, h2 => Void.exfalso (Nat.lessIrrefl j (Nat.leTrans (Succ j) s j h2 h1))
  | Succ c, s, j, h1, h2 =>
    Bool.inspect (q s) (\u => q j = False)
      (\t => Void.exfalso (Nat.lessIrrefl j (Nat.leTrans (Succ j) s j (Nat.ltCongRight j (Nat.firstFrom q (Succ c) s) s (Nat.firstFromStop q c s t) h2) h1)))
      (\f => Bool.inspect (j == s) (\u => q j = False)
        (\e => J (\z p => q z = False) f (Eq.sym (Decidable.toBoolSound (Nat.decEq j s) e)))
        (\ne => Nat.firstFromBefore q c (Succ s) j
          (Nat.leNeSucc s j h1 (\e => Bool.trueNotFalse (Eq.trans (Eq.sym (Decidable.toBoolOf (Nat.decEq j s) (Eq.sym e))) ne)))
          (Nat.ltCongRight j (Nat.firstFrom q (Succ c) s) (Nat.firstFrom q c (Succ s)) (Nat.firstFromSkip q c s f) h2)))

theorem Nat.firstFromFound (q: Nat -> Bool): (c: Nat) -> (s: Nat) -> (k: Nat) -> s <= k -> k < s + c -> q k = True -> q (Nat.firstFrom q c s) = True
  | Zero,   s, k, h1, h2, hk => Void.exfalso (Nat.lessIrrefl k (Nat.leTrans (Succ k) s k (Nat.ltCongRight k (s + 0) s (Nat.addZero s) h2) h1))
  | Succ c, s, k, h1, h2, hk =>
    Bool.inspect (q s) (\u => q (Nat.firstFrom q (Succ c) s) = True)
      (\t => J (\z p => q z = True) t (Eq.sym (Nat.firstFromStop q c s t)))
      (\f => J (\z p => q z = True)
        (Nat.firstFromFound q c (Succ s) k
          (Nat.leNeSucc s k h1 (\e => Bool.trueNotFalse (Eq.trans (Eq.sym hk) (Eq.trans (Eq.cong q (Eq.sym e)) f))))
          (Nat.ltSuccAdd s c k h2) hk)
        (Eq.sym (Nat.firstFromSkip q c s f)))

theorem Nat.firstFromLe (q: Nat -> Bool) (c: Nat) (s: Nat) (k: Nat) (h1: s <= k) (hk: q k = True): Nat.firstFrom q c s <= k :=
  match e: Nat.leq (Nat.firstFrom q c s) k with
    | True  => rfl
    | False => Void.exfalso (Bool.trueNotFalse (Eq.trans (Eq.sym hk) (Nat.firstFromBefore q c s k h1 (Nat.leqFalse (Nat.firstFrom q c s) k e))))

-- Sums that agree on the elements passing a check `all` says they all pass.
theorem List.sumByCongrAll (p: a -> Bool) (f: a -> Nat) (g: a -> Nat) (h: (x: a) -> p x = True -> f x = g x):
    (xs: List a) -> List.all p xs = True -> List.sumBy f xs = List.sumBy g xs
  | Nil,       ok => rfl
  | Cons x xs, ok =>
    Eq.trans (List.sumByCons f x xs)
      (Eq.trans (Eq.cong (\t => t + List.sumBy f xs) (h x (Bool.andLeft (p x) (List.all p xs) ok)))
        (Eq.trans (Eq.cong (\t => g x + t) (List.sumByCongrAll p f g h xs (Bool.andRight (p x) (List.all p xs) ok)))
          (Eq.sym (List.sumByCons g x xs))))

-- `True` for `Less` and `Equal`.
def Ordering.isLessEq: Ordering -> Bool
  | Less    => True
  | Equal   => True
  | Greater => False

theorem Ordering.isLessEqIf: (d: Bool) -> Ordering.isLessEq (if d then Less else Greater) = d
  | True  => rfl
  | False => rfl

-- `Nat.compare` agrees with `<=`, so `List.sortBy` with it is total.
theorem Nat.compareLeq (m: Nat) (n: Nat): Ordering.isLessEq (Nat.compare m n) = Nat.leq m n :=
  Bool.inspect (Nat.equal m n)
    (\c => Ordering.isLessEq (if c then Equal else (if Nat.leq m n then Less else Greater)) = Nat.leq m n)
    (\e => Eq.sym (Nat.leCongRight m m n (Nat.equalSound m n e) (Nat.leRefl m)))
    (\e => Ordering.isLessEqIf (Nat.leq m n))

theorem Nat.compareTotal (m: Nat) (n: Nat)
  (h: Ordering.isLessEq (Nat.compare m n) = False): Ordering.isLessEq (Nat.compare n m) = True := Eq.trans (Nat.compareLeq n m) (Nat.leqTotal m n (Eq.trans (Eq.sym (Nat.compareLeq m n)) h))

-- Merges two lists sorted by `le` ("may come before"), taking from the first
-- list on ties.
def List.merge (le: a -> a -> Bool): List a -> List a -> List a
  | Nil,       ys        => ys
  | Cons x xs, Nil       => Cons x xs
  | Cons x xs, Cons y ys =>
    if le x y then Cons x (List.merge le xs (Cons y ys)) else Cons y (List.merge le (Cons x xs) ys)

-- Bottom-up merge sort, structurally recursive throughout. The runs are kept
-- like the digits of a binary counter: slot `i` is empty or holds a sorted run
-- of 2^i elements, newest first. Adding an element carries: two runs of the
-- same size merge into the next slot. Each element takes part in about log n
-- merges, so sorting is O(n log n).
def List.pushRun (le: a -> a -> Bool) (run: List a): List (Maybe (List a)) -> List (Maybe (List a))
  | Nil                => Cons (Just run) Nil
  | Cons Nothing rest  => Cons (Just run) rest
  | Cons (Just r) rest => Cons Nothing (List.pushRun le (List.merge le r run) rest)

def List.buildRuns (le: a -> a -> Bool) (c: List (Maybe (List a))): List a -> List (Maybe (List a))
  | Nil       => c
  | Cons x xs => List.buildRuns le (List.pushRun le (Cons x Nil) c) xs

-- Merges the runs, older (earlier) ones on the left.
def List.mergeRuns (le: a -> a -> Bool) (acc: List a): List (Maybe (List a)) -> List a
  | Nil                => acc
  | Cons Nothing rest  => List.mergeRuns le acc rest
  | Cons (Just r) rest => List.mergeRuns le (List.merge le r acc) rest

-- Sorts by `le`, which says whether its first argument may come before its
-- second (`Nat.leq` for ascending numbers). Stable: equal elements keep their
-- order. `List.sortWithSorted` and `List.sortWithPerm` say it's correct.
def List.sortWith (le: a -> a -> Bool) (xs: List a): List a := List.mergeRuns le Nil (List.buildRuns le Nil xs)

-- Sorts by a comparison, such as `Nat.compare` or `Text.compare`.
def List.sortBy (cmp: a -> a -> Ordering) (xs: List a): List a := List.sortWith (\x y => Ordering.isLessEq (cmp x y)) xs

-- Sorts numbers into ascending order.
def List.sort (xs: List Nat): List Nat := List.sortWith Nat.leq xs

-- `List.LeHead le z xs`: `z` may come before the first element of `xs`, if any.
def List.LeHead (le: a -> a -> Bool) (z: a): List a -> Prop
  | Nil       => Unit
  | Cons y ys => le z y = True

-- Each element may come before the next. For a transitive `le`, such as
-- `Nat.leq`, that orders every pair.
def List.Sorted (le: a -> a -> Bool): List a -> Prop
  | Nil       => Unit
  | Cons x xs => And (List.LeHead le x xs) (List.Sorted le xs)

-- The correctness proofs need only that `le` is total: `tot` below.
theorem List.mergeLeHead (le: a -> a -> Bool) (z: a): (xs: List a) -> (ys: List a) ->
    List.LeHead le z xs -> List.LeHead le z ys -> List.LeHead le z (List.merge le xs ys)
  | Nil,       ys,        hx, hy => hy
  | Cons x xs, Nil,       hx, hy => hx
  | Cons x xs, Cons y ys, hx, hy =>
    Bool.inspect (le x y)
      (\c => List.LeHead le z (if c then Cons x (List.merge le xs (Cons y ys)) else Cons y (List.merge le (Cons x xs) ys)))
      (\e => hx) (\e => hy)

theorem List.mergeSorted (le: a -> a -> Bool) (tot: (x: a) -> (y: a) -> le x y = False -> le y x = True):
    (xs: List a) -> (ys: List a) -> List.Sorted le xs -> List.Sorted le ys -> List.Sorted le (List.merge le xs ys)
  | Nil,       ys,        sx, sy => sy
  | Cons x xs, Nil,       sx, sy => sx
  | Cons x xs, Cons y ys, Both hx sxs, Both hy sys =>
    Bool.inspect (le x y)
      (\c => List.Sorted le (if c then Cons x (List.merge le xs (Cons y ys)) else Cons y (List.merge le (Cons x xs) ys)))
      (\e => Both (List.mergeLeHead le x xs (Cons y ys) hx e) (List.mergeSorted le tot xs (Cons y ys) sxs (Both hy sys)))
      (\e => Both (List.mergeLeHead le y (Cons x xs) ys (tot x y e) hy) (List.mergeSorted le tot (Cons x xs) ys (Both hx sxs) sys))

-- Every run in the counter is sorted.
def List.RunsSorted (le: a -> a -> Bool): List (Maybe (List a)) -> Prop
  | Nil                => Unit
  | Cons Nothing rest  => List.RunsSorted le rest
  | Cons (Just r) rest => And (List.Sorted le r) (List.RunsSorted le rest)

theorem List.pushRunSorted (le: a -> a -> Bool) (tot: (x: a) -> (y: a) -> le x y = False -> le y x = True)
    (run: List a): (c: List (Maybe (List a))) -> List.Sorted le run -> List.RunsSorted le c -> List.RunsSorted le (List.pushRun le run c)
  | Nil,                s, h         => Both s Trivial
  | Cons Nothing rest,  s, h         => Both s h
  | Cons (Just r) rest, s, Both sr h =>
    List.pushRunSorted le tot (List.merge le r run) rest (List.mergeSorted le tot r run sr s) h

theorem List.buildRunsSorted (le: a -> a -> Bool) (tot: (x: a) -> (y: a) -> le x y = False -> le y x = True)
    (c: List (Maybe (List a))): (xs: List a) -> List.RunsSorted le c -> List.RunsSorted le (List.buildRuns le c xs)
  | Nil,       h => h
  | Cons x xs, h =>
    List.buildRunsSorted le tot (List.pushRun le (Cons x Nil) c) xs (List.pushRunSorted le tot (Cons x Nil) c (Both Trivial Trivial) h)

theorem List.mergeRunsSorted (le: a -> a -> Bool) (tot: (x: a) -> (y: a) -> le x y = False -> le y x = True)
    (acc: List a): (c: List (Maybe (List a))) -> List.Sorted le acc -> List.RunsSorted le c -> List.Sorted le (List.mergeRuns le acc c)
  | Nil,                s, h         => s
  | Cons Nothing rest,  s, h         => List.mergeRunsSorted le tot acc rest s h
  | Cons (Just r) rest, s, Both sr h =>
    List.mergeRunsSorted le tot (List.merge le r acc) rest (List.mergeSorted le tot r acc sr s) h

theorem List.sortWithSorted (le: a -> a -> Bool) (tot: (x: a) -> (y: a) -> le x y = False -> le y x = True)
  (xs: List a): List.Sorted le (List.sortWith le xs) :=
  List.mergeRunsSorted le tot Nil (List.buildRuns le Nil xs) Trivial (List.buildRunsSorted le tot Nil xs Trivial)

theorem List.sortBySorted (cmp: a -> a -> Ordering)
  (tot: (x: a) -> (y: a) -> Ordering.isLessEq (cmp x y) = False -> Ordering.isLessEq (cmp y x) = True)
  (xs: List a): List.Sorted (\x y => Ordering.isLessEq (cmp x y)) (List.sortBy cmp xs) := List.sortWithSorted (\x y => Ordering.isLessEq (cmp x y)) tot xs

theorem List.sortSorted (xs: List Nat): List.Sorted Nat.leq (List.sort xs) := List.sortWithSorted Nat.leq Nat.leqTotal xs

-- `List.count` is `List.occurrences`, which suits proofs; counting and
-- `List.scanLeft` over `++`. (`List.drop 1` drops the starting value.)
theorem List.countStep: (b: Bool) -> (k: Nat) -> (o: Nat) -> Nat.succIf k b + o = k + (Bool.toNat b + o)
  | True,  k, o => Eq.sym (Nat.addSucc k o)
  | False, k, o => rfl

theorem List.countFold (p: a -> Bool) (k: Nat): (xs: List a) ->
    List.foldLeft (\n x => Nat.succIf n (p x)) k xs = k + List.occurrences p xs
  | Nil       => Eq.sym (Nat.addZero k)
  | Cons x xs => Eq.trans (List.countFold p (Nat.succIf k (p x)) xs) (List.countStep (p x) k (List.occurrences p xs))

theorem List.countOccurrences (p: a -> Bool) (xs: List a): List.count p xs = List.occurrences p xs := List.countFold p 0 xs

theorem List.occurrencesAppend (p: a -> Bool): (xs: List a) -> (ys: List a) ->
    List.occurrences p (List.append xs ys) = List.occurrences p xs + List.occurrences p ys
  | Nil,       ys => rfl
  | Cons x xs, ys =>
    Eq.trans (Eq.cong (\t => Bool.toNat (p x) + t) (List.occurrencesAppend p xs ys))
      (Eq.sym (Nat.addAssoc (Bool.toNat (p x)) (List.occurrences p xs) (List.occurrences p ys)))

theorem List.scanLeftCons (f: b -> a -> b) (z: b): (xs: List a) -> List.scanLeft f z xs = Cons z (List.drop 1 (List.scanLeft f z xs))
  | Nil       => rfl
  | Cons x xs => rfl

theorem List.scanLeftAppend (f: b -> a -> b) (z: b): (xs: List a) -> (ys: List a) ->
    List.drop 1 (List.scanLeft f z (List.append xs ys)) = List.append (List.drop 1 (List.scanLeft f z xs)) (List.drop 1 (List.scanLeft f (List.foldLeft f z xs) ys))
  | Nil,       ys => rfl
  | Cons x xs, ys =>
    Eq.trans (List.scanLeftCons f (f z x) (List.append xs ys))
      (Eq.trans (Eq.cong (Cons (f z x)) (List.scanLeftAppend f (f z x) xs ys))
        (Eq.cong (\l => List.append l (List.drop 1 (List.scanLeft f (List.foldLeft f (f z x) xs) ys))) (Eq.sym (List.scanLeftCons f (f z x) xs))))

-- `xs` and `ys` are permutations of each other: every test is passed by as
-- many elements of one as of the other. For elements with decidable equality
-- this is the usual meaning (test with `Nat.equal v` for each `v`). Counting
-- turns the proofs into arithmetic, and needs no equality on the elements.
def List.Perm (xs: List a) (ys: List a): Prop := (p: a -> Bool) -> List.occurrences p xs = List.occurrences p ys

theorem List.permRefl (xs: List a): List.Perm xs xs := \p => rfl

theorem List.permSym (xs: List a) (ys: List a) (h: List.Perm xs ys): List.Perm ys xs := \p => Eq.sym (h p)

theorem List.permTrans (xs: List a) (ys: List a) (zs: List a) (h1: List.Perm xs ys) (h2: List.Perm ys zs): List.Perm xs zs := \p => Eq.trans (h1 p) (h2 p)

theorem List.occurrencesTrue: (xs: List a) -> List.occurrences (\x => True) xs = List.length xs
  | Nil       => rfl
  | Cons x xs => Eq.cong Succ (List.occurrencesTrue xs)

theorem List.permLength (xs: List a) (ys: List a) (h: List.Perm xs ys): List.length xs = List.length ys := Eq.trans (Eq.sym (List.occurrencesTrue xs)) (Eq.trans (h (\x => True)) (List.occurrencesTrue ys))

-- Some element passes `p` exactly when at least one does, so permutations
-- agree on `any`.
theorem List.anyOccurrences (p: a -> Bool): (xs: List a) -> List.any p xs = Nat.leq 1 (List.occurrences p xs)
  | Nil       => rfl
  | Cons x xs =>
    Bool.inspect (p x) (\c => Bool.ifThenElse c (\u => True) (\u => List.any p xs) = Nat.leq 1 (Bool.toNat c + List.occurrences p xs))
      (\t => rfl) (\f => List.anyOccurrences p xs)

theorem List.anyPerm (p: a -> Bool) (xs: List a) (ys: List a) (h: List.Perm xs ys): List.any p xs = List.any p ys :=
  Eq.trans (List.anyOccurrences p xs) (Eq.trans (Eq.cong (\n => Nat.leq 1 n) (h p)) (Eq.sym (List.anyOccurrences p ys)))

-- Reversing is a permutation, and keeps sums.
theorem List.occurrencesReverseOnto (p: a -> Bool): (xs: List a) -> (acc: List a) ->
    List.occurrences p (List.reverseOnto xs acc) = List.occurrences p xs + List.occurrences p acc
  | Nil,       acc => rfl
  | Cons x xs, acc =>
    Eq.trans (List.occurrencesReverseOnto p xs (Cons x acc))
      (Eq.trans (Nat.addLeftComm (List.occurrences p xs) (Bool.toNat (p x)) (List.occurrences p acc))
        (Eq.sym (Nat.addAssoc (Bool.toNat (p x)) (List.occurrences p xs) (List.occurrences p acc))))

theorem List.reversePerm (xs: List a): List.Perm (List.reverse xs) xs := \p =>
  Eq.trans (List.occurrencesReverseOnto p xs Nil) (Nat.addZero (List.occurrences p xs))

theorem List.sumByReverseOnto (f: a -> Nat): (xs: List a) -> (acc: List a) ->
    List.sumBy f (List.reverseOnto xs acc) = List.sumBy f xs + List.sumBy f acc
  | Nil,       acc => rfl
  | Cons x xs, acc =>
    Eq.trans (List.sumByReverseOnto f xs (Cons x acc))
      (Eq.trans (Eq.cong (\t => List.sumBy f xs + t) (List.sumByCons f x acc))
        (Eq.trans (Nat.addLeftComm (List.sumBy f xs) (f x) (List.sumBy f acc))
          (Eq.trans (Eq.sym (Nat.addAssoc (f x) (List.sumBy f xs) (List.sumBy f acc)))
            (Eq.cong (\t => t + List.sumBy f acc) (Eq.sym (List.sumByCons f x xs))))))

theorem List.sumByReverse (f: a -> Nat) (xs: List a): List.sumBy f (List.reverse xs) = List.sumBy f xs :=
  Eq.trans (List.sumByReverseOnto f xs Nil) (Nat.addZero (List.sumBy f xs))

-- Counting with tests that agree, with a test nothing passes, and with
-- either of two tests.
theorem List.occurrencesCongr (p: a -> Bool) (q: a -> Bool) (h: (x: a) -> p x = q x): (xs: List a) ->
    List.occurrences p xs = List.occurrences q xs
  | Nil       => rfl
  | Cons x xs =>
    Eq.trans (Eq.cong (\b => Bool.toNat b + List.occurrences p xs) (h x))
      (Eq.cong (\n => Bool.toNat (q x) + n) (List.occurrencesCongr p q h xs))

theorem List.occurrencesNone (p: a -> Bool) (h: (x: a) -> p x = False): (xs: List a) -> List.occurrences p xs = 0
  | Nil       => rfl
  | Cons x xs => Eq.trans (Eq.cong (\b => Bool.toNat b + List.occurrences p xs) (h x)) (List.occurrencesNone p h xs)

-- When nothing passes both `p` and `q`, the elements passing either are those
-- passing `p` plus those passing `q`.
theorem List.occurrencesOr (p: a -> Bool) (q: a -> Bool) (h: (x: a) -> p x = True -> q x = False): (xs: List a) ->
    List.occurrences (\x => p x || q x) xs = List.occurrences p xs + List.occurrences q xs
  | Nil       => rfl
  | Cons x xs =>
    Bool.inspect (p x)
      (\c => Bool.toNat (c || q x) + List.occurrences (\x => p x || q x) xs
        = (Bool.toNat c + List.occurrences p xs) + (Bool.toNat (q x) + List.occurrences q xs))
      (\t => Eq.trans (Eq.cong (\n => 1 + n) (List.occurrencesOr p q h xs))
        (Eq.cong (\b => (1 + List.occurrences p xs) + (Bool.toNat b + List.occurrences q xs)) (Eq.sym (h x t))))
      (\f => Eq.trans (Eq.cong (\n => Bool.toNat (q x) + n) (List.occurrencesOr p q h xs))
        (Nat.addLeftComm (Bool.toNat (q x)) (List.occurrences p xs) (List.occurrences q xs)))

-- Adding an element in front keeps every subsequence.
theorem List.subsequenceCons (x: a): (s: List a) -> (ys: List a) -> List.Subsequence s ys -> List.Subsequence s (Cons x ys)
  | Nil,      ys, h => Trivial
  | Cons y s, ys, h => Inr h

theorem List.subsequenceRefl: (xs: List a) -> List.Subsequence xs xs
  | Nil       => Trivial
  | Cons x xs => Inl (Both rfl (List.subsequenceRefl xs))

theorem List.subsequenceLength: (s: List a) -> (ys: List a) -> List.Subsequence s ys -> List.length s <= List.length ys
  | Nil,       ys,        h              => rfl
  | Cons x xs, Nil,       h              => Void.exfalso h
  | Cons x xs, Cons y ys, Inl (Both e h) => List.subsequenceLength xs ys h
  | Cons x xs, Cons y ys, Inr h          =>
    Nat.leTrans (List.length (Cons x xs)) (List.length ys) (Succ (List.length ys)) (List.subsequenceLength (Cons x xs) ys h) (Nat.leSucc (List.length ys))

theorem List.mergeCount (le: a -> a -> Bool) (p: a -> Bool): (xs: List a) -> (ys: List a) ->
    List.occurrences p (List.merge le xs ys) = List.occurrences p xs + List.occurrences p ys
  | Nil,       ys        => rfl
  | Cons x xs, Nil       => Eq.sym (Nat.addZero (List.occurrences p (Cons x xs)))
  | Cons x xs, Cons y ys =>
    Bool.inspect (le x y)
      (\c => List.occurrences p (if c then Cons x (List.merge le xs (Cons y ys)) else Cons y (List.merge le (Cons x xs) ys))
        = List.occurrences p (Cons x xs) + List.occurrences p (Cons y ys))
      (\e => Eq.trans (Eq.cong (\t => Bool.toNat (p x) + t) (List.mergeCount le p xs (Cons y ys)))
        (Eq.sym (Nat.addAssoc (Bool.toNat (p x)) (List.occurrences p xs) (List.occurrences p (Cons y ys)))))
      (\e => Eq.trans (Eq.cong (\t => Bool.toNat (p y) + t) (List.mergeCount le p (Cons x xs) ys))
        (Nat.addLeftComm (Bool.toNat (p y)) (List.occurrences p (Cons x xs)) (List.occurrences p ys)))

-- How many elements of all the runs satisfy `p`.
def List.runsCount (p: a -> Bool): List (Maybe (List a)) -> Nat
  | Nil                => 0
  | Cons Nothing rest  => List.runsCount p rest
  | Cons (Just r) rest => List.occurrences p r + List.runsCount p rest

theorem List.pushRunCount (le: a -> a -> Bool) (p: a -> Bool) (run: List a): (c: List (Maybe (List a))) ->
    List.runsCount p (List.pushRun le run c) = List.occurrences p run + List.runsCount p c
  | Nil                => rfl
  | Cons Nothing rest  => rfl
  | Cons (Just r) rest =>
    Eq.trans (List.pushRunCount le p (List.merge le r run) rest)
      (Eq.trans (Eq.cong (\t => t + List.runsCount p rest) (List.mergeCount le p r run))
        (Nat.addRotate (List.occurrences p r) (List.occurrences p run) (List.runsCount p rest)))

theorem List.buildRunsCount (le: a -> a -> Bool) (p: a -> Bool) (c: List (Maybe (List a))): (xs: List a) ->
    List.runsCount p (List.buildRuns le c xs) = List.runsCount p c + List.occurrences p xs
  | Nil       => Eq.sym (Nat.addZero (List.runsCount p c))
  | Cons x xs =>
    Eq.trans (List.buildRunsCount le p (List.pushRun le (Cons x Nil) c) xs)
      (Eq.trans (Eq.cong (\t => t + List.occurrences p xs) (List.pushRunCount le p (Cons x Nil) c))
        (Eq.trans (Eq.cong (\t => (t + List.runsCount p c) + List.occurrences p xs) (Nat.addZero (Bool.toNat (p x))))
          (Nat.addRotate (Bool.toNat (p x)) (List.runsCount p c) (List.occurrences p xs))))

theorem List.mergeRunsCount (le: a -> a -> Bool) (p: a -> Bool) (acc: List a): (c: List (Maybe (List a))) ->
    List.occurrences p (List.mergeRuns le acc c) = List.occurrences p acc + List.runsCount p c
  | Nil                => Eq.sym (Nat.addZero (List.occurrences p acc))
  | Cons Nothing rest  => List.mergeRunsCount le p acc rest
  | Cons (Just r) rest =>
    Eq.trans (List.mergeRunsCount le p (List.merge le r acc) rest)
      (Eq.trans (Eq.cong (\t => t + List.runsCount p rest) (List.mergeCount le p r acc))
        (Nat.addRotate (List.occurrences p r) (List.occurrences p acc) (List.runsCount p rest)))

theorem List.sortWithPerm (le: a -> a -> Bool) (xs: List a): List.Perm (List.sortWith le xs) xs := \p =>
  Eq.trans (List.mergeRunsCount le p Nil (List.buildRuns le Nil xs)) (List.buildRunsCount le p Nil xs)

theorem List.sortByPerm (cmp: a -> a -> Ordering) (xs: List a): List.Perm (List.sortBy cmp xs) xs := List.sortWithPerm (\x y => Ordering.isLessEq (cmp x y)) xs

theorem List.sortPerm (xs: List Nat): List.Perm (List.sort xs) xs := List.sortWithPerm Nat.leq xs

theorem List.sortLength (xs: List Nat): List.length (List.sort xs) = List.length xs := List.permLength (List.sort xs) xs (List.sortPerm xs)
