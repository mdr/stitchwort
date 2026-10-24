-- Lemmas about positions in lists, and ranges of numbers, that need
-- `omega` or `DecEq`: where `List.indexOf` finds an element, running sums by
-- position, sorted lists of numbers by position, and `List.all` over
-- `List.between`. Kept out of Index.sw and Sort.sw, which small programs
-- load, so that those don't load Omega.

-- The element at `x`'s position is `x`.
theorem List.getOrIndexOf [auto eq: DecEq a] (d: a) (x: a): (xs: List a) -> List.Mem x xs -> List.getOr d (List.indexOf x xs) xs = x
  | Nil, m => Void.exfalso m
  | Cons y ys, m =>
    match e: y == x with
      | True => DecEq.sound y x e
      | False =>
        match m with
          | Inl q => Void.exfalso (DecEq.soundFalse y x e q)
          | Inr rest => List.getOrIndexOf d x ys rest

-- An element's position is inside the list.
theorem List.indexOfLt [auto eq: DecEq a] (x: a): (xs: List a) -> List.Mem x xs -> List.indexOf x xs < List.length xs
  | Nil, m => Void.exfalso m
  | Cons y ys, m =>
    match e: y == x with
      | True => rfl
      | False =>
        match m with
          | Inl q => Void.exfalso (DecEq.soundFalse y x e q)
          | Inr rest => List.indexOfLt x ys rest

-- Running sums from `start`: entry c is `start` plus the first c elements.
theorem List.getOrScanAdd: (start: Nat) -> (row: List Nat) -> (c: Nat) -> c <= List.length row ->
    List.getOr 0 c (List.scanLeft Nat.add start row) = start + List.sumBy (i => List.getOr 0 i row) (List.range c)
  | start, Nil, Zero, h => Eq.sym (Nat.addZero start)
  | start, Nil, Succ c, h => Void.exfalso (Bool.falseNotTrue h)
  | start, Cons x xs, Zero, h => Eq.sym (Nat.addZero start)
  | start, Cons x xs, Succ c, h =>
    rewrite List.getOrScanAdd (Nat.add start x) xs c h, List.sumByRangeSucc (i => List.getOr 0 i (Cons x xs)) c in omega

-- In a sorted list of numbers, an element is at most every later one.
theorem List.sortedGetOrLe (d: Nat): (xs: List Nat) -> List.Sorted Nat.leq xs -> (i: Nat) -> (j: Nat) -> i <= j -> j < List.length xs ->
    List.getOr d i xs <= List.getOr d j xs
  | Nil, s, i, j, h, lt => Void.exfalso (Bool.falseNotTrue lt)
  | Cons x rest, s, Zero, Zero, h, lt => Nat.leRefl x
  | Cons x Nil, s, Zero, Succ j, h, lt => Void.exfalso (Bool.falseNotTrue lt)
  | Cons x (Cons y ys), Both first s, Zero, Succ j, h, lt =>
    Nat.leTrans x y (List.getOr d j (Cons y ys)) first (List.sortedGetOrLe d (Cons y ys) s 0 j rfl lt)
  | Cons x rest, s, Succ i, Zero, h, lt => Void.exfalso (Bool.falseNotTrue h)
  | Cons x rest, Both first s, Succ i, Succ j, h, lt => List.sortedGetOrLe d rest s i j h lt

-- A value of a sorted list that lies between the elements at positions i and
-- j (i <= j) is the element at a position from i to j: so anything true of
-- those elements is true of it.
theorem List.sortedBetween (d: Nat) (p: Nat -> Prop) (xs: List Nat) (s: List.Sorted Nat.leq xs) (i: Nat) (j: Nat) (ij: i <= j) (jIn: j < List.length xs)
    (each: (k: Nat) -> i <= k -> k <= j -> p (List.getOr d k xs))
    (v: Nat) (m: List.Mem v xs) (above: List.getOr d i xs <= v) (below: v <= List.getOr d j xs): p v :=
  let k := List.indexOf v xs
  let at: List.getOr d k xs = v := List.getOrIndexOf d v xs m
  let kIn: k < List.length xs := List.indexOfLt v xs m
  match ki: Nat.leq i k with
    | True =>
      match kj: Nat.leq k j with
        | True => rewrite <- at in each k ki kj
        -- Past j: the element at j is at most v and at least it, so v is it.
        | False =>
          let up := List.sortedGetOrLe d xs s j k (omega) kIn
          rewrite (omega [up, at, below]: v = List.getOr d j xs) in each j ij (Nat.leRefl j)
    -- Before i: the same, at i.
    | False =>
      let down := List.sortedGetOrLe d xs s k i (omega) (omega)
      rewrite (omega [down, at, above]: v = List.getOr d i xs) in each i (Nat.leRefl i) ij

theorem List.allBetweenElim (q: Nat -> Bool) (lo: Nat) (hi: Nat) (h: List.all q (List.between lo hi) = True) (k: Nat) (lk: lo <= k) (kh: k <= hi): q k = True :=
  List.allRangeElim q (hi + 1 - lo) lo h k lk (omega)

theorem List.allBetweenIntro (q: Nat -> Bool) (lo: Nat) (hi: Nat) (h: (k: Nat) -> lo <= k -> k <= hi -> q k = True): List.all q (List.between lo hi) = True :=
  List.allRangeIntro q (hi + 1 - lo) lo (k lk kh => h k lk (omega))
