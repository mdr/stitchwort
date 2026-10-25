-- Lemmas about positions in lists, and ranges of numbers, that need
-- `omega` or `DecEq`: where `List.indexOf` finds an element, running sums by
-- position, sorted lists of numbers by position, and `List.all` over
-- `List.between`. Kept out of Index.sw and Sort.sw, which small programs
-- load, so that those don't load Omega.

-- The element at `x`'s position is `x`.
theorem List.getOrIndexOf [auto eq: DecEq a]: (xs: List a) → (d: a) → (x: a) → List.Mem x xs → List.getOr xs d (List.indexOf xs x) = x
  | Nil, d, x, m => Void.exfalso m
  | Cons y ys, d, x, m =>
    match e: y == x with
      | True => DecEq.sound y x e
      | False =>
        match m with
          | Inl q => Void.exfalso (DecEq.soundFalse y x e q)
          | Inr rest => List.getOrIndexOf ys d x rest

-- An element's position is inside the list.
theorem List.indexOfLt [auto eq: DecEq a]: (xs: List a) → (x: a) → List.Mem x xs → List.indexOf xs x < List.length xs
  | Nil, x, m => Void.exfalso m
  | Cons y ys, x, m =>
    match e: y == x with
      | True => rfl
      | False =>
        match m with
          | Inl q => Void.exfalso (DecEq.soundFalse y x e q)
          | Inr rest => List.indexOfLt ys x rest

-- Running sums from `start`: entry c is `start` plus the first c elements.
theorem List.getOrScanAdd: (row: List Nat) → (start: Nat) → (c: Nat) → c ≤ List.length row →
    List.getOr (List.scanLeft row start Nat.add) 0 c = start + List.sumBy (List.range c) (i => List.getOr row 0 i)
  | Nil, start, Zero, h => Eq.sym (Nat.addZero start)
  | Nil, start, Succ c, h => Void.exfalso (Bool.falseNotTrue h)
  | Cons x xs, start, Zero, h => Eq.sym (Nat.addZero start)
  | Cons x xs, start, Succ c, h =>
    rewrite List.getOrScanAdd xs (Nat.add start x) c h, List.sumByRangeSucc (i => List.getOr (Cons x xs) 0 i) c in omega

-- In a sorted list of numbers, an element is at most every later one.
theorem List.sortedGetOrLe: (xs: List Nat) → (d: Nat) → List.Sorted Nat.leq xs → (i: Nat) → (j: Nat) → i ≤ j → j < List.length xs →
    List.getOr xs d i ≤ List.getOr xs d j
  | Nil, d, s, i, j, h, lt => Void.exfalso (Bool.falseNotTrue lt)
  | Cons x rest, d, s, Zero, Zero, h, lt => Nat.leRefl x
  | Cons x Nil, d, s, Zero, Succ j, h, lt => Void.exfalso (Bool.falseNotTrue lt)
  | Cons x (Cons y ys), d, Both first s, Zero, Succ j, h, lt =>
    Nat.leTrans x y (List.getOr (Cons y ys) d j) first (List.sortedGetOrLe (Cons y ys) d s 0 j rfl lt)
  | Cons x rest, d, s, Succ i, Zero, h, lt => Void.exfalso (Bool.falseNotTrue h)
  | Cons x rest, d, Both first s, Succ i, Succ j, h, lt => List.sortedGetOrLe rest d s i j h lt

-- A value of a sorted list that lies between the elements at positions i and
-- j (i <= j) is the element at a position from i to j: so anything true of
-- those elements is true of it.
theorem List.sortedBetween (d: Nat) (p: Nat → Prop) (xs: List Nat) (s: List.Sorted Nat.leq xs) (i: Nat) (j: Nat) (ij: i ≤ j) (jIn: j < List.length xs)
    (each: (k: Nat) → i ≤ k → k ≤ j → p (List.getOr xs d k))
    (v: Nat) (m: List.Mem v xs) (above: List.getOr xs d i ≤ v) (below: v ≤ List.getOr xs d j): p v :=
  let k := List.indexOf xs v
  let at: List.getOr xs d k = v := List.getOrIndexOf xs d v m
  let kIn: k < List.length xs := List.indexOfLt xs v m
  match ki: Nat.leq i k with
    | True =>
      match kj: Nat.leq k j with
        | True => rewrite <- at in each k ki kj
        -- Past j: the element at j is at most v and at least it, so v is it.
        | False =>
          let up := List.sortedGetOrLe xs d s j k (omega) kIn
          rewrite (omega [up, at, below]: v = List.getOr xs d j) in each j ij (Nat.leRefl j)
    -- Before i: the same, at i.
    | False =>
      let down := List.sortedGetOrLe xs d s k i (omega) (omega)
      rewrite (omega [down, at, above]: v = List.getOr xs d i) in each i (Nat.leRefl i) ij

theorem List.allBetweenElim (q: Nat → Bool) (lo: Nat) (hi: Nat) (h: List.all (List.between lo hi) q = True) (k: Nat) (lk: lo ≤ k) (kh: k ≤ hi): q k = True :=
  List.allRangeElim q (hi + 1 - lo) lo h k lk (omega)

theorem List.allBetweenIntro (q: Nat → Bool) (lo: Nat) (hi: Nat) (h: (k: Nat) → lo ≤ k → k ≤ hi → q k = True): List.all (List.between lo hi) q = True :=
  List.allRangeIntro q (hi + 1 - lo) lo (k lk kh => h k lk (omega))
