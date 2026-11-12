--| Lemmas about positions in lists, and ranges of numbers, that need
--| `omega` or `DecEq`: where `List.indexOf` finds an element (and
--| `List.contains` by it), folds of `Nat.max` and `Nat.min`, counting a
--| number in a range, running sums by position, sorted lists of numbers by
--| position, and `List.all` over a range that includes its end.
-- Kept out of Index.sw and Sort.sw, which small programs load, so that those
-- don't load Omega.

--| The element at `x`'s position is `x`.
theorem List.getOrIndexOf [auto eq: DecEq a] (xs: List a) (d x: a) (m: List.Mem x xs): List.getOr xs (List.indexOf xs x) d = x :=
  match xs with
    | [y, ..ys] =>
      match e: y == x with
        | True => DecEq.sound e
        | False =>
          match m with
            | Inl q => Void.exfalso (DecEq.soundFalse y x e q)
            | Inr rest => List.getOrIndexOf ys d x rest

--| An element's position is inside the list.
theorem List.indexOfLt [auto eq: DecEq a] (xs: List a) (x: a) (m: List.Mem x xs): List.indexOf xs x < List.length xs :=
  match xs with
    | [y, ..ys] =>
      match e: y == x with
        | True => rfl
        | False =>
          match m with
            | Inl q => Void.exfalso (DecEq.soundFalse y x e q)
            | Inr rest => List.indexOfLt ys x rest

--| `x` is in `xs` exactly when its first place is inside it.
theorem List.containsIndexOf [auto eq: DecEq a] (x: a) (xs: List a): List.contains xs x = (List.indexOf xs x < List.length xs) :=
  match xs with
    | [] => rfl
    | [y, ..rest] =>
      match e: y == x with
        | True => rfl
        | False => List.containsIndexOf x rest

--| `x` is in `xs` exactly when its first place in `xs` followed by more is inside `xs`.
theorem List.containsIndexOfAppend [auto eq: DecEq a] (x: a) (more: List a) (xs: List a):
    List.contains xs x = (List.indexOf (List.append xs more) x < List.length xs) :=
  match xs with
    | [] => rfl
    | [y, ..rest] =>
      match e: y == x with
        | True => rfl
        | False => List.containsIndexOfAppend x more rest

--| A fold of `Nat.max` is below `k` exactly when its start and every `f x` are.
theorem List.foldMaxLt (f: a → Nat) (k: Nat) (xs: List a) (start: Nat):
    ((List.foldLeft xs start (m x => Nat.max m (f x)) < k): Bool) = (start < k ∧ List.all xs (x => f x < k)) :=
  match xs with
    | [] => cases
    | [x, ..rest] => rewrite List.foldMaxLt f k rest (Nat.max start (f x)) in cases

--| A fold of `Nat.min` is below `k` exactly when its start or some `f x` is.
theorem List.foldMinLt (f: a → Nat) (k: Nat) (xs: List a) (start: Nat):
    ((List.foldLeft xs start (m x => Nat.min m (f x)) < k): Bool) = (start < k ∨ List.any xs (x => f x < k)) :=
  match xs with
    | [] => cases
    | [x, ..rest] => rewrite List.foldMinLt f k rest (Nat.min start (f x)) in cases

--| A run of numbers has `k` once if `k` is in it, and not at all otherwise.
theorem List.countRangeFromEq (k: Nat) (c s: Nat): List.count (List.rangeFrom c s) (== k) = Bool.toNat (s ≤ k < s + c) :=
  match c with
    | Zero => cases
    | Succ c => rewrite List.countCons (List.rangeFrom c (Succ s)) s (== k), List.countRangeFromEq k c (Succ s) in cases

--| `List.range 0 n` has `k` once if `k < n`, and not at all otherwise.
theorem List.countRangeEq (n: Nat) (k: Nat): List.count (List.range 0 n) (== k) = Bool.toNat (k < n) :=
  rewrite List.countRangeFromEq k n 0 in cases

--| Running sums from `start`: entry c is `start` plus the first c elements.
theorem List.getOrScanAdd (row: List Nat) (start c: Nat) (h: c ≤ List.length row):
    List.getOr (List.scanLeft row start Nat.add) c 0 = start + List.sumBy (List.range 0 c) (i => List.getOr row i 0) :=
  match row, c with
    | [], Zero => Eq.sym (Nat.addZero start)
    | [x, ..xs], Zero => Eq.sym (Nat.addZero start)
    | [x, ..xs], Succ c =>
      rewrite List.getOrScanAdd xs (Nat.add start x) c h, List.sumByRangeSucc (i => List.getOr [x, ..xs] i 0) c in omega

--| In a sorted list of numbers, an element is at most every later one.
theorem List.sortedGetOrLe: ∀ (xs: List Nat) (d: Nat) => List.Sorted Nat.leq xs → ∀ (i j: Nat) => i ≤ j → j < List.length xs →
    List.getOr xs i d ≤ List.getOr xs j d
  | [], d, s, i, j, h, lt => cases
  | [x, ..rest], d, s, Zero, Zero, h, lt => Nat.leRefl x
  | [x], d, s, Zero, Succ j, h, lt => cases
  | [x, y, ..ys], d, Both first s, Zero, Succ j, h, lt =>
    Nat.leTrans x y (List.getOr [y, ..ys] j d) first (List.sortedGetOrLe [y, ..ys] d s 0 j rfl lt)
  | [x, ..rest], d, s, Succ i, Zero, h, lt => cases
  | [x, ..rest], d, Both first s, Succ i, Succ j, h, lt => List.sortedGetOrLe rest d s i j h lt

--| A value of a sorted list between the elements at positions i and j is one
--| of the elements from i to j. So anything true of those elements is true
--| of it.
theorem List.sortedBetween (d: Nat) (p: Nat → Prop) (xs: List Nat) (s: List.Sorted Nat.leq xs) (i: Nat) (j: Nat) (ij: i ≤ j) (jIn: j < List.length xs)
    (each: ∀ (k: Nat) => i ≤ k → k ≤ j → p (List.getOr xs k d))
    (v: Nat) (m: List.Mem v xs) (above: List.getOr xs i d ≤ v) (below: v ≤ List.getOr xs j d): p v :=
  let k := List.indexOf xs v
  let at: List.getOr xs k d = v := List.getOrIndexOf xs d v m
  let kIn: k < List.length xs := List.indexOfLt xs v m
  match ki: Nat.leq i k with
    | True =>
      match kj: Nat.leq k j with
        | True => rewrite <- at in each k ki kj
        -- Past j: the element at j is at most v and at least it, so v is it.
        | False =>
          let up := List.sortedGetOrLe xs d s j k (omega) kIn
          rewrite (omega [up, at, below]: v = List.getOr xs j d) in each j ij (Nat.leRefl j)
    -- Before i: the same, at i.
    | False =>
      let down := List.sortedGetOrLe xs d s k i (omega) (omega)
      rewrite (omega [down, at, above]: v = List.getOr xs i d) in each i (Nat.leRefl i) ij

theorem List.allBetweenElim [q: Nat → Bool] [lo: Nat] [hi: Nat] (h: List.all (List.range lo (hi + 1)) q = True) [k: Nat] (lk: lo ≤ k) (kh: k ≤ hi): q k = True :=
  List.allRangeElim q (hi + 1 - lo) lo h k lk (omega)

theorem List.allBetweenIntro [q: Nat → Bool] [lo: Nat] [hi: Nat] (h: ∀ (k: Nat) => lo ≤ k → k ≤ hi → q k = True): List.all (List.range lo (hi + 1)) q = True :=
  List.allRangeIntro q (hi + 1 - lo) lo (k lk kh => h k lk (omega))
