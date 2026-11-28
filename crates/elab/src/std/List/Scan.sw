--| `List.scanLeft`, the running accumulations of a fold, and its lemmas: its length, `get` and
--| `getOr`, and `zipWith` and `mapAccumLeft` beside the elements.
-- Its own file, not part of List/Toolkit.sw, because the result is a
-- `NonEmptyList` and NonEmptyList/NonEmptyList.sw needs the sorting lemmas,
-- which need the toolkit, and the lemmas about `get` and `zipWith` that
-- mention it follow it here rather than in Index.sw and Zip.sw, which that
-- file needs.

--| Running accumulations, the initial value first (Haskell's `scanLeft`):
--| `List.scanLeft [x, y] initial f` is `[initial, f initial x, f (f initial x) y]`. It is a
--| `NonEmptyList`, one longer than the input ([`List.lengthScanLeft`]), so `.last`, `.maximum`
--| and `.minimum` of a scan are values, and `.tail` is the accumulations after the initial value.
def List.scanLeft: (xs: List a) → (initial: b) → (f: b → a → b) → NonEmptyList b
  | [], initial, f => { head = initial, tail = [] }
  | [x, ..xs], initial, f => { head = initial, tail = (List.scanLeft xs (f initial x) f).toList }

theorem List.scanLeftCons ∀ (xs: List a) (z: b) (f: b → a → b):
    (List.scanLeft xs z f).toList = [z, ..(List.scanLeft xs z f).tail] :=
  match xs with | [] | [_, .._] => byComputing

theorem List.scanLeftAppend ∀ (xs: List a) (z: b) (ys: List a) (f: b → a → b):
    (List.scanLeft (List.append xs ys) z f).tail
      = List.append (List.scanLeft xs z f).tail (List.scanLeft ys (List.foldLeft xs z f) f).tail :=
  match xs with
    | [] => byComputing
    | [x, ..xs] =>
      calc (List.scanLeft (List.append [x, ..xs] ys) z f).tail
        _ = (List.scanLeft (List.append xs ys) (f z x) f).toList := byComputing
        _ = [f z x, ..(List.scanLeft (List.append xs ys) (f z x) f).tail] :=
          List.scanLeftCons (List.append xs ys) (f z x) f
        _ = [
            f z x,
            ..List.append (List.scanLeft xs (f z x) f).tail (List.scanLeft ys (List.foldLeft xs (f z x) f) f).tail
          ] := Eq.cong (Cons (f z x)) (List.scanLeftAppend xs (f z x) ys f)
        _ = List.append (List.scanLeft xs (f z x) f).toList (List.scanLeft ys (List.foldLeft xs (f z x) f) f).tail :=
          Eq.cong
            (l => List.append l (List.scanLeft ys (List.foldLeft xs (f z x) f) f).tail)
            (Eq.flipped (List.scanLeftCons xs (f z x) f))
        _ = List.append (List.scanLeft [x, ..xs] z f).tail (List.scanLeft ys (List.foldLeft [x, ..xs] z f) f).tail :=
          byComputing

--| Running results: one more than the elements, the start first.
theorem List.lengthScanLeft ∀ (xs: List a) (start: b) (f: b → a → b):
    (List.scanLeft xs start f).length = Succ (List.length xs) :=
  match xs with
    | [] => byComputing
    | [x, ..xs] => Eq.cong Succ (List.lengthScanLeft xs (f start x) f)

theorem List.scanLeftNil: (List.scanLeft [] 5 (acc x => acc + x)).toList = [5] := byComputing

theorem List.scanLeftSums: (List.scanLeft [1, 2, 3] 0 (acc x => acc + x)).toList = [0, 1, 3, 6] := byComputing

--| The first step, for induction, of running accumulations beside the elements, by computation.
--| `List.zipWith xs (List.scanLeft xs z f) g` is `g` of each element and the fold of the
--| elements before it ([`List.getOrZipWithScanLeft`]). It
--| lays items end to end from `z`, say, with `f` adding an item's size and
--| `g` placing it.
theorem List.zipWithScanLeftCons ∀ (x: a) (xs: List a) (z: b) (f: b → a → b) (g: a → b → c):
    List.zipWith [x, ..xs] (List.scanLeft [x, ..xs] z f).toList g
      = [g x z, ..List.zipWith xs (List.scanLeft xs (f z x) f).toList g] :=
  byComputing

theorem List.zipWithScanLeftExample: List.zipWith
      [2, 3, 4]
      (List.scanLeft [2, 3, 4] 10 (offset width => offset + width)).toList
      (width offset => (offset, width))
      = [(10, 2), (12, 3), (15, 4)] :=
  byComputing

--| Running accumulations beside the elements have one for each element.
theorem List.lengthZipWithScanLeft ∀ (f: b → a → b) (g: a → b → c) (xs: List a) (z: b):
    List.length (List.zipWith xs (List.scanLeft xs z f).toList g) = List.length xs :=
  match xs with
    | [] => byComputing
    | [x, ..xs] => Eq.cong Succ (List.lengthZipWithScanLeft f g xs (f z x))

theorem List.mapZipWithScanLeft ∀ (h: c → d) (k: a → d) (g: a → b → c)
    (same: ∀ (x: a) (y: b) => h (g x y) = k x)
    (xs: List a) (z: b) (f: b → a → b):
    List.map (List.zipWith xs (List.scanLeft xs z f).toList g) h = List.map xs k :=
  List.mapZipWithLeft h k g same xs
    (List.scanLeft xs z f).toList
    (rewrite NonEmptyList.lengthToList (List.scanLeft xs z f), List.lengthScanLeft xs z f then
      Nat.leSucc (List.length xs))

--| Entry k of the running accumulations is the fold of the first k elements.
theorem List.getOrScanLeft ∀ (f: b → a → b) (d: b) (xs: List a) (z: b) (k: Nat)
    (h: k ≤ List.length xs):
    List.getOr (List.scanLeft xs z f).toList k d = List.foldLeft (List.take xs k) z f :=
  match xs, k with
    | [] | [_, .._], Zero => byComputing
    | [x, ..xs], Succ k => List.getOrScanLeft f d xs (f z x) k h

--| Element k of `zipWith xs (scanLeft xs z f) g` is `g` of element k and the
--| fold of the elements before it. Laying items end to end from `z`, item k
--| is placed after the first k.
theorem List.getOrZipWithScanLeft ∀ (f: b → a → b) (g: a → b → c) (dx: a) (dc: c) (xs: List a) (z: b) (k: Nat)
    (h: k < List.length xs):
    List.getOr (List.zipWith xs (List.scanLeft xs z f).toList g) k dc
      = g (List.getOr xs k dx) (List.foldLeft (List.take xs k) z f) :=
  match xs, k with
    | [x, ..xs], Zero => byComputing
    | [x, ..xs], Succ k => List.getOrZipWithScanLeft f g dx dc xs (f z x) k h

theorem List.getOrZipWithScanLeftExample: List.getOr
      (List.zipWith [2, 3, 4] (List.scanLeft [2, 3, 4] 10 (offset width => offset + width)).toList (width offset =>
        (offset, width)))
      2
      (0, 0)
      = (List.foldLeft [2, 3] 10 (offset width => offset + width), 4) :=
  List.getOrZipWithScanLeft
    (offset width => offset + width)
    (width offset => (offset, width))
    0
    (0, 0)
    [2, 3, 4]
    10
    2
    byComputing

--| Running sums from `start`: entry c is `start` plus the first c elements.
theorem List.getOrScanAdd ∀ (row: List Nat) (start c: Nat)
    (h: c ≤ List.length row):
    List.getOr (List.scanLeft row start Nat.add).toList c 0
      = start + List.sumBy (List.range 0 c) (i => List.getOr row i 0) :=
  match row, c with
    | [] | [_, .._], Zero => (Nat.addZero start).flipped
    | [x, ..xs], Succ c =>
      rewrite List.getOrScanAdd xs (Nat.add start x) c h, List.sumByRangeSucc (i => List.getOr [x, ..xs] i 0) c then
        arithmetic

--| `mapAccumLeft` is a fold for its final state, and for its list the zip of
--| the elements with the running states.
theorem List.mapAccumLeftGoSpec ∀ (f: s → a → Pair s b) (xs: List a) (state: s) (done: List b):
    List.mapAccumLeftGo f state done xs
      = MkPair
        (List.foldLeft xs state (st x => Pair.fst (f st x)))
        (List.reverseOnto done
          (List.zipWith xs (List.scanLeft xs state (st x => Pair.fst (f st x))).toList (x st => Pair.snd (f st x)))) :=
  match xs with
    | [] => byComputing
    | [x, ..xs] => List.mapAccumLeftGoSpec f xs (Pair.fst (f state x)) [Pair.snd (f state x), ..done]

theorem List.mapAccumLeftState ∀ (xs: List a) (initial: s) (f: s → a → Pair s b):
    Pair.fst (List.mapAccumLeft xs initial f) = List.foldLeft xs initial (st x => Pair.fst (f st x)) :=
  Eq.cong Pair.fst (List.mapAccumLeftGoSpec f xs initial [])

theorem List.mapAccumLeftList ∀ (xs: List a) (initial: s) (f: s → a → Pair s b):
    Pair.snd (List.mapAccumLeft xs initial f)
      = List.zipWith xs (List.scanLeft xs initial (st x => Pair.fst (f st x))).toList (x st => Pair.snd (f st x)) :=
  Eq.cong Pair.snd (List.mapAccumLeftGoSpec f xs initial [])

theorem List.lengthMapAccumLeft ∀ (xs: List a) (initial: s) (f: s → a → Pair s b):
    List.length (Pair.snd (List.mapAccumLeft xs initial f)) = List.length xs :=
  rewrite List.mapAccumLeftList xs initial f then
    List.lengthZipWithScanLeft (st x => Pair.fst (f st x)) (x st => Pair.snd (f st x)) xs initial

theorem List.mapAccumLeftExample: List.mapAccumLeft [1, 2, 3] 0 (sum x => MkPair (sum + x) sum) = MkPair 6 [0, 1, 3] :=
  byComputing

--| Entry k of the running accumulations is the fold of the first k
--| elements ([`List.getOrScanLeft`], std/List/Index.sw, with a fallback).
theorem List.getScanLeft ∀ (f: b → a → b) (xs: List a) (z: b) (k: Nat)
    (h: k ≤ List.length xs):
    List.get (List.scanLeft xs z f).toList k = Some (List.foldLeft (List.take xs k) z f) :=
  match xs, k with
    | [] | [_, .._], Zero => byComputing
    | [x, ..xs], Succ k => List.getScanLeft f xs (f z x) k h

--| Element k of each element beside the running accumulations is `g` of
--| element k and the fold of the elements before it, and nothing past the end.
theorem List.getZipWithScanLeft ∀ (f: b → a → b) (g: a → b → c) (xs: List a) (z: b) (k: Nat):
    List.get (List.zipWith xs (List.scanLeft xs z f).toList g) k
      = Option.map (List.get xs k) (x => g x (List.foldLeft (List.take xs k) z f)) :=
  match xs, k with
    | [], k => byComputing
    | [x, ..xs], Zero => byComputing
    | [x, ..xs], Succ k => List.getZipWithScanLeft f g xs (f z x) k

--| Running accumulations of a `NonEmptyList`, the initial value first, as for `List.scanLeft`
--| ([`NonEmptyList.scanLeftToList`]).
def NonEmptyList.scanLeft (xs: NonEmptyList a) (initial: b) (f: b → a → b): NonEmptyList b :=
  List.scanLeft xs.toList initial f

theorem NonEmptyList.scanLeftToList ∀ (xs: NonEmptyList a) (initial: b) (f: b → a → b):
    xs.scanLeft initial f = List.scanLeft xs.toList initial f :=
  byComputing

test "scanLeft's minimum, maximum and last are values" :=
  let scanned := [1, -2, 3, 1].scanLeft 0 (acc x => acc + x)
  (scanned.minimum, scanned.maximum, scanned.last) == (-1, 3, 3)
