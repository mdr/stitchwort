--| Lemmas about `sumBy`, permutations, reversing (`reverse`,
--| `reverseOnto`), `map`, `filterMap` and grids, with the `all`/`any` and
--| zip-length facts around them, and the examples and tests that use them.

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
  | [] | [_] => byComputing
  | [x, y, ..ys] => rewrite List.initMap [y, ..ys] f

theorem List.lastMap ∀ (xs: List a) (f: a → b): List.last (List.map xs f) = Option.map (List.last xs) f := match xs with
  | [] | [_] => byComputing
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
  match m with | None | Some _ => byComputing

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
  match xs with | [] | [_, .._] => byComputing

theorem List.zipWith3NilThird ∀ (f: a → b → c → d) (xs: List a) (ys: List b): List.zipWith3 xs ys [] f = [] :=
  match xs, ys with
    | [], ys => byComputing
    | [_, .._], [] | [_, .._] => byComputing

theorem List.zipWith4NilSecond ∀ (zs: List c) (ws: List d) (f: a → b → c → d → e) (xs: List a):
    List.zipWith4 xs [] zs ws f = [] :=
  match xs with | [] | [_, .._] => byComputing

theorem List.zipWith4NilThird ∀ (ws: List d) (f: a → b → c → d → e) (xs: List a) (ys: List b):
    List.zipWith4 xs ys [] ws f = [] :=
  match xs, ys with
    | [], ys => byComputing
    | [_, .._], [] | [_, .._] => byComputing

theorem List.zipWith4NilFourth ∀ (f: a → b → c → d → e) (xs: List a) (ys: List b) (zs: List c):
    List.zipWith4 xs ys zs [] f = [] :=
  match xs, ys, zs with
    | [], ys, zs => byComputing
    | [x, ..xs], [], zs => byComputing
    | [_, .._], [_, .._], [] | [_, .._] => byComputing
