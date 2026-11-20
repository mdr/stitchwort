--| Lemmas about `take` and `drop`, prefixes (`List.stripPrefix`,
--| `List.startsWith`), and `isEmpty`, with the examples and tests that use
--| them.

--| Dropping a list's start leaves what was appended to it.
theorem List.dropAppend ∀ (start rest: List a): List.drop (List.append start rest) (List.length start) = rest :=
  match start with
    | [] => byComputing
    | [x, ..xs] => List.dropAppend xs rest

--| Nothing is left of the empty list, however much is dropped.
theorem List.dropNil ∀ (n: Nat): List.drop ([]: List a) n = [] := match n with | Zero | Succ _ => byComputing

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
theorem List.takeNil ∀ (n: Nat): List.take ([]: List a) n = [] := match n with | Zero | Succ _ => byComputing

--| A prefix is no longer than the list it came from, whether or not the
--| count reached the end. [`List.lengthTake`] gives the exact length when
--| the count is within the list, and [`List.takeAll`] gives the whole list
--| when it is past the end.
theorem List.lengthTakeLe ∀ (xs: List a) (n: Nat): List.length (List.take xs n) ≤ List.length xs := match xs, n with
  | [], Zero | Succ _ => arithmetic
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
    | [x, ..xs], Zero => Both (rewrite List.consInjectiveHead d) (arithmetic)
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
    | [], Succ _, Zero | Succ _ => byComputing
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
  | [] | [_, .._] => byComputing
