--| Decimal digits of a `Nat`: `Nat.digits` and `Nat.fromDigits`, the lemmas
--| about them, and the digit values of characters.
-- This file was the prelude's digit block.

--| `n / 10 < n` once `n` has two digits.
theorem Nat.divTenLess ∀ (n: Nat) (h: Nat.leq n 9 = False): Succ (n / 10) ≤ n := match n with
  | Succ n =>
    Nat.divLeOfLtMul (Succ n) n 10
      (Nat.leTrans n (n * 10) (8 + n * 10)
        (Nat.leCongRight n (n + n * 9) (n * 10) ring (Nat.leAddRight n (n * 9)))
        (Nat.leAddLeft 8 (n * 10)))

--| The decimal digits of `n`, most significant first, in front of `acc`.
@[tailrec]
def Nat.digitsAcc (n: Nat) (acc: List Nat): List Nat
    decreasing n
:=
  if big: Nat.leq n 9 = False
  then Nat.digitsAcc (n / 10) [n % 10, ..acc] [decreasing := Nat.divTenLess n big]
  else [n, ..acc]

--| The number whose decimal digits these are, most significant first. Digits
--| above 9 carry into their neighbours: it is `Nat.digits`'s inverse only on
--| real digit lists.
def Nat.fromDigits (digits: List Nat): Nat := List.foldLeft digits 0 (acc digit => acc * 10 + digit)

--| `Nat.fromDigits` starting from `a` instead of 0: `a` is shifted left past
--| every digit.
theorem Nat.fromDigitsFrom ∀ (a: Nat) (ds: List Nat):
    List.foldLeft ds a (acc d => acc * 10 + d) = a * Nat.pow 10 (List.length ds) + Nat.fromDigits ds := match ds with
      | [] => ring
      | [d, ..ds] => ring [Nat.fromDigitsFrom (a * 10 + d) ds, Nat.fromDigitsFrom d ds]

--| The first digit counts 10^n, for the n digits after it.
theorem Nat.fromDigitsCons ∀ (d: Nat) (ds: List Nat):
    Nat.fromDigits [d, ..ds] = d * Nat.pow 10 (List.length ds) + Nat.fromDigits ds := Nat.fromDigitsFrom d ds

--| One step of `Nat.digitsAcc`, for a number with one digit and for one with more.
theorem Nat.digitsAccSmall ∀ (n: Nat) (acc: List Nat) (h: Nat.leq n 9 = True): Nat.digitsAcc n acc = [n, ..acc] :=
  rewrite Nat.digitsAcc.unfold n acc in
  rewrite h in
  rfl

theorem Nat.digitsAccBig ∀ (n: Nat) (acc: List Nat) (h: Nat.leq n 9 = False): Nat.digitsAcc n acc = Nat.digitsAcc (n / 10) [n % 10, ..acc] :=
  rewrite Nat.digitsAcc.unfold n acc in
  rewrite h in
  rfl

theorem Nat.digitsAccNonEmpty ∀ (n: Nat) (acc: List Nat): 1 ≤ List.length (Nat.digitsAcc n acc)
    decreasing n
:= match e: Nat.leq n 9 with
  | True => rewrite Nat.digitsAccSmall n acc e
  | False =>
    rewrite Nat.digitsAccBig n acc e in
    Nat.digitsAccNonEmpty (n / 10) [n % 10, ..acc] [decreasing := Nat.divTenLess n e]

theorem Nat.digitsAccNotNil ∀ (n: Nat) (acc: List Nat): Nat.digitsAcc n acc ≠ [] :=
  nil =>
    let same := Nat.digitsAccNonEmpty n acc
    let empty := rewrite nil at same in same
    omega [empty]

--| Decimal digits, most significant first: `(Nat.digits 1205).toList` is `[1, 2, 0, 5]`
--| and `(Nat.digits 0).toList` is `[0]`. There is always a digit, so the list is a
--| `NonEmptyList` ([`Nat.digitsToList`] says it is `Nat.digitsAcc n []`).
--| `Nat.fromDigits` undoes it ([`Nat.fromDigitsDigits`]), and each is a digit ([`Nat.digitsDigits`]).
def Nat.digits (n: Nat): NonEmptyList Nat := List.toNonEmpty (Nat.digitsAcc n []) [nonEmpty := Nat.digitsAccNotNil n []]

theorem Nat.digitsToList ∀ (n: Nat): (Nat.digits n).toList = Nat.digitsAcc n [] := List.toNonEmptyToList (Nat.digitsAcc n []) [nonEmpty := Nat.digitsAccNotNil n []]

--| How many decimal digits `n` has: 1 from 0 to 9, 2 from 10 to 99, and so on. It is
--| `(Nat.digits n).length` ([`Nat.digitCountLength`]); written through `Nat.digitsAcc`
--| so that it stays a plain number in proofs, not the `Succ` that the length of a
--| `NonEmptyList` computes to.
def Nat.digitCount (n: Nat): Nat := List.length (Nat.digitsAcc n [])

theorem Nat.digitCountLength ∀ (n: Nat): Nat.digitCount n = List.length (Nat.digits n).toList := Eq.sym (Eq.cong List.length (Nat.digitsToList n))

--| A fact about `Nat.digitsAcc n []` is one about `(Nat.digits n).toList`. (`rewrite` can't
--| do it: it sees `toList` computed.)
theorem Nat.digitsAs ∀ (n: Nat) (motive: List Nat → Prop) (fact: motive (Nat.digitsAcc n [])): motive (Nat.digits n).toList := Eq.subst motive (Eq.sym (Nat.digitsToList n)) fact

--| `n` has few enough digits: `n < 10 ^ (number of digits)`.
theorem Nat.digitsAccBound ∀ (n: Nat) (acc: List Nat):
    Succ n * Nat.pow 10 (List.length acc) ≤ Nat.pow 10 (List.length (Nat.digitsAcc n acc))
    decreasing n
:= match e: Nat.leq n 9 with
  | True =>
    rewrite Nat.digitsAccSmall n acc e in
    Nat.leCongRight (Succ n * Nat.pow 10 (List.length acc)) (10 * Nat.pow 10 (List.length acc)) (Nat.pow 10 (List.length acc) * 10)
      ring (Nat.leMulRight (Succ n) 10 (Nat.pow 10 (List.length acc)) e)
  | False =>
    rewrite Nat.digitsAccBig n acc e in
    Nat.leTrans (Succ n * Nat.pow 10 (List.length acc)) ((Succ (n / 10) * 10) * Nat.pow 10 (List.length acc))
      (Nat.pow 10 (List.length (Nat.digitsAcc (n / 10) [n % 10, ..acc])))
      (Nat.leMulRight (Succ n) (Succ (n / 10) * 10) (Nat.pow 10 (List.length acc)) (Nat.divFuelBound n n 10 (Nat.succNotZero 9) (Nat.leRefl n)))
      (Nat.leCongLeft (Succ (n / 10) * (Nat.pow 10 (List.length acc) * 10)) ((Succ (n / 10) * 10) * Nat.pow 10 (List.length acc)) (Nat.pow 10 (List.length (Nat.digitsAcc (n / 10) [n % 10, ..acc])))
        ring
        (Nat.digitsAccBound (n / 10) [n % 10, ..acc] [decreasing := Nat.divTenLess n e]))

theorem Nat.ltPowTenDigits ∀ (hi: Nat): hi < Nat.pow 10 (Nat.digitCount hi) :=
  Nat.leCongLeft (Succ hi * 1) (Succ hi) (Nat.pow 10 (Nat.digitCount hi)) ring
    (Nat.digitsAccBound hi [])

--| Every element is a decimal digit.
def Nat.Digits: (digits: List Nat) → Prop
  | [] => Unit
  | [digit, ..digits] => (digit < 10) ∧ (Nat.Digits digits)

theorem Or.andWith ∀ [p q r: Prop] (hr: r) (h: p ∨ q): p ∨ (q ∧ r) := match h with
  | Inl a => Inl a
  | Inr b => Inr (Both b hr)

--| [`Nat.fromDigitsCons`], with the power written for another list of the
--| same length.
theorem Nat.fromDigitsConsLen ∀ (d: Nat) (s: List Nat) (r: List Nat) (hl: List.length s = List.length r):
    Nat.fromDigits [d, ..s] = d * Nat.pow 10 (List.length r) + Nat.fromDigits s :=
  Eq.trans (Nat.fromDigitsCons d s) (Eq.cong (n => d * Nat.pow 10 n + Nat.fromDigits s) hl)

--| n digits make a number below 10^n.
theorem Nat.fromDigitsBound ∀ (s: List Nat) (h: Nat.Digits s): Nat.fromDigits s < Nat.pow 10 (List.length s) :=
  match s, h with
    | [], h => rfl
    | [d, ..s], Both hd hs =>
      Nat.ltCongLeft (d * Nat.pow 10 (List.length s) + Nat.fromDigits s) (Nat.fromDigits [d, ..s]) (Nat.pow 10 (List.length s) * 10)
        (Eq.sym (Nat.fromDigitsCons d s))
        (Nat.leTrans (Succ (d * Nat.pow 10 (List.length s) + Nat.fromDigits s)) (d * Nat.pow 10 (List.length s) + Nat.pow 10 (List.length s)) (Nat.pow 10 (List.length s) * 10)
          (Nat.ltAddCong (d * Nat.pow 10 (List.length s)) (Nat.fromDigits s) (Nat.pow 10 (List.length s)) (Nat.fromDigitsBound s hs))
          (Nat.leCongRight (d * Nat.pow 10 (List.length s) + Nat.pow 10 (List.length s)) (10 * Nat.pow 10 (List.length s)) (Nat.pow 10 (List.length s) * 10)
            ring (Nat.nextMultipleLe d 10 (Nat.pow 10 (List.length s)) hd)))

--| Equal-length numbers: a smaller first digit gives a smaller number.
theorem Nat.fromDigitsHeadLess ∀ (y: Nat) (t: Nat) (s: List Nat) (r: List Nat) (hl: List.length s = List.length r)
    (hd: Nat.Digits s) (h: y < t): Nat.fromDigits [y, ..s] ≤ Nat.fromDigits [t, ..r] :=
  Nat.leCongLeft (y * Nat.pow 10 (List.length r) + Nat.fromDigits s) (Nat.fromDigits [y, ..s]) (Nat.fromDigits [t, ..r])
    (Eq.sym (Nat.fromDigitsConsLen y s r hl))
    (Nat.leCongRight (y * Nat.pow 10 (List.length r) + Nat.fromDigits s) (t * Nat.pow 10 (List.length r) + Nat.fromDigits r) (Nat.fromDigits [t, ..r])
      (Eq.sym (Nat.fromDigitsCons t r))
      (Nat.headLessArith y t (Nat.pow 10 (List.length r)) (Nat.fromDigits s) (Nat.fromDigits r)
        (Nat.ltCongRight (Nat.fromDigits s) (Nat.pow 10 (List.length s)) (Nat.pow 10 (List.length r)) (Eq.cong (n => Nat.pow 10 n) hl) (Nat.fromDigitsBound s hd))
        h))

--| Equal-length numbers with the same first digit: the rest decides.
theorem Nat.fromDigitsConsLe ∀ (c: Nat) (s: List Nat) (r: List Nat) (hl: List.length s = List.length r)
    (h: Nat.fromDigits s ≤ Nat.fromDigits r): Nat.fromDigits [c, ..s] ≤ Nat.fromDigits [c, ..r] :=
  Nat.leCongLeft (c * Nat.pow 10 (List.length r) + Nat.fromDigits s) (Nat.fromDigits [c, ..s]) (Nat.fromDigits [c, ..r])
    (Eq.sym (Nat.fromDigitsConsLen c s r hl))
    (Nat.leCongRight (c * Nat.pow 10 (List.length r) + Nat.fromDigits s) (c * Nat.pow 10 (List.length r) + Nat.fromDigits r) (Nat.fromDigits [c, ..r])
      (Eq.sym (Nat.fromDigitsCons c r))
      (Nat.leAddCong (c * Nat.pow 10 (List.length r)) (Nat.fromDigits s) (Nat.fromDigits r) h))

-- `Nat.digits` and `Nat.fromDigits` undo each other; the digits are digits,
-- the first is not 0 (for n >= 1), and there are k of them for 10^(k-1) <=
-- n < 10^k; digits shifted left by more digits are the digit lists appended
-- (`Nat.digitsShift`).

--| The digits of `n` in front of `acc` are its digits, then `acc`.
-- Each is a proof by the same measure as `Nat.digitsAcc`, and the accumulator
-- is just appended.
theorem Nat.digitsAccAppend ∀ (n: Nat) (acc: List Nat): Nat.digitsAcc n acc = List.append (Nat.digitsAcc n []) acc
    decreasing n
:= match e: Nat.leq n 9 with
  | True =>
    Eq.trans (Nat.digitsAccSmall n acc e) (Eq.sym (Eq.cong (l => List.append l acc) (Nat.digitsAccSmall n [] e)))
  | False =>
    Eq.trans (Nat.digitsAccBig n acc e)
      (Eq.trans (Nat.digitsAccAppend (n / 10) [n % 10, ..acc] [decreasing := Nat.divTenLess n e])
        (Eq.sym (Eq.trans (Eq.cong (l => List.append l acc) (Eq.trans (Nat.digitsAccBig n [] e) (Nat.digitsAccAppend (n / 10) [n % 10] [decreasing := Nat.divTenLess n e])))
          (List.appendAssoc (Nat.digitsAcc (n / 10) []) [n % 10] acc))))

theorem Nat.digitsAccDigits ∀ (n: Nat) (acc: List Nat) (ha: Nat.Digits acc): Nat.Digits (Nat.digitsAcc n acc)
    decreasing n
:= match e: Nat.leq n 9 with
  | True => rewrite Nat.digitsAccSmall n acc e in Both e ha
  | False =>
    rewrite Nat.digitsAccBig n acc e in
    Nat.digitsAccDigits (n / 10) [n % 10, ..acc] (Both (Nat.modLt n 10) ha) [decreasing := Nat.divTenLess n e]

theorem Nat.digitsDigits ∀ (n: Nat): Nat.Digits (Nat.digits n).toList :=
  Nat.digitsAs n (l => Nat.Digits l) (Nat.digitsAccDigits n [] Trivial)

--| a * (10^k * 10) + (b * 10^k + r) = (a * 10 + b) * 10^k + r
theorem Nat.shiftDigitArith ∀ (a: Nat) (b: Nat) (p: Nat) (r: Nat): a * (p * 10) + (b * p + r) = (a * 10 + b) * p + r := ring

theorem Nat.fromDigitsAcc ∀ (n: Nat) (acc: List Nat): Nat.fromDigits (Nat.digitsAcc n acc) = n * Nat.pow 10 (List.length acc) + Nat.fromDigits acc
    decreasing n
:= match e: Nat.leq n 9 with
  | True => Eq.trans (Eq.cong Nat.fromDigits (Nat.digitsAccSmall n acc e)) (Nat.fromDigitsCons n acc)
  | False =>
    Eq.trans (Eq.cong Nat.fromDigits (Nat.digitsAccBig n acc e))
      (Eq.trans (Nat.fromDigitsAcc (n / 10) [n % 10, ..acc] [decreasing := Nat.divTenLess n e])
        (Eq.trans (Eq.cong (t => (n / 10) * Nat.pow 10 (Succ (List.length acc)) + t) (Nat.fromDigitsCons (n % 10) acc))
          (Eq.trans (Nat.shiftDigitArith (n / 10) (n % 10) (Nat.pow 10 (List.length acc)) (Nat.fromDigits acc))
            (Eq.cong (t => t * Nat.pow 10 (List.length acc) + Nat.fromDigits acc) (Eq.sym (Nat.divModEq n 10))))))

theorem Nat.fromDigitsDigitsAcc ∀ (n: Nat): Nat.fromDigits (Nat.digitsAcc n []) = n :=
  rewrite Nat.fromDigitsAcc n [] in ring

theorem Nat.fromDigitsDigits ∀ (n: Nat): Nat.fromDigits (Nat.digits n).toList = n :=
  Nat.digitsAs n (l => Nat.fromDigits l = n) (Nat.fromDigitsDigitsAcc n)

theorem Nat.digitsAccHead ∀ (n: Nat) (acc: List Nat) (hn: 1 ≤ n): 1 ≤ List.headOr (Nat.digitsAcc n acc) 0
    decreasing n
:= match e: Nat.leq n 9 with
  | True => rewrite Nat.digitsAccSmall n acc e in hn
  | False =>
    rewrite Nat.digitsAccBig n acc e in
    Nat.digitsAccHead (n / 10) [n % 10, ..acc] (Nat.leDivOfMulLe 1 n 10 (e.read)) [decreasing := Nat.divTenLess n e]

theorem Nat.digitsHead ∀ (n: Nat) (hn: 1 ≤ n): 1 ≤ List.headOr (Nat.digits n).toList 0 :=
  Nat.digitsAs n (l => 1 ≤ List.headOr l 0) (Nat.digitsAccHead n [] hn)

theorem Nat.digitsNonEmpty ∀ (n: Nat): 1 ≤ Nat.digitCount n := Nat.digitsAccNonEmpty n []

--| Every number has at least one digit.
theorem Nat.digitCountPos ∀ (n: Nat): 0 < Nat.digitCount n := Nat.digitsNonEmpty n

theorem Nat.digitCountExample: Nat.digitCount 1205 = 4 := rfl

theorem Nat.digitsSnoc ∀ (a: Nat) (d: Nat) (ha: 1 ≤ a) (hd: d < 10): (Nat.digits (a * 10 + d)).toList = List.append (Nat.digits a).toList [d] :=
  Eq.trans (Nat.digitsToList (a * 10 + d)) (Eq.trans (Eq.trans (Nat.digitsAccBig (a * 10 + d) []
      (Nat.leqFalseOfLess 9 (a * 10 + d) (Nat.leTrans 10 (a * 10) (a * 10 + d) (Nat.leMulRight 1 a 10 ha) (Nat.leAddRight (a * 10) d))))
    (Eq.trans (Eq.cong (t => Nat.digitsAcc t [(a * 10 + d) % 10])
        (Eq.trans (Eq.cong (t => t / 10) (ring: a * 10 + d = d + a * 10)) (Eq.trans (Nat.divAddMul d a 10) (Eq.cong (t => t + a) (Nat.divSmall d 10 hd)))))
      (Eq.trans (Eq.cong (t => Nat.digitsAcc a [t])
          (Eq.trans (Eq.cong (t => t % 10) (ring: a * 10 + d = d + a * 10)) (Eq.trans (Nat.modAddMul d a 10) (Nat.modSmall d 10 hd))))
        (Nat.digitsAccAppend a [d]))))
      (Eq.sym (Eq.cong (l => List.append l [d]) (Nat.digitsToList a))))

theorem Nat.digitsShift ∀ (ds: List Nat) (a: Nat) (ha: 1 ≤ a) (h: Nat.Digits ds):
    (Nat.digits (a * Nat.pow 10 (List.length ds) + Nat.fromDigits ds)).toList = List.append (Nat.digits a).toList ds :=
  match ds, h with
    | [], hd => Eq.trans (Eq.cong (n => (Nat.digits n).toList) (ring: a * 1 + 0 = a)) (Eq.sym (List.appendNil (Nat.digits a).toList))
    | [d, ..ds], Both hd hds =>
      Eq.trans (Eq.cong (n => (Nat.digits n).toList)
          (Eq.trans (Eq.cong (t => a * (Nat.pow 10 (List.length ds) * 10) + t) (Nat.fromDigitsCons d ds))
            (Nat.shiftDigitArith a d (Nat.pow 10 (List.length ds)) (Nat.fromDigits ds))))
        (Eq.trans (Nat.digitsShift ds (a * 10 + d) (Nat.leTrans 1 a (a * 10 + d) ha (Nat.leTrans a (a * 10) (a * 10 + d) (Nat.leMulPos a 10 rfl) (Nat.leAddRight (a * 10) d))) hds)
          (Eq.trans (Eq.cong (l => List.append l ds) (Nat.digitsSnoc a d ha hd))
            (List.appendAssoc (Nat.digits a).toList [d] ds)))

theorem Nat.fromDigitsAppend ∀ (xs: List Nat) (ys: List Nat): Nat.fromDigits (List.append xs ys) = Nat.fromDigits xs * Nat.pow 10 (List.length ys) + Nat.fromDigits ys :=
  Eq.trans (List.foldLeftAppend xs 0 ys (acc d => acc * 10 + d)) (Nat.fromDigitsFrom (Nat.fromDigits xs) ys)

theorem Nat.digitsTake ∀ (k: Nat) (xs: List Nat) (h: Nat.Digits xs): Nat.Digits (List.take xs k) :=
  match k, xs, h with
    | Zero, xs, h => Trivial
    | Succ k, [], h => Trivial
    | Succ k, [x, ..xs], Both hx hs => Both hx (Nat.digitsTake k xs hs)

theorem Nat.digitsDrop ∀ (k: Nat) (xs: List Nat) (h: Nat.Digits xs): Nat.Digits (List.drop xs k) :=
  match k, xs, h with
    | Zero, xs, h => h
    | Succ k, [], h => Trivial
    | Succ k, [x, ..xs], Both hx hs => Nat.digitsDrop k xs hs

theorem Nat.fromDigitsHeadBound ∀ (l: List Nat) (h: 1 ≤ List.headOr l 0): Nat.pow 10 (List.length l - 1) ≤ Nat.fromDigits l :=
  match l with
    | [d, ..s] =>
      Nat.leCongRight (Nat.pow 10 (List.length s)) (d * Nat.pow 10 (List.length s) + Nat.fromDigits s) (Nat.fromDigits [d, ..s]) (Eq.sym (Nat.fromDigitsCons d s))
        (Nat.leTrans (Nat.pow 10 (List.length s)) (d * Nat.pow 10 (List.length s)) (d * Nat.pow 10 (List.length s) + Nat.fromDigits s)
          (Nat.leCongLeft (1 * Nat.pow 10 (List.length s)) (Nat.pow 10 (List.length s)) (d * Nat.pow 10 (List.length s)) ring
            (Nat.leMulRight 1 d (Nat.pow 10 (List.length s)) h))
          (Nat.leAddRight (d * Nat.pow 10 (List.length s)) (Nat.fromDigits s)))

theorem Nat.powTenLt ∀ (a: Nat) (c: Nat) (x: Nat) (h1: Nat.pow 10 a ≤ x) (h2: x < Nat.pow 10 c): a < c :=
  Bool.inspect (Nat.leq (Succ a) c) (u => u = True) (t => rfl)
    (f => Void.exfalso (Nat.lessIrrefl x (Nat.leTrans (Succ x) (Nat.pow 10 c) x h2
      (Nat.leTrans (Nat.pow 10 c) (Nat.pow 10 a) x (Nat.powMono 9 c a f.read) h1))))

theorem Nat.digitsLength ∀ (j: Nat) (b: Nat) (h1: Nat.pow 10 j ≤ b) (h2: b < Nat.pow 10 (Succ j)): Nat.digitCount b = Succ j :=
  Nat.leAntisym (Nat.digitCount b) (Succ j)
    (Nat.predLeSucc (Nat.digitCount b) j
      (Nat.powTenLt (Nat.digitCount b - 1) (Succ j) b
        (Nat.leCongRight (Nat.pow 10 (Nat.digitCount b - 1)) (Nat.fromDigits (Nat.digitsAcc b [])) b (Nat.fromDigitsDigitsAcc b)
          (Nat.fromDigitsHeadBound (Nat.digitsAcc b []) (Nat.digitsAccHead b [] (Nat.leTrans 1 (Nat.pow 10 j) b (Nat.powSuccPos 9 j) h1))))
        h2))
    (Nat.powTenLt j (Nat.digitCount b) b h1 (Nat.ltPowTenDigits b))

--| A number below 10^m (m >= 1) has at most m digits.
theorem Nat.digitsLengthLe ∀ (x m: Nat) (hm: 1 ≤ m) (h: x < Nat.pow 10 m): Nat.digitCount x ≤ m := match x, m with
  | Zero, Succ j => rfl
  | Succ y, Succ j =>
    Nat.predLeSucc (Nat.digitCount (Succ y)) j
      (Nat.powTenLt (Nat.digitCount (Succ y) - 1) (Succ j) (Succ y)
        (Nat.leCongRight (Nat.pow 10 (Nat.digitCount (Succ y) - 1)) (Nat.fromDigits (Nat.digitsAcc (Succ y) [])) (Succ y) (Nat.fromDigitsDigitsAcc (Succ y))
          (Nat.fromDigitsHeadBound (Nat.digitsAcc (Succ y) []) (Nat.digitsAccHead (Succ y) [] rfl)))
        h)

--| A bigger number has at least as many digits.
theorem Nat.digitsLengthMono ∀ (x: Nat) (y: Nat) (h: x ≤ y): Nat.digitCount x ≤ Nat.digitCount y :=
  Nat.digitsLengthLe x (Nat.digitCount y) (Nat.digitsNonEmpty y)
    (Nat.leTrans (Succ x) (Succ y) (Nat.pow 10 (Nat.digitCount y)) h (Nat.ltPowTenDigits y))

theorem Nat.digitsLengthMonoExample: Nat.digitCount 99 ≤ Nat.digitCount 100 := Nat.digitsLengthMono 99 100 rfl

--| The option is nothing, or a decimal digit, below 10: what `Char.digitValue`
--| gives (so `Char.toDigit` loses nothing).
def Option.IsDigit: (digit: Option Nat) → Prop
  | None => Unit
  | Some n => n < 10

theorem Char.digitValueDigit ∀ (c: Char): Option.IsDigit (Char.digitValue c) :=
  Bool.inspect (Nat.leq 48 (Char.toNat c))
    (b => Option.IsDigit (Bool.ifThenElse b (u => Bool.ifThenElse (Nat.leq (Char.toNat c) 57) (u => Some (Char.toNat c - 48)) (u => None)) (u => None)))
    (e1 => Bool.inspect (Nat.leq (Char.toNat c) 57)
      (b => Option.IsDigit (Bool.ifThenElse b (u => Some (Char.toNat c - 48)) (u => None)))
      (e2 => Nat.subLtAdd (Char.toNat c) 48 10 e1 e2)
      (e2 => Trivial))
    (e1 => Trivial)

theorem Nat.digitsZero: (Nat.digits 0).toList = [0] := rfl

theorem Nat.digitsExample: (Nat.digits 1205).toList = [1, 2, 0, 5] := rfl

theorem Nat.fromDigitsExample: Nat.fromDigits [1, 2, 0, 5] = 1205 := rfl

theorem Nat.digitsSeven: (Nat.digits 7).toList = [7] := rfl

theorem Nat.digitsTen: (Nat.digits 10).toList = [1, 0] := rfl

theorem Nat.fromDigitsNil: Nat.fromDigits [] = 0 := rfl

theorem Nat.digitsRoundTrip: Nat.fromDigits (Nat.digits 9876543210).toList = 9876543210 := rfl

--| Digit characters read back as their digits.
theorem Char.digitValueChar ∀ (d: Nat) (h: Nat.leq d 9 = True): Char.digitValue (Nat.digitChar d) = Some d :=
  match d with
    | 0 => rfl
    | 1 => rfl
    | 2 => rfl
    | 3 => rfl
    | 4 => rfl
    | 5 => rfl
    | 6 => rfl
    | 7 => rfl
    | 8 => rfl
    | 9 => rfl
    | Succ (Succ (Succ (Succ (Succ (Succ (Succ (Succ (Succ (Succ d))))))))) => cases

theorem Char.digitsOntoValues ∀ (f n: Nat) (acc: List Char) (h: n < f):
    List.filterMap (Nat.digitsOnto f n acc) Char.digitValue = Nat.digitsAcc n (List.filterMap acc Char.digitValue) :=
  match f with
    | Succ f =>
      match e: Nat.leq n 9 with
        | True => rewrite Nat.digitsAccSmall n (List.filterMap acc Char.digitValue) e in rewrite Char.digitValueChar n e
        | False =>
          rewrite Nat.digitsAccBig n (List.filterMap acc Char.digitValue) e in
          calc List.filterMap (Nat.digitsOnto f (n / 10) [Nat.digitChar (n % 10), ..acc]) Char.digitValue
            _ = Nat.digitsAcc (n / 10) (List.filterMap [Nat.digitChar (n % 10), ..acc] Char.digitValue)
              := Char.digitsOntoValues f (n / 10) [Nat.digitChar (n % 10), ..acc] (Nat.leTrans (Succ (n / 10)) n f (Nat.divTenLess n e) h)
            _ = Nat.digitsAcc (n / 10) [n % 10, ..List.filterMap acc Char.digitValue] := rewrite Char.digitValueChar (n % 10) (Nat.modLt n 10)

--| A number written in decimal reads back as its digits.
theorem Char.toTextDigits ∀ (n: Nat): List.filterMap (Text.toList (Nat.toText n)) Char.digitValue = (Nat.digits n).toList :=
  Nat.digitsAs n (l => List.filterMap (Text.toList (Nat.toText n)) Char.digitValue = l) (Char.digitsOntoValues (Succ n) n [] (Nat.leRefl n))

--| `Nat.toText` writes the digits' characters: `Nat.digitsOnto` is
--| `Nat.digitsAcc` with each digit turned into its character.
theorem Char.digitsOntoMap ∀ (f n: Nat) (acc: List Nat) (h: n < f):
    Nat.digitsOnto f n (List.map acc Nat.digitChar) = List.map (Nat.digitsAcc n acc) Nat.digitChar := match f with
      | Succ f =>
        match e: Nat.leq n 9 with
          | True => rewrite Nat.digitsAccSmall n acc e
          | False =>
            rewrite Nat.digitsAccBig n acc e in
            Char.digitsOntoMap f (n / 10) [n % 10, ..acc] (Nat.leTrans (Succ (n / 10)) n f (Nat.divTenLess n e) h)

theorem Char.toTextMap ∀ (n: Nat): Text.toList (Nat.toText n) = List.map (Nat.digits n).toList Nat.digitChar :=
  Nat.digitsAs n (l => Text.toList (Nat.toText n) = List.map l Nat.digitChar) (Char.digitsOntoMap (Succ n) n [] (Nat.leRefl n))

--| Reading digit characters: each digit shifts the accumulator left, so
--| `acc` ends up shifted past every digit.
theorem Text.readDigitsMap ∀ (acc: Nat) (ds: List Nat) (h: Nat.Digits ds):
    Text.readDigits acc (List.map ds Nat.digitChar) = Some (acc * Nat.pow 10 (List.length ds) + Nat.fromDigits ds) :=
  match ds, h with
    | [], h => Eq.cong Some (Nat.fromDigitsFrom acc [])
    | [d, ..ds], Both hd hs =>
      calc Text.readDigits acc (List.map [d, ..ds] Nat.digitChar)
        -- the first character is the digit `d`
        _ = Text.readDigits (acc * 10 + d) (List.map ds Nat.digitChar) := rewrite Char.digitValueChar d hd
        _ = Some ((acc * 10 + d) * Nat.pow 10 (List.length ds) + Nat.fromDigits ds) := Text.readDigitsMap (acc * 10 + d) ds hs
        -- the same fold, started from `acc`
        _ = Some (acc * Nat.pow 10 (List.length [d, ..ds]) + Nat.fromDigits [d, ..ds])
          := Eq.cong Some (Eq.trans (Eq.sym (Nat.fromDigitsFrom (acc * 10 + d) ds)) (Nat.fromDigitsFrom acc [d, ..ds]))

--| A non-empty list of digits, written out, reads back as its number.
theorem Text.toNatMap ∀ (ds: List Nat) (hl: 1 ≤ List.length ds) (h: Nat.Digits ds):
    Text.toNat (MkText (List.map ds Nat.digitChar)) = Some (Nat.fromDigits ds) := match ds with
      | [d, ..ds] =>
        calc Text.toNat (MkText (List.map [d, ..ds] Nat.digitChar))
          _ = Text.readDigits 0 (List.map [d, ..ds] Nat.digitChar) := rfl
          _ = Some (0 * Nat.pow 10 (List.length [d, ..ds]) + Nat.fromDigits [d, ..ds]) := Text.readDigitsMap 0 [d, ..ds] h
          _ = Some (Nat.fromDigits [d, ..ds]) := rfl

--| Writing a number in decimal and reading it back gives the number (`0` too:
--| it is written "0").
theorem Text.toNatToText ∀ (n: Nat): Text.toNat (Nat.toText n) = Some n :=
  calc Text.toNat (Nat.toText n)
    _ = Text.toNat (MkText (List.map (Nat.digits n).toList Nat.digitChar)) := Eq.cong (l => Text.toNat (MkText l)) (Char.toTextMap n)
    _ = Some (Nat.fromDigits (Nat.digits n).toList) := Text.toNatMap (Nat.digits n).toList rfl (Nat.digitsDigits n)
    _ = Some n := Eq.cong Some (Nat.fromDigitsDigits n)
