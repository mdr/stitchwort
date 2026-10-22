-- Decimal digits of a `Nat`: `Nat.digits` and `Nat.fromDigits`, the lemmas
-- about them, and the digit values of characters. This file was the prelude's
-- digit block.

-- `n / 10 < n` once `n` has two digits.
theorem Nat.divTenLess: (n: Nat) -> Nat.leq n 9 = False -> Succ (n / 10) <= n
  | Zero,   h => Void.exfalso (Bool.trueNotFalse h)
  | Succ n, h =>
    Nat.divLeOfLtMul (Succ n) n 10
      (Nat.leTrans n (n * 10) (8 + n * 10)
        (Nat.leCongRight n (n + n * 9) (n * 10) (Eq.sym (Nat.mulSucc n 9)) (Nat.leAddRight n (n * 9)))
        (Nat.leAddLeft 8 (n * 10)))

-- Decimal digits, most significant first: `Nat.digits 1205` is `[1, 2, 0, 5]`
-- and `Nat.digits 0` is `[0]`. `Nat.digitsAcc n acc` puts them onto `acc`.
def Nat.digitsAcc (n: Nat) (acc: List Nat): List Nat
  decreasing n
:=
  if big: Nat.leq n 9 = False
  then Nat.digitsAcc (n / 10) (Cons (n % 10) acc) [decreasing := Nat.divTenLess n big]
  else Cons n acc

def Nat.digits (n: Nat): List Nat := Nat.digitsAcc n Nil


-- The number whose decimal digits these are, most significant first. Digits
-- above 9 carry into their neighbours: it is `Nat.digits`'s inverse only on
-- real digit lists.
def Nat.fromDigits (ds: List Nat): Nat := List.foldLeft (acc d => acc * 10 + d) 0 ds

-- `Nat.fromDigits` starting from `a` instead of 0: `a` is shifted left past
-- every digit.
theorem Nat.fromDigitsFrom: (a: Nat) -> (ds: List Nat) ->
    List.foldLeft (acc d => acc * 10 + d) a ds = a * Nat.pow 10 (List.length ds) + Nat.fromDigits ds
  | a, Nil       => Eq.sym (Eq.trans (Nat.addZero (a * 1)) (Nat.mulOne a))
  | a, Cons d ds =>
    Eq.trans (Nat.fromDigitsFrom (a * 10 + d) ds)
      (Eq.trans (Eq.cong (t => t + Nat.fromDigits ds) (Nat.mulDistribRight (a * 10) d (Nat.pow 10 (List.length ds))))
        (Eq.trans (Nat.addAssoc ((a * 10) * Nat.pow 10 (List.length ds)) (d * Nat.pow 10 (List.length ds)) (Nat.fromDigits ds))
          (Eq.trans (Eq.cong (t => t + (d * Nat.pow 10 (List.length ds) + Nat.fromDigits ds))
              (Eq.trans (Nat.mulAssoc a 10 (Nat.pow 10 (List.length ds))) (Eq.cong (u => a * u) (Nat.mulComm 10 (Nat.pow 10 (List.length ds))))))
            (Eq.cong (t => a * (Nat.pow 10 (List.length ds) * 10) + t) (Eq.sym (Nat.fromDigitsFrom d ds))))))

-- The first digit counts 10^n, for the n digits after it.
theorem Nat.fromDigitsCons (d: Nat) (ds: List Nat):
  Nat.fromDigits (Cons d ds) = d * Nat.pow 10 (List.length ds) + Nat.fromDigits ds := Nat.fromDigitsFrom d ds

-- One step of `Nat.digitsAcc`, for a number with one digit and for one with more.
theorem Nat.digitsAccSmall (n: Nat) (acc: List Nat) (h: Nat.leq n 9 = True): Nat.digitsAcc n acc = Cons n acc :=
  rewrite Nat.digitsAcc.unfold n acc in
  rewrite h in
  rfl

theorem Nat.digitsAccBig (n: Nat) (acc: List Nat) (h: Nat.leq n 9 = False): Nat.digitsAcc n acc = Nat.digitsAcc (n / 10) (Cons (n % 10) acc) :=
  rewrite Nat.digitsAcc.unfold n acc in
  rewrite h in
  rfl

-- `n` has few enough digits: `n < 10 ^ (number of digits)`.
theorem Nat.digitsAccBound (n: Nat) (acc: List Nat):
    Succ n * Nat.pow 10 (List.length acc) <= Nat.pow 10 (List.length (Nat.digitsAcc n acc))
  decreasing n
:=
  match e: Nat.leq n 9 with
    | True =>
      rewrite Nat.digitsAccSmall n acc e in
      Nat.leCongRight (Succ n * Nat.pow 10 (List.length acc)) (10 * Nat.pow 10 (List.length acc)) (Nat.pow 10 (List.length acc) * 10)
        (Nat.mulComm 10 (Nat.pow 10 (List.length acc))) (Nat.leMulRight (Succ n) 10 (Nat.pow 10 (List.length acc)) e)
    | False =>
      rewrite Nat.digitsAccBig n acc e in
      Nat.leTrans (Succ n * Nat.pow 10 (List.length acc)) ((Succ (n / 10) * 10) * Nat.pow 10 (List.length acc))
        (Nat.pow 10 (List.length (Nat.digitsAcc (n / 10) (Cons (n % 10) acc))))
        (Nat.leMulRight (Succ n) (Succ (n / 10) * 10) (Nat.pow 10 (List.length acc)) (Nat.divFuelBound n n 10 (Nat.succNotZero 9) (Nat.leRefl n)))
        (Nat.leCongLeft (Succ (n / 10) * (Nat.pow 10 (List.length acc) * 10)) ((Succ (n / 10) * 10) * Nat.pow 10 (List.length acc)) (Nat.pow 10 (List.length (Nat.digitsAcc (n / 10) (Cons (n % 10) acc))))
          (Eq.sym (Eq.trans (Nat.mulAssoc (Succ (n / 10)) 10 (Nat.pow 10 (List.length acc))) (Eq.cong (u => Succ (n / 10) * u) (Nat.mulComm 10 (Nat.pow 10 (List.length acc))))))
          (Nat.digitsAccBound (n / 10) (Cons (n % 10) acc) [decreasing := Nat.divTenLess n e]))

theorem Nat.ltPowTenDigits (hi: Nat): hi < Nat.pow 10 (List.length (Nat.digits hi)) :=
  Nat.leCongLeft (Succ hi * 1) (Succ hi) (Nat.pow 10 (List.length (Nat.digits hi))) (Nat.mulOne (Succ hi))
    (Nat.digitsAccBound hi Nil)

-- Every element is a decimal digit.
def Nat.Digits: List Nat -> Prop
  | Nil       => Unit
  | Cons d ds => And (d < 10) (Nat.Digits ds)

theorem Or.andWith: [p q r: Prop] -> r -> Or p q -> Or p (And q r)
  | hr, Inl a => Inl a
  | hr, Inr b => Inr (Both b hr)

-- `Nat.fromDigitsCons`, with the power written for another list of the
-- same length.
theorem Nat.fromDigitsConsLen (d: Nat) (s: List Nat) (r: List Nat) (hl: List.length s = List.length r):
  Nat.fromDigits (Cons d s) = d * Nat.pow 10 (List.length r) + Nat.fromDigits s :=
  Eq.trans (Nat.fromDigitsCons d s) (Eq.cong (n => d * Nat.pow 10 n + Nat.fromDigits s) hl)

-- n digits make a number below 10^n.
theorem Nat.fromDigitsBound: (s: List Nat) -> Nat.Digits s -> Nat.fromDigits s < Nat.pow 10 (List.length s)
  | Nil,      h          => rfl
  | Cons d s, Both hd hs =>
    Nat.ltCongLeft (d * Nat.pow 10 (List.length s) + Nat.fromDigits s) (Nat.fromDigits (Cons d s)) (Nat.pow 10 (List.length s) * 10)
      (Eq.sym (Nat.fromDigitsCons d s))
      (Nat.leTrans (Succ (d * Nat.pow 10 (List.length s) + Nat.fromDigits s)) (d * Nat.pow 10 (List.length s) + Nat.pow 10 (List.length s)) (Nat.pow 10 (List.length s) * 10)
        (Nat.ltAddCong (d * Nat.pow 10 (List.length s)) (Nat.fromDigits s) (Nat.pow 10 (List.length s)) (Nat.fromDigitsBound s hs))
        (Nat.leCongRight (d * Nat.pow 10 (List.length s) + Nat.pow 10 (List.length s)) (10 * Nat.pow 10 (List.length s)) (Nat.pow 10 (List.length s) * 10)
          (Nat.mulComm 10 (Nat.pow 10 (List.length s))) (Nat.nextMultipleLe d 10 (Nat.pow 10 (List.length s)) hd)))

-- Equal-length numbers: a smaller first digit gives a smaller number.
theorem Nat.fromDigitsHeadLess (y: Nat) (t: Nat) (s: List Nat) (r: List Nat) (hl: List.length s = List.length r)
  (hd: Nat.Digits s) (h: y < t): Nat.fromDigits (Cons y s) <= Nat.fromDigits (Cons t r) :=
  Nat.leCongLeft (y * Nat.pow 10 (List.length r) + Nat.fromDigits s) (Nat.fromDigits (Cons y s)) (Nat.fromDigits (Cons t r))
    (Eq.sym (Nat.fromDigitsConsLen y s r hl))
    (Nat.leCongRight (y * Nat.pow 10 (List.length r) + Nat.fromDigits s) (t * Nat.pow 10 (List.length r) + Nat.fromDigits r) (Nat.fromDigits (Cons t r))
      (Eq.sym (Nat.fromDigitsCons t r))
      (Nat.headLessArith y t (Nat.pow 10 (List.length r)) (Nat.fromDigits s) (Nat.fromDigits r)
        (Nat.ltCongRight (Nat.fromDigits s) (Nat.pow 10 (List.length s)) (Nat.pow 10 (List.length r)) (Eq.cong (n => Nat.pow 10 n) hl) (Nat.fromDigitsBound s hd))
        h))

-- Equal-length numbers with the same first digit: the rest decides.
theorem Nat.fromDigitsConsLe (c: Nat) (s: List Nat) (r: List Nat) (hl: List.length s = List.length r)
  (h: Nat.fromDigits s <= Nat.fromDigits r): Nat.fromDigits (Cons c s) <= Nat.fromDigits (Cons c r) :=
  Nat.leCongLeft (c * Nat.pow 10 (List.length r) + Nat.fromDigits s) (Nat.fromDigits (Cons c s)) (Nat.fromDigits (Cons c r))
    (Eq.sym (Nat.fromDigitsConsLen c s r hl))
    (Nat.leCongRight (c * Nat.pow 10 (List.length r) + Nat.fromDigits s) (c * Nat.pow 10 (List.length r) + Nat.fromDigits r) (Nat.fromDigits (Cons c r))
      (Eq.sym (Nat.fromDigitsCons c r))
      (Nat.leAddCong (c * Nat.pow 10 (List.length r)) (Nat.fromDigits s) (Nat.fromDigits r) h))

-- `Nat.digits` and `Nat.fromDigits` undo each other; the digits are digits,
-- the first is not 0 (for n >= 1), and there are k of them for
-- 10^(k-1) <= n < 10^k; digits shifted left by more digits are the digit
-- lists appended (`Nat.digitsShift`). Each is a proof by the same measure as
-- `Nat.digitsAcc`, and the accumulator is just appended.
theorem Nat.digitsAccAppend (n: Nat) (acc: List Nat): Nat.digitsAcc n acc = List.append (Nat.digitsAcc n Nil) acc
  decreasing n
:=
  match e: Nat.leq n 9 with
    | True =>
      Eq.trans (Nat.digitsAccSmall n acc e) (Eq.sym (Eq.cong (l => List.append l acc) (Nat.digitsAccSmall n Nil e)))
    | False =>
      Eq.trans (Nat.digitsAccBig n acc e)
        (Eq.trans (Nat.digitsAccAppend (n / 10) (Cons (n % 10) acc) [decreasing := Nat.divTenLess n e])
          (Eq.sym (Eq.trans (Eq.cong (l => List.append l acc) (Eq.trans (Nat.digitsAccBig n Nil e) (Nat.digitsAccAppend (n / 10) (Cons (n % 10) Nil) [decreasing := Nat.divTenLess n e])))
            (List.appendAssoc (Nat.digitsAcc (n / 10) Nil) (Cons (n % 10) Nil) acc))))

theorem Nat.digitsAccDigits (n: Nat) (acc: List Nat) (ha: Nat.Digits acc): Nat.Digits (Nat.digitsAcc n acc)
  decreasing n
:=
  match e: Nat.leq n 9 with
    | True => rewrite Nat.digitsAccSmall n acc e in Both e ha
    | False =>
      rewrite Nat.digitsAccBig n acc e in
      Nat.digitsAccDigits (n / 10) (Cons (n % 10) acc) (Both (Nat.modLt n 10) ha) [decreasing := Nat.divTenLess n e]

theorem Nat.digitsDigits (n: Nat): Nat.Digits (Nat.digits n) := Nat.digitsAccDigits n Nil Trivial

-- a * (10^k * 10) + (b * 10^k + r) = (a * 10 + b) * 10^k + r
theorem Nat.shiftDigitArith (a: Nat) (b: Nat) (p: Nat) (r: Nat): a * (p * 10) + (b * p + r) = (a * 10 + b) * p + r :=
  Eq.trans (Eq.sym (Nat.addAssoc (a * (p * 10)) (b * p) r))
    (Eq.cong (t => t + r)
      (Eq.trans (Eq.cong (t => t + b * p) (Eq.trans (Eq.cong (u => a * u) (Nat.mulComm p 10)) (Eq.sym (Nat.mulAssoc a 10 p))))
        (Eq.sym (Nat.mulDistribRight (a * 10) b p))))

theorem Nat.fromDigitsAcc (n: Nat) (acc: List Nat): Nat.fromDigits (Nat.digitsAcc n acc) = n * Nat.pow 10 (List.length acc) + Nat.fromDigits acc
  decreasing n
:=
  match e: Nat.leq n 9 with
    | True => Eq.trans (Eq.cong Nat.fromDigits (Nat.digitsAccSmall n acc e)) (Nat.fromDigitsCons n acc)
    | False =>
      Eq.trans (Eq.cong Nat.fromDigits (Nat.digitsAccBig n acc e))
        (Eq.trans (Nat.fromDigitsAcc (n / 10) (Cons (n % 10) acc) [decreasing := Nat.divTenLess n e])
          (Eq.trans (Eq.cong (t => (n / 10) * Nat.pow 10 (Succ (List.length acc)) + t) (Nat.fromDigitsCons (n % 10) acc))
            (Eq.trans (Nat.shiftDigitArith (n / 10) (n % 10) (Nat.pow 10 (List.length acc)) (Nat.fromDigits acc))
              (Eq.cong (t => t * Nat.pow 10 (List.length acc) + Nat.fromDigits acc) (Eq.sym (Nat.divModEq n 10 (Nat.succNotZero 9)))))))

theorem Nat.fromDigitsDigits (n: Nat): Nat.fromDigits (Nat.digits n) = n :=
  Eq.trans (Nat.fromDigitsAcc n Nil) (Eq.trans (Nat.addZero (n * 1)) (Nat.mulOne n))

theorem Nat.digitsAccHead (n: Nat) (acc: List Nat) (hn: 1 <= n): 1 <= List.headOr 0 (Nat.digitsAcc n acc)
  decreasing n
:=
  match e: Nat.leq n 9 with
    | True => rewrite Nat.digitsAccSmall n acc e in hn
    | False =>
      rewrite Nat.digitsAccBig n acc e in
      Nat.digitsAccHead (n / 10) (Cons (n % 10) acc) (Nat.leDivOfMulLe 1 n 10 (Nat.leqFalse n 9 e)) [decreasing := Nat.divTenLess n e]

theorem Nat.digitsHead (n: Nat) (hn: 1 <= n): 1 <= List.headOr 0 (Nat.digits n) := Nat.digitsAccHead n Nil hn

theorem Nat.digitsAccNonEmpty (n: Nat) (acc: List Nat): 1 <= List.length (Nat.digitsAcc n acc)
  decreasing n
:=
  match e: Nat.leq n 9 with
    | True => rewrite Nat.digitsAccSmall n acc e
    | False =>
      rewrite Nat.digitsAccBig n acc e in
      Nat.digitsAccNonEmpty (n / 10) (Cons (n % 10) acc) [decreasing := Nat.divTenLess n e]

theorem Nat.digitsNonEmpty (n: Nat): 1 <= List.length (Nat.digits n) := Nat.digitsAccNonEmpty n Nil

theorem Nat.digitsSnoc (a: Nat) (d: Nat) (ha: 1 <= a) (hd: d < 10): Nat.digits (a * 10 + d) = List.append (Nat.digits a) (Cons d Nil) :=
  Eq.trans (Nat.digitsAccBig (a * 10 + d) Nil
      (Nat.leqFalseOfLess 9 (a * 10 + d) (Nat.leTrans 10 (a * 10) (a * 10 + d) (Nat.leMulRight 1 a 10 ha) (Nat.leAddRight (a * 10) d))))
    (Eq.trans (Eq.cong (t => Nat.digitsAcc t (Cons ((a * 10 + d) % 10) Nil))
        (Eq.trans (Eq.cong (t => t / 10) (Nat.addComm (a * 10) d)) (Eq.trans (Nat.divAddMul d a 10) (Eq.cong (t => t + a) (Nat.divSmall d 10 hd)))))
      (Eq.trans (Eq.cong (t => Nat.digitsAcc a (Cons t Nil))
          (Eq.trans (Eq.cong (t => t % 10) (Nat.addComm (a * 10) d)) (Eq.trans (Nat.modAddMul d a 10) (Nat.modSmall d 10 hd))))
        (Nat.digitsAccAppend a (Cons d Nil))))

theorem Nat.digitsShift: (ds: List Nat) -> (a: Nat) -> 1 <= a -> Nat.Digits ds ->
    Nat.digits (a * Nat.pow 10 (List.length ds) + Nat.fromDigits ds) = List.append (Nat.digits a) ds
  | Nil,       a, ha, hd => Eq.trans (Eq.cong Nat.digits (Eq.trans (Nat.addZero (a * 1)) (Nat.mulOne a))) (Eq.sym (List.appendNil (Nat.digits a)))
  | Cons d ds, a, ha, Both hd hds =>
    Eq.trans (Eq.cong Nat.digits
        (Eq.trans (Eq.cong (t => a * (Nat.pow 10 (List.length ds) * 10) + t) (Nat.fromDigitsCons d ds))
          (Nat.shiftDigitArith a d (Nat.pow 10 (List.length ds)) (Nat.fromDigits ds))))
      (Eq.trans (Nat.digitsShift ds (a * 10 + d) (Nat.leTrans 1 a (a * 10 + d) ha (Nat.leTrans a (a * 10) (a * 10 + d) (Nat.leMulPos a 10 rfl) (Nat.leAddRight (a * 10) d))) hds)
        (Eq.trans (Eq.cong (l => List.append l ds) (Nat.digitsSnoc a d ha hd))
          (List.appendAssoc (Nat.digits a) (Cons d Nil) ds)))

theorem Nat.fromDigitsAppend (xs: List Nat) (ys: List Nat): Nat.fromDigits (List.append xs ys) = Nat.fromDigits xs * Nat.pow 10 (List.length ys) + Nat.fromDigits ys :=
  Eq.trans (List.foldLeftAppend (acc d => acc * 10 + d) 0 xs ys) (Nat.fromDigitsFrom (Nat.fromDigits xs) ys)

theorem Nat.digitsTake: (k: Nat) -> (xs: List Nat) -> Nat.Digits xs -> Nat.Digits (List.take k xs)
  | Zero,   xs,        h          => Trivial
  | Succ k, Nil,       h          => Trivial
  | Succ k, Cons x xs, Both hx hs => Both hx (Nat.digitsTake k xs hs)

theorem Nat.fromDigitsHeadBound: (l: List Nat) -> 1 <= List.headOr 0 l -> Nat.pow 10 (List.length l - 1) <= Nat.fromDigits l
  | Nil,      h => Void.exfalso (Bool.falseNotTrue h)
  | Cons d s, h =>
    Nat.leCongRight (Nat.pow 10 (List.length s)) (d * Nat.pow 10 (List.length s) + Nat.fromDigits s) (Nat.fromDigits (Cons d s)) (Eq.sym (Nat.fromDigitsCons d s))
      (Nat.leTrans (Nat.pow 10 (List.length s)) (d * Nat.pow 10 (List.length s)) (d * Nat.pow 10 (List.length s) + Nat.fromDigits s)
        (Nat.leCongLeft (1 * Nat.pow 10 (List.length s)) (Nat.pow 10 (List.length s)) (d * Nat.pow 10 (List.length s)) (Nat.addZero (Nat.pow 10 (List.length s)))
          (Nat.leMulRight 1 d (Nat.pow 10 (List.length s)) h))
        (Nat.leAddRight (d * Nat.pow 10 (List.length s)) (Nat.fromDigits s)))

theorem Nat.powTenLt (a: Nat) (c: Nat) (x: Nat) (h1: Nat.pow 10 a <= x) (h2: x < Nat.pow 10 c): a < c :=
  Bool.inspect (Nat.leq (Succ a) c) (u => u = True) (t => rfl)
    (f => Void.exfalso (Nat.lessIrrefl x (Nat.leTrans (Succ x) (Nat.pow 10 c) x h2
      (Nat.leTrans (Nat.pow 10 c) (Nat.pow 10 a) x (Nat.powMono 9 c a (Nat.leqFalse (Succ a) c f)) h1))))

theorem Nat.digitsLength (j: Nat) (b: Nat) (h1: Nat.pow 10 j <= b) (h2: b < Nat.pow 10 (Succ j)): List.length (Nat.digits b) = Succ j :=
  Nat.leAntisym (List.length (Nat.digits b)) (Succ j)
    (Nat.predLeSucc (List.length (Nat.digits b)) j
      (Nat.powTenLt (List.length (Nat.digits b) - 1) (Succ j) b
        (Nat.leCongRight (Nat.pow 10 (List.length (Nat.digits b) - 1)) (Nat.fromDigits (Nat.digits b)) b (Nat.fromDigitsDigits b)
          (Nat.fromDigitsHeadBound (Nat.digits b) (Nat.digitsHead b (Nat.leTrans 1 (Nat.pow 10 j) b (Nat.powSuccPos 9 j) h1))))
        h2))
    (Nat.powTenLt j (List.length (Nat.digits b)) b h1 (Nat.ltPowTenDigits b))

-- A number below 10^m (m >= 1) has at most m digits.
theorem Nat.digitsLengthLe: (x: Nat) -> (m: Nat) -> 1 <= m -> x < Nat.pow 10 m -> List.length (Nat.digits x) <= m
  | x,      Zero,   hm, h => Void.exfalso (Bool.falseNotTrue hm)
  | Zero,   Succ j, hm, h => rfl
  | Succ y, Succ j, hm, h =>
    Nat.predLeSucc (List.length (Nat.digits (Succ y))) j
      (Nat.powTenLt (List.length (Nat.digits (Succ y)) - 1) (Succ j) (Succ y)
        (Nat.leCongRight (Nat.pow 10 (List.length (Nat.digits (Succ y)) - 1)) (Nat.fromDigits (Nat.digits (Succ y))) (Succ y) (Nat.fromDigitsDigits (Succ y))
          (Nat.fromDigitsHeadBound (Nat.digits (Succ y)) (Nat.digitsHead (Succ y) rfl)))
        h)

-- `Char.digitValue` gives a digit, or nothing (so `Char.toDigit` loses
-- nothing).
def Option.IsDigit: Option Nat -> Prop
  | None => Unit
  | Some n  => n < 10

theorem Char.digitValueDigit (c: Char): Option.IsDigit (Char.digitValue c) :=
  Bool.inspect (Nat.leq 48 (Char.toNat c))
    (b => Option.IsDigit (Bool.ifThenElse b (u => Bool.ifThenElse (Nat.leq (Char.toNat c) 57) (u => Some (Char.toNat c - 48)) (u => None)) (u => None)))
    (e1 => Bool.inspect (Nat.leq (Char.toNat c) 57)
      (b => Option.IsDigit (Bool.ifThenElse b (u => Some (Char.toNat c - 48)) (u => None)))
      (e2 => Nat.subLtAdd (Char.toNat c) 48 10 e1 e2)
      (e2 => Trivial))
    (e1 => Trivial)

theorem Nat.digitsZero: Nat.digits 0 = [0] := rfl

theorem Nat.digitsExample: Nat.digits 1205 = [1, 2, 0, 5] := rfl

theorem Nat.fromDigitsExample: Nat.fromDigits [1, 2, 0, 5] = 1205 := rfl

theorem Nat.digitsSeven: Nat.digits 7 = [7] := rfl

theorem Nat.digitsTen: Nat.digits 10 = [1, 0] := rfl

theorem Nat.fromDigitsNil: Nat.fromDigits Nil = 0 := rfl

theorem Nat.digitsRoundTrip: Nat.fromDigits (Nat.digits 9876543210) = 9876543210 := rfl

-- Digit characters read back as their digits.
theorem Char.digitValueChar: (d: Nat) -> Nat.leq d 9 = True -> Char.digitValue (Nat.digitChar d) = Some d
  | 0, h => rfl
  | 1, h => rfl
  | 2, h => rfl
  | 3, h => rfl
  | 4, h => rfl
  | 5, h => rfl
  | 6, h => rfl
  | 7, h => rfl
  | 8, h => rfl
  | 9, h => rfl
  | Succ (Succ (Succ (Succ (Succ (Succ (Succ (Succ (Succ (Succ d))))))))), h => Void.exfalso (Bool.falseNotTrue h)

theorem Char.digitsOntoValues: (f: Nat) -> (n: Nat) -> (acc: List Char) -> n < f ->
    List.filterMap Char.digitValue (Nat.digitsOnto f n acc) = Nat.digitsAcc n (List.filterMap Char.digitValue acc)
  | Zero,   n, acc, h => Void.exfalso (Bool.falseNotTrue h)
  | Succ f, n, acc, h =>
    match e: Nat.leq n 9 with
      | True  => rewrite Nat.digitsAccSmall n (List.filterMap Char.digitValue acc) e in rewrite Char.digitValueChar n e
      | False =>
        rewrite Nat.digitsAccBig n (List.filterMap Char.digitValue acc) e in
        calc List.filterMap Char.digitValue (Nat.digitsOnto f (n / 10) (Cons (Nat.digitChar (n % 10)) acc))
          _ = Nat.digitsAcc (n / 10) (List.filterMap Char.digitValue (Cons (Nat.digitChar (n % 10)) acc))
              := Char.digitsOntoValues f (n / 10) (Cons (Nat.digitChar (n % 10)) acc) (Nat.leTrans (Succ (n / 10)) n f (Nat.divTenLess n e) h)
          _ = Nat.digitsAcc (n / 10) (Cons (n % 10) (List.filterMap Char.digitValue acc)) := rewrite Char.digitValueChar (n % 10) (Nat.modLt n 10)

-- A number written in decimal reads back as its digits.
theorem Char.toTextDigits (n: Nat): List.filterMap Char.digitValue (Text.toList (Nat.toText n)) = Nat.digits n :=
  Char.digitsOntoValues (Succ n) n Nil (Nat.leRefl n)

-- `Nat.toText` writes the digits' characters: `Nat.digitsOnto` is
-- `Nat.digitsAcc` with each digit turned into its character.
theorem Char.digitsOntoMap: (f: Nat) -> (n: Nat) -> (acc: List Nat) -> n < f ->
    Nat.digitsOnto f n (List.map Nat.digitChar acc) = List.map Nat.digitChar (Nat.digitsAcc n acc)
  | Zero,   n, acc, h => Void.exfalso (Bool.falseNotTrue h)
  | Succ f, n, acc, h =>
    match e: Nat.leq n 9 with
      | True  => rewrite Nat.digitsAccSmall n acc e
      | False =>
        rewrite Nat.digitsAccBig n acc e in
        Char.digitsOntoMap f (n / 10) (Cons (n % 10) acc) (Nat.leTrans (Succ (n / 10)) n f (Nat.divTenLess n e) h)

theorem Char.toTextMap (n: Nat): Text.toList (Nat.toText n) = List.map Nat.digitChar (Nat.digits n) :=
  Char.digitsOntoMap (Succ n) n Nil (Nat.leRefl n)

-- Reading digit characters: each digit shifts the accumulator left, so
-- `acc` ends up shifted past every digit.
theorem Text.readDigitsMap: (acc: Nat) -> (ds: List Nat) -> Nat.Digits ds ->
    Text.readDigits acc (List.map Nat.digitChar ds) = Some (acc * Nat.pow 10 (List.length ds) + Nat.fromDigits ds)
  | acc, Nil,       h          => Eq.cong Some (Nat.fromDigitsFrom acc Nil)
  | acc, Cons d ds, Both hd hs =>
    calc Text.readDigits acc (List.map Nat.digitChar (Cons d ds))
      -- the first character is the digit `d`
      _ = Text.readDigits (acc * 10 + d) (List.map Nat.digitChar ds) := rewrite Char.digitValueChar d hd
      _ = Some ((acc * 10 + d) * Nat.pow 10 (List.length ds) + Nat.fromDigits ds) := Text.readDigitsMap (acc * 10 + d) ds hs
      -- the same fold, started from `acc`
      _ = Some (acc * Nat.pow 10 (List.length (Cons d ds)) + Nat.fromDigits (Cons d ds))
          := Eq.cong Some (Eq.trans (Eq.sym (Nat.fromDigitsFrom (acc * 10 + d) ds)) (Nat.fromDigitsFrom acc (Cons d ds)))

-- A non-empty list of digits, written out, reads back as its number.
theorem Text.toNatMap: (ds: List Nat) -> 1 <= List.length ds -> Nat.Digits ds ->
    Text.toNat (MkText (List.map Nat.digitChar ds)) = Some (Nat.fromDigits ds)
  | Nil,       hl, h => Void.exfalso (Bool.falseNotTrue hl)
  | Cons d ds, hl, h =>
    calc Text.toNat (MkText (List.map Nat.digitChar (Cons d ds)))
      _ = Text.readDigits 0 (List.map Nat.digitChar (Cons d ds)) := rfl
      _ = Some (0 * Nat.pow 10 (List.length (Cons d ds)) + Nat.fromDigits (Cons d ds)) := Text.readDigitsMap 0 (Cons d ds) h
      _ = Some (Nat.fromDigits (Cons d ds)) := rfl

-- Writing a number in decimal and reading it back gives the number (`0` too:
-- it is written "0").
theorem Text.toNatToText (n: Nat): Text.toNat (Nat.toText n) = Some n :=
  calc Text.toNat (Nat.toText n)
    _ = Text.toNat (MkText (List.map Nat.digitChar (Nat.digits n))) := Eq.cong (l => Text.toNat (MkText l)) (Char.toTextMap n)
    _ = Some (Nat.fromDigits (Nat.digits n)) := Text.toNatMap (Nat.digits n) (Nat.digitsNonEmpty n) (Nat.digitsDigits n)
    _ = Some n := Eq.cong Some (Nat.fromDigitsDigits n)
