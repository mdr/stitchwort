--| `Nat` arithmetic and its lemmas.
-- This file was the prelude's arithmetic, division and number-helper blocks
-- after the core's division primitives.

--| Arithmetic lemmas (the basic laws of `+` and `*` are in the core, for the
--| `Add` and `Mul` instances): order and subtraction facts proved by induction,
--| then the division law and `n % d < d`.

--| Adding zero on the left leaves the number alone (Lean's `Nat.zero_add`).
theorem Nat.zeroAdd ∀ (n: Nat): 0 + n = n := byComputing

--| A successor on the left steps out of the sum (Lean's `Nat.succ_add`).
theorem Nat.succAdd ∀ (m n: Nat): Succ m + n = Succ (m + n) := byComputing

theorem Nat.addCancelLeft ∀ (a b c: Nat) (h: a + b = a + c): b = c := match a with
  | Zero => h
  | Succ a => Nat.addCancelLeft a b c (Nat.succInjective h)

theorem Nat.mulDistribLeft ∀ (a b c: Nat): a * (b + c) = a * b + a * c := calc a * (b + c)
  _ = (b + c) * a := Nat.mulComm a (b + c)
  _ = b * a + (c * a) := Nat.mulDistribRight b c a
  _ = a * b + (c * a) := Eq.cong (t => t + c * a) (Nat.mulComm b a)
  _ = a * b + (a * c) := Eq.cong (t => a * b + t) (Nat.mulComm c a)

theorem Nat.zeroLe ∀ (n: Nat): 0 ≤ n := byComputing

theorem Nat.leAntisym ∀ (a b: Nat) (h1: a ≤ b) (h2: b ≤ a): a = b := match a, b with
  | Zero, Zero => byComputing
  | Succ a, Succ b => Eq.cong Succ (Nat.leAntisym a b h1 h2)

theorem Nat.leAddRight ∀ (n m: Nat): n ≤ n + m := match n with
  | Zero => byComputing
  | Succ n => Nat.leAddRight n m

theorem Nat.leAddLeft ∀ (n m: Nat): m ≤ n + m := match n with
  | Zero => Nat.leRefl m
  | Succ n => Nat.leTrans m (n + m) (Succ (n + m)) (Nat.leAddLeft n m) (Nat.leSucc (n + m))

theorem Nat.leqSuccSelf ∀ (n: Nat): Nat.leq (Succ n) n = False := match n with
  | Zero => byComputing
  | Succ n => Nat.leqSuccSelf n

theorem Nat.lessIrrefl ∀ (n: Nat): ¬(n < n)
  | h => Bool.falseNotTrue (Eq.trans (Nat.leqSuccSelf n).flipped h)

theorem Nat.leLessSucc ∀ (m n: Nat) (h: m ≤ n): m < Succ n := h

theorem Nat.subSelf ∀ (n: Nat): n - n = 0 := match n with
  | Zero => byComputing
  | Succ n => Nat.subSelf n

theorem Nat.addSub ∀ (n m: Nat): (n + m) - m = n := match m with
  | Zero => Nat.addZero n
  | Succ m => Eq.trans (Eq.cong (t => t - Succ m) (Nat.addSucc n m)) (Nat.addSub n m)

theorem Nat.subLe ∀ (n m: Nat): n - m ≤ n := match n, m with
  | n, Zero => Nat.leRefl n
  | Zero, Succ m => byComputing
  | Succ n, Succ m => Nat.leTrans (n - m) n (Succ n) (Nat.subLe n m) (Nat.leSucc n)
theorem Nat.leCongLeft ∀ (a b n: Nat) (p: a = b) (h: a ≤ n): b ≤ n := rewrite p at h

theorem Nat.leCongRight ∀ (a b n: Nat) (p: b = n) (h: a ≤ b): a ≤ n := rewrite p at h

theorem Nat.ltCongLeft ∀ (a b n: Nat) (p: a = b) (h: a < n): b < n := rewrite p at h

theorem Nat.ltCongRight ∀ (a b n: Nat) (p: b = n) (h: a < b): a < n := rewrite p at h

theorem Nat.leAddCong ∀ (d a b: Nat) (h: a ≤ b): d + a ≤ d + b := match d with
  | Zero => h
  | Succ d => Nat.leAddCong d a b h

theorem Nat.ltAddCong ∀ (d a b: Nat) (h: a < b): d + a < d + b := match d with
  | Zero => h
  | Succ d => Nat.ltAddCong d a b h

theorem Nat.leMulRight ∀ (a b c: Nat) (h: a ≤ b): a * c ≤ b * c := match a, b with
  | Zero, b => byComputing
  | Succ a, Succ b => Nat.leAddCong c (a * c) (b * c) (Nat.leMulRight a b c h)

theorem Nat.leMulPos ∀ (x y: Nat) (h: 0 < y): x ≤ x * y := match y with
  | Succ y => Nat.leCongRight x (x + x * y) (x * Succ y) (Nat.mulSucc x y).flipped (Nat.leAddRight x (x * y))

theorem Nat.leAddCancel ∀ (d a b: Nat) (h: d + a ≤ d + b): a ≤ b := match d with
  | Zero => h
  | Succ d => Nat.leAddCancel d a b h

theorem Nat.addSubCancel ∀ (d n: Nat) (h: d ≤ n): d + (n - d) = n := match d, n with
  | Zero, n => byComputing
  | Succ d, Succ n => Eq.cong Succ (Nat.addSubCancel d n h)

theorem Nat.leqFalse ∀ (d n: Nat) (h: Nat.leq d n = False): n < d := match d, n with
  | Succ d, Zero => byComputing
  | Succ d, Succ n => Nat.leqFalse d n h

--| Comparisons from their negations and from equations.
-- (the bridge lemmas of docs/proposals/omega.md §6.4)
theorem Nat.ltOfNotLe ∀ (a b: Nat) (h: ¬(a ≤ b)): b < a := Nat.leqFalse a b (Bool.falseOfNotTrue (Nat.leq a b) h)

theorem Nat.leOfNotLt ∀ (a b: Nat) (h: ¬(a < b)): b ≤ a :=
  Nat.leqFalse (Succ a) b (Bool.falseOfNotTrue (Nat.leq (Succ a) b) h)

theorem Nat.leOfEq ∀ (a b: Nat) (e: a = b): a ≤ b := J (y p => a ≤ y) (Nat.leRefl a) e

theorem Nat.ltOfNotLeExample: 2 < 3 := Nat.ltOfNotLe 3 2 Bool.falseNotTrue

theorem Nat.subLtAdd ∀ (n x d: Nat) (hx: x ≤ n) (h: n < d + x): n - x < d := match n, x with
  | n, Zero => Nat.ltCongRight n (d + 0) d (Nat.addZero d) h
  | Succ n, Succ x => Nat.subLtAdd n x d hx (Nat.ltCongRight (Succ n) (d + Succ x) (Succ (d + x)) (Nat.addSucc d x) h)

theorem Nat.divFuelLeStep ∀ (fuel n d: Nat) (b: Bool)
    (h: Nat.leq d n = b)
    (ih: ∀ (m: Nat) => Nat.divFuel fuel m d * d ≤ m):
    Nat.divStep b fuel n d * d ≤ n :=
  match d, b with
    | Zero, True => byComputing
    | Succ d, True =>
      Nat.leCongRight
        (Succ d + Nat.divFuel fuel (n - Succ d) (Succ d) * Succ d)
        (Succ d + (n - Succ d))
        n
        (Nat.addSubCancel (Succ d) n h)
        (Nat.leAddCong (Succ d) (Nat.divFuel fuel (n - Succ d) (Succ d) * Succ d) (n - Succ d) (ih (n - Succ d)))
    | d, False => byComputing

theorem Nat.divFuelLe ∀ (fuel n d: Nat): Nat.divFuel fuel n d * d ≤ n := match fuel with
  | Zero => byComputing
  | Succ fuel => Nat.divFuelLeStep fuel n d (Nat.leq d n) byComputing (m => Nat.divFuelLe fuel m d)

theorem Nat.fuelSub ∀ (n d f: Nat) (ok: d ≠ 0) (h: n ≤ Succ f): n - d ≤ f := match n, d with
  | n, Zero => (ok byComputing).impossible
  | Zero, Succ d => byComputing
  | Succ n, Succ d => Nat.leTrans (n - d) n f (Nat.subLe n d) h

theorem Nat.divFuelBoundStep ∀ (fuel n d: Nat)
    (ok: d ≠ 0)
    (hn: n ≤ Succ fuel) (b: Bool)
    (h: Nat.leq d n = b)
    (ih: ∀ (m: Nat) => m ≤ fuel → m < Succ (Nat.divFuel fuel m d) * d):
    n < Succ (Nat.divStep b fuel n d) * d :=
  match d, b with
    | Zero, True => (ok byComputing).impossible
    | Succ d, True =>
      Nat.ltCongLeft
        (Succ d + (n - Succ d))
        n
        (Succ d + Succ (Nat.divFuel fuel (n - Succ d) (Succ d)) * Succ d)
        (Nat.addSubCancel (Succ d) n h)
        (Nat.ltAddCong
          (Succ d)
          (n - Succ d)
          (Succ (Nat.divFuel fuel (n - Succ d) (Succ d)) * Succ d)
          (ih (n - Succ d) (Nat.fuelSub n (Succ d) fuel ok hn)))
    | d, False => Nat.ltCongRight n d (d + 0) (Nat.addZero d).flipped (Nat.leqFalse d n h)

theorem Nat.nonzeroPos ∀ (d: Nat) (ok: d ≠ 0): 0 < d := match d with
  | Zero => (ok byComputing).impossible
  | Succ d => byComputing

theorem Nat.nonzeroOfPos ∀ (d: Nat) (h: 1 ≤ d): d ≠ 0 := e => Bool.falseNotTrue (rewrite e at h)

theorem Nat.divFuelBound ∀ (fuel n d: Nat) (ok: d ≠ 0) (hn: n ≤ fuel): n < Succ (Nat.divFuel fuel n d) * d :=
  match fuel, n with
    | Zero, Zero => Nat.ltCongRight 0 d (d + 0) (Nat.addZero d).flipped (Nat.nonzeroPos d ok)
    | Succ fuel, n =>
      Nat.divFuelBoundStep fuel n d ok hn (Nat.leq d n) byComputing (m hm => Nat.divFuelBound fuel m d ok hm)

--| Dividing by 0 gives 0 (Lean's `Nat.div_zero`).
theorem Nat.divZero ∀ (n: Nat): n / 0 = 0 := match n with
  | Zero => byComputing
  | Succ n => byComputing

--| Counting divisions by 0 gives 0, whatever the fuel: `Nat.divStep` stops at
--| a divisor of 0. `arithmetic` uses it for `n / 0`, which is `Nat.divFuel n n 0`,
--| stuck on the fuel `n` when `n` is unknown.
theorem Nat.divFuelZero ∀ (fuel n: Nat): Nat.divFuel fuel n 0 = 0 := match fuel with
  | Zero => byComputing
  | Succ fuel => byComputing

--| The remainder of dividing by 0 is the number itself (Lean's `Nat.mod_zero`).
theorem Nat.modZero ∀ (n: Nat): n % 0 = n := match n with
  | Zero => byComputing
  | Succ n => byComputing

--| `(n / d) * d <= n`: the quotient never overshoots.
theorem Nat.divMulLe ∀ (n d: Nat): (n / d) * d ≤ n := Nat.divFuelLe n n d

theorem Nat.divModEq ∀ (n d: Nat): n = (n / d) * d + n % d :=
  Eq.flipped (Nat.addSubCancel ((n / d) * d) n (Nat.divMulLe n d))

--| Quotient and remainder together, as `/` and `%` give them: `Nat.divMod 17 5`
--| is `MkPair 3 2`. `n` is the main value. `Nat.divMod n 0` is `MkPair 0 n`.
def Nat.divMod (n divisor: Nat): Pair Nat Nat := MkPair (n / divisor) (n % divisor)

test "Nat.divMod" := Nat.divMod 17 5 == MkPair 3 2 ∧ Nat.divMod 3 5 == MkPair 0 3 ∧ Nat.divMod 7 0 == MkPair 0 7

theorem Nat.modLess ∀ (n d: Nat) (ok: d ≠ 0): n % d < d :=
  Nat.subLtAdd n ((n / d) * d) d (Nat.divMulLe n d) (Nat.divFuelBound n n d ok (Nat.leRefl n))

--| Division with remainder is unique: if `n = q * d + r` and `r < d`, then
--| `n / d = q` and `n % d = r`. Consequences for small numbers and for adding
--| `d`, and a few facts about subtraction.
theorem Nat.notBelowAdd ∀ (d r m: Nat) (h: r < d) (e: r = d + m): Void :=
  Nat.lessIrrefl r (Nat.leTrans (Succ r) d r h (Nat.leCongRight d (d + m) r e.flipped (Nat.leAddRight d m)))

theorem Nat.quotUnique ∀ (d q r q2 r2: Nat) (h1: r < d) (h2: r2 < d) (e: q * d + r = q2 * d + r2): q = q2 :=
  match q, q2 with
    | Zero, Zero => byComputing
    | Zero, Succ k => Void.impossible (Nat.notBelowAdd d r (k * d + r2) h1 (Eq.trans e (Nat.addAssoc d (k * d) r2)))
    | Succ a, Zero =>
      Void.impossible (Nat.notBelowAdd d r2 (a * d + r) h2 (Eq.trans e.flipped (Nat.addAssoc d (a * d) r)))
    | Succ a, Succ b =>
      Eq.cong Succ
        (Nat.quotUnique d a r b r2 h1 h2
          (Nat.addCancelLeft d
            (a * d + r)
            (b * d + r2)
            (calc d + (a * d + r)
              _ = d + a * d + r := Eq.flipped (Nat.addAssoc d (a * d) r)
              _ = d + b * d + r2 := e
              _ = d + (b * d + r2) := Nat.addAssoc d (b * d) r2)))

theorem Nat.divUnique ∀ (n d q r: Nat) (h: r < d) (e: n = q * d + r): n / d = q :=
  Nat.quotUnique d
    (n / d)
    (n % d)
    q
    r
    (Nat.modLess n d (Nat.nonzeroOfPos d (Nat.leTrans 1 (Succ r) d byComputing h)))
    h
    (Eq.trans (Nat.divModEq n d).flipped e)

theorem Nat.modUnique ∀ (n d q r: Nat) (h: r < d) (e: n = q * d + r): n % d = r :=
  Nat.addCancelLeft
    (q * d)
    (n % d)
    r
    (J (y p => y * d + n % d = q * d + r) (Eq.trans (Nat.divModEq n d).flipped e) (Nat.divUnique n d q r h e))

theorem Nat.modSmall ∀ (n d: Nat) (h: n < d): n % d = n := Nat.modUnique n d 0 n h byComputing

theorem Nat.divSmall ∀ (n d: Nat) (h: n < d): n / d = 0 := Nat.divUnique n d 0 n h byComputing

theorem Nat.addDivModSelf ∀ (d n: Nat): d + n = Succ (n / d) * d + n % d :=
  Eq.trans (Eq.cong (t => d + t) (Nat.divModEq n d)) (Eq.flipped (Nat.addAssoc d ((n / d) * d) (n % d)))

theorem Nat.addDivSelf ∀ (d n: Nat) [auto ok: d ≠ 0]: (d + n) / d = Succ (n / d) :=
  Nat.divUnique (d + n) d (Succ (n / d)) (n % d) (Nat.modLess n d ok) (Nat.addDivModSelf d n)

theorem Nat.addModSelf ∀ (d n: Nat): (d + n) % d = n % d := match d with
  | Zero => byComputing
  | Succ d =>
    Nat.modUnique
      (Succ d + n)
      (Succ d)
      (Succ (n / Succ d))
      (n % Succ d)
      (Nat.modLess n (Succ d) (Nat.succNotZero d))
      (Nat.addDivModSelf (Succ d) n)

theorem Nat.zeroSub ∀ (n: Nat): 0 - n = 0 := match n with
  | Zero => byComputing
  | Succ n => byComputing

theorem Nat.subEqZero ∀ (n m: Nat) (h: n ≤ m): n - m = 0 := match n, m with
  | Zero, m => Nat.zeroSub m
  | Succ n, Succ m => Nat.subEqZero n m h

theorem Nat.addOne ∀ (a: Nat): a + 1 = Succ a := Eq.trans (Nat.addSucc a 0) (Eq.cong Succ (Nat.addZero a))

theorem Nat.modLt ∀ (n d: Nat) [auto ok: d ≠ 0]: n % d < d := Nat.modLess n d ok

theorem Nat.modSelf ∀ (d: Nat): d % d = 0 := match d with
  | Zero => byComputing
  | Succ d =>
    Nat.modUnique
      (Succ d)
      (Succ d)
      1
      0
      byComputing
      (Eq.flipped (Eq.trans (Nat.addZero (Succ d + 0)) (Nat.addZero (Succ d))))

theorem Nat.divOne ∀ (n: Nat): n / 1 = n :=
  Nat.divUnique n 1 n 0 byComputing (Eq.flipped (Eq.trans (Nat.addZero (n * 1)) (Nat.mulOne n)))

theorem Nat.succAddSub ∀ (m r: Nat): Succ (m + r) - m = Succ r := match m with
  | Zero => byComputing
  | Succ m => Nat.succAddSub m r

theorem Nat.subSuccRight ∀ (j t: Nat) (h: Succ j ≤ t): t - j = Succ (t - Succ j) := match j, t with
  | Zero, Succ t => byComputing
  | Succ j, Succ t => Nat.subSuccRight j t h

--| `n + 1 - m` (the size of the interval `m..n`): one more than `n - m` when
--| `m <= n`, and 0 otherwise.
theorem Nat.addOneSub ∀ (n m: Nat) (h: m ≤ n): n + 1 - m = n - m + 1 := calc Succ n - m
  _ = Succ n - m := Eq.cong (t => t - m) (Nat.addOne n)
  _ = Succ (n - m) := Nat.subSuccRight m (Succ n) h
  _ = Succ (n - m) := Eq.flipped (Nat.addOne (n - m))

theorem Nat.addOneSubEqZero ∀ (n m: Nat) (h: Nat.leq m n = False): n + 1 - m = 0 :=
  Eq.trans (Eq.cong (t => t - m) (Nat.addOne n)) (Nat.subEqZero (Succ n) m h.read)

theorem Nat.succSub ∀ (t: Nat): Succ t - t = 1 := match t with
  | Zero => byComputing
  | Succ t => Nat.succSub t

--| `n / d` is the largest `q` with `q * d <= n`.
theorem Nat.mulLeOfLeDiv ∀ (q n d: Nat) (h: q ≤ n / d): q * d ≤ n :=
  Nat.leTrans (q * d) ((n / d) * d) n (Nat.leMulRight q (n / d) d h) (Nat.divMulLe n d)

theorem Nat.leDivOfMulLe ∀ (q n d: Nat) [auto ok: d ≠ 0] (h: q * d ≤ n): q ≤ n / d :=
  Bool.inspect (Nat.leq q (n / d)) (c => c = True) (t => byComputing) (f =>
    Void.impossible
      (Nat.lessIrrefl n
        (Nat.leTrans
          (Succ n)
          (Succ (n / d) * d)
          n
          (Nat.divFuelBound n n d ok (Nat.leRefl n))
          (Nat.leTrans (Succ (n / d) * d) (q * d) n (Nat.leMulRight (Succ (n / d)) q d f.read) h))))

theorem Nat.divLeOfLtMul ∀ (n b d: Nat) (h: n < Succ b * d): n / d ≤ b :=
  Bool.inspect (Nat.leq (n / d) b) (c => c = True) (t => byComputing) (f =>
    Void.impossible
      (Nat.lessIrrefl n
        (Nat.leTrans
          (Succ n)
          (Succ b * d)
          n
          h
          (Nat.leTrans (Succ b * d) ((n / d) * d) n (Nat.leMulRight (Succ b) (n / d) d f.read) (Nat.divMulLe n d)))))

--| Dividing never makes a number bigger, and makes it smaller when the number
--| is positive and the divisor is at least 2. `arithmetic` knows division by a
--| number itself; for a division by a variable, give the instance as a hint:
--| `arithmetic [Nat.divLe n k]`.
theorem Nat.divLe ∀ (n k: Nat): n / k ≤ n := match k with
  | Zero => Nat.leCongLeft 0 (n / 0) n (Nat.divZero n).flipped byComputing
  | Succ k =>
    Nat.leTrans
      (n / Succ k)
      ((n / Succ k) * Succ k)
      n
      (Nat.leMulPos (n / Succ k) (Succ k) byComputing)
      (Nat.divMulLe n (Succ k))

--| `(n + n) / 2 = n`
theorem Nat.halfDouble ∀ (n: Nat): (n + n) / 2 = n :=
  Nat.divUnique
    (n + n)
    2
    n
    0
    byComputing
    (calc n + n
      _ = n + n * 1 := Eq.flipped (Eq.cong (t => n + t) (Nat.mulOne n))
      _ = n * 2 := Eq.flipped (Nat.mulSucc n 1)
      _ = n * 2 + 0 := Eq.flipped (Nat.addZero (n * 2)))

-- Remainders and shifts. A multiple of `d` can be added or dropped without
-- changing the remainder, and a sum can be reduced early.

--| Adding a multiple of `d` adds to the quotient and leaves the remainder.
theorem Nat.addMulDivMod ∀ (a b d: Nat): a + b * d = (a / d + b) * d + a % d := calc a + (b * d)
  _ = a / d * d + (a % d) + (b * d) := Eq.cong (t => t + b * d) (Nat.divModEq a d)
  _ = a / d * d + (a % d + (b * d)) := Nat.addAssoc ((a / d) * d) (a % d) (b * d)
  _ = a / d * d + (b * d + (a % d)) := Eq.cong (t => (a / d) * d + t) (Nat.addComm (a % d) (b * d))
  _ = a / d * d + (b * d) + (a % d) := Eq.flipped (Nat.addAssoc ((a / d) * d) (b * d) (a % d))
  _ = (a / d + b) * d + (a % d) := Eq.cong (t => t + a % d) (Eq.flipped (Nat.mulDistribRight (a / d) b d))

--| `(a + b * d) % d = a % d`
theorem Nat.modAddMul ∀ (a b d: Nat): (a + b * d) % d = a % d := match d with
  | Zero =>
    calc (a + b * 0) % 0
      _ = a + b * 0 := Nat.modZero (a + b * 0)
      _ = a + 0 := Eq.cong (t => a + t) (Nat.mulZero b)
      _ = a % 0 := (Nat.modZero a).flipped
  | Succ d =>
    Nat.modUnique
      (a + b * Succ d)
      (Succ d)
      (a / Succ d + b)
      (a % Succ d)
      (Nat.modLess a (Succ d) (Nat.succNotZero d))
      (Nat.addMulDivMod a b (Succ d))

--| `(a + b * d) / d = a / d + b`
theorem Nat.divAddMul ∀ (a b d: Nat) [auto ok: d ≠ 0]: (a + b * d) / d = a / d + b :=
  Nat.divUnique (a + b * d) d (a / d + b) (a % d) (Nat.modLess a d ok) (Nat.addMulDivMod a b d)

--| `a % d % d = a % d`
theorem Nat.modMod ∀ (a d: Nat): a % d % d = a % d := match d with
  | Zero => Nat.modZero (a % 0)
  | Succ d => Nat.modSmall (a % Succ d) (Succ d) (Nat.modLess a (Succ d) (Nat.succNotZero d))

--| `(a % d + b) % d = (a + b) % d`: reducing the first summand early.
theorem Nat.modAddMod ∀ (a b d: Nat): (a % d + b) % d = (a + b) % d :=
  Eq.flipped
    (Eq.trans
      (Eq.cong
        (t => t % d)
        (calc a + b
          _ = a / d * d + (a % d) + b := Eq.cong (t => t + b) (Nat.divModEq a d)
          _ = a / d * d + (a % d + b) := Nat.addAssoc ((a / d) * d) (a % d) b
          _ = a % d + b + (a / d * d) := Nat.addComm ((a / d) * d) (a % d + b)))
      (Nat.modAddMul (a % d + b) (a / d) d))

--| `(a + b % d) % d = (a + b) % d`: the second.
theorem Nat.addModMod ∀ (a b d: Nat): (a + b % d) % d = (a + b) % d := calc (a + (b % d)) % d
  _ = (b % d + a) % d := Eq.cong (t => t % d) (Nat.addComm a (b % d))
  _ = (b + a) % d := Nat.modAddMod b a d
  _ = (a + b) % d := Eq.cong (t => t % d) (Nat.addComm b a)

--| `a * b` in two parts: the product of the remainder, and whole multiples of `d`.
theorem Nat.mulSplit ∀ (a b d: Nat): a * b = a % d * b + (a / d * b) * d := calc a * b
  _ = (a / d * d + (a % d)) * b := Eq.cong (t => t * b) (Nat.divModEq a d)
  _ = a / d * d * b + (a % d * b) := Nat.mulDistribRight (a / d * d) (a % d) b
  _ = a % d * b + (a / d * d * b) := Nat.addComm ((a / d * d) * b) (a % d * b)
  _ = a % d * b + (a / d * b * d) :=
    (Eq.cong
      (t => a % d * b + t)
      (calc a / d * d * b
        _ = a / d * (d * b) := Nat.mulAssoc (a / d) d b
        _ = a / d * (b * d) := Eq.cong (t => a / d * t) (Nat.mulComm d b)
        _ = a / d * b * d := Eq.flipped (Nat.mulAssoc (a / d) b d)))

--| `(a % d * b) % d = (a * b) % d`: reducing the first factor early.
theorem Nat.modMulMod ∀ (a b d: Nat): (a % d * b) % d = (a * b) % d :=
  Eq.flipped (Eq.trans (Eq.cong (t => t % d) (Nat.mulSplit a b d)) (Nat.modAddMul (a % d * b) (a / d * b) d))

--| `(a * (b % d)) % d = (a * b) % d`: the second.
theorem Nat.mulModMod ∀ (a b d: Nat): (a * (b % d)) % d = (a * b) % d := calc a * (b % d) % d
  _ = b % d * a % d := Eq.cong (t => t % d) (Nat.mulComm a (b % d))
  _ = b * a % d := Nat.modMulMod b a d
  _ = a * b % d := Eq.cong (t => t % d) (Nat.mulComm b a)

theorem Nat.leqFalseOfLess ∀ (a b: Nat) (h: a < b): Nat.leq b a = False :=
  Bool.inspect
    (Nat.leq b a)
    (c => c = False)
    (t => Void.impossible (Nat.lessIrrefl a (Nat.leTrans (Succ a) b a h t)))
    (f => byComputing)

--| `lo <= x <= hi`, by cases on where `x` is.
theorem Nat.betweenYes ∀ (lo hi x: Nat) (h1: lo ≤ x) (h2: x ≤ hi): (lo ≤ x ≤ hi) = True :=
  J (c q => Bool.ifThenElse c (u => Nat.leq x hi) (u => False) = True) h2 h1.flipped

theorem Nat.betweenBelow ∀ (lo hi x: Nat) (h: Nat.leq lo x = False): (lo ≤ x ≤ hi) = False :=
  J (c q => Bool.ifThenElse c (u => Nat.leq x hi) (u => False) = False) byComputing h.flipped

theorem Nat.betweenAbove ∀ (lo hi x: Nat) (h1: lo ≤ x) (h2: Nat.leq x hi = False): (lo ≤ x ≤ hi) = False :=
  J (c q => Bool.ifThenElse c (u => Nat.leq x hi) (u => False) = False) h2 h1.flipped

theorem Nat.betweenOver ∀ (lo hi x: Nat) (h: Nat.leq x hi = False): (lo ≤ x ≤ hi) = False :=
  Bool.inspect (Nat.leq lo x) (c => (lo ≤ x ≤ hi) = False) (t => Nat.betweenAbove lo hi x t h) (f =>
    Nat.betweenBelow lo hi x f)

--| `lo <= x <= hi` once `lo <= x` is known.
theorem Nat.betweenFrom ∀ (lo hi x: Nat) (h: lo ≤ x): (lo ≤ x ≤ hi) = Nat.leq x hi :=
  J (c q => Bool.ifThenElse c (u => Nat.leq x hi) (u => False) = Nat.leq x hi) byComputing h.flipped

--| Each end, from the whole test.
theorem Nat.betweenLo ∀ (lo hi x: Nat) (h: (lo ≤ x ≤ hi) = True): lo ≤ x :=
  Bool.inspect (Nat.leq lo x) (c => c = True) (t => byComputing) (f => cases)

theorem Nat.betweenHi ∀ (lo hi x: Nat) (h: (lo ≤ x ≤ hi) = True): x ≤ hi :=
  Bool.inspect (Nat.leq x hi) (c => c = True) (t => byComputing) (f =>
    Void.impossible (Bool.falseNotTrue (Eq.trans (Nat.betweenOver lo hi x f).flipped h)))

--| Rounding up and down: with `d = Succ m`, `lo <= b * d` exactly when
--| `(lo + d - 1) / d <= b`, and `b * d <= hi` exactly when `b <= hi / d`.
theorem Nat.roundUpArg ∀ (lo m: Nat): lo + Succ m - 1 = lo + m := Eq.cong (t => t - 1) (Nat.addSucc lo m)

theorem Nat.roundUpLe ∀ (lo m b: Nat) (h: lo ≤ b * Succ m): (lo + Succ m - 1) / Succ m ≤ b :=
  Nat.leCongLeft
    ((lo + m) / Succ m)
    ((lo + Succ m - 1) / Succ m)
    b
    (Eq.cong (t => t / Succ m) (Nat.roundUpArg lo m).flipped)
    (Nat.divLeOfLtMul
      (lo + m)
      b
      (Succ m)
      (Nat.leCongLeft (m + lo) (lo + m) (m + b * Succ m) (Nat.addComm m lo) (Nat.leAddCong m lo (b * Succ m) h)))

theorem Nat.roundUpGe ∀ (lo m b: Nat) (h: (lo + Succ m - 1) / Succ m ≤ b): lo ≤ b * Succ m :=
  Nat.leTrans lo
    (((lo + m) / Succ m) * Succ m)
    (b * Succ m)
    (Nat.leAddCancel m lo
      (((lo + m) / Succ m) * Succ m)
      (Nat.leCongLeft
        (lo + m)
        (m + lo)
        (m + ((lo + m) / Succ m) * Succ m)
        (Nat.addComm lo m)
        (Nat.divFuelBound (lo + m) (lo + m) (Succ m) (Nat.succNotZero m) (Nat.leRefl (lo + m)))))
    (Nat.leMulRight
      ((lo + m) / Succ m)
      b
      (Succ m)
      (Nat.leCongLeft
        ((lo + Succ m - 1) / Succ m)
        ((lo + m) / Succ m)
        b
        (Eq.cong (t => t / Succ m) (Nat.roundUpArg lo m))
        h))

theorem Nat.roundUpNo ∀ (lo m b: Nat)
    (h: Nat.leq ((lo + Succ m - 1) / Succ m) b = False):
    Nat.leq lo (b * Succ m) = False :=
  Bool.inspect
    (Nat.leq lo (b * Succ m))
    (c => c = False)
    (t => Void.impossible (Bool.falseNotTrue (Eq.trans h.flipped (Nat.roundUpLe lo m b t))))
    (f => byComputing)

theorem Nat.roundDownNo ∀ (hi m b: Nat) (h: Nat.leq b (hi / Succ m) = False): Nat.leq (b * Succ m) hi = False :=
  Bool.inspect
    (Nat.leq (b * Succ m) hi)
    (c => c = False)
    (t => Void.impossible (Bool.falseNotTrue (Eq.trans h.flipped (Nat.leDivOfMulLe b hi (Succ m) t))))
    (f => byComputing)

--| Division rounding up: `Nat.ceilDiv 7 2 = 4`. For `divisor != 0` it is the
--| smallest `b` with `n <= b * divisor` ([`Nat.ceilDivLe`], [`Nat.leMulOfCeilDivLe`]),
--| just as `n / divisor` is the largest `q` with `q * divisor <= n`. Like `/`,
--| `Nat.ceilDiv n 0` is 0.
def Nat.ceilDiv (n divisor: Nat): Nat := (n + divisor - 1) / divisor

--| Any `b` with `n <= b * d` is at least `Nat.ceilDiv n d`.
theorem Nat.ceilDivLe ∀ (n b d: Nat) (h: n ≤ b * d): Nat.ceilDiv n d ≤ b := match d with
  | Zero => Nat.leCongLeft 0 (Nat.ceilDiv n 0) b (Eq.flipped (Nat.divZero (n + 0 - 1))) byComputing
  | Succ m => Nat.roundUpLe n m b h

--| Any `b` at least `Nat.ceilDiv n d` has `n <= b * d`.
theorem Nat.leMulOfCeilDivLe ∀ (n b d: Nat) [auto ok: d ≠ 0] (h: Nat.ceilDiv n d ≤ b): n ≤ b * d := match d with
  | Zero => (ok byComputing).impossible
  | Succ m => Nat.roundUpGe n m b h

--| `Nat.ceilDiv n d` copies of `d` cover `n`.
theorem Nat.leCeilDivMul ∀ (n d: Nat) [auto ok: d ≠ 0]: n ≤ Nat.ceilDiv n d * d :=
  Nat.leMulOfCeilDivLe n (Nat.ceilDiv n d) d (Nat.leRefl (Nat.ceilDiv n d))

test "Nat.ceilDiv" := Nat.ceilDiv 7 2 == 4 ∧ Nat.ceilDiv 8 2 == 4 ∧ Nat.ceilDiv 9 3 == 3 ∧ Nat.ceilDiv 10 3 == 4

test "Nat.ceilDiv, small numerators" := Nat.ceilDiv 0 5 == 0 ∧ Nat.ceilDiv 1 5 == 1 ∧ Nat.ceilDiv 5 1 == 5

test "Nat.ceilDiv by 0" := Nat.ceilDiv 7 0 == 0

theorem Nat.powTenPredLe ∀ (k: Nat): Nat.pow 10 (k - 1) ≤ Nat.pow 10 k := match k with
  | Zero => byComputing
  | Succ k => Nat.leMulPos (Nat.pow 10 k) 10 byComputing

--| `y * p + p` is at most `t * p` when `y < t`.
theorem Nat.nextMultipleLe ∀ (y t p: Nat) (h: y < t): y * p + p ≤ t * p :=
  Nat.leCongLeft (Succ y * p) (y * p + p) (t * p) (Nat.addComm p (y * p)) (Nat.leMulRight (Succ y) t p h)

theorem Nat.headLessArith ∀ (y t p vs vr: Nat) (bound: vs < p) (h: y < t): y * p + vs ≤ t * p + vr :=
  Nat.leTrans
    (y * p + vs)
    (t * p)
    (t * p + vr)
    (Nat.leTrans
      (y * p + vs)
      (y * p + p)
      (t * p)
      (Nat.lessLe (y * p + vs) (y * p + p) (Nat.ltAddCong (y * p) vs p bound))
      (Nat.nextMultipleLe y t p h))
    (Nat.leAddRight (t * p) vr)

--| `k + (n - k) <= n` when `k <= n`, and the other way round.
theorem Nat.addSubLe ∀ (k n: Nat) (room: k ≤ n): k + (n - k) ≤ n :=
  Nat.leCongRight (k + (n - k)) (k + (n - k)) n (Nat.addSubCancel k n room) (Nat.leRefl (k + (n - k)))

theorem Nat.leSubAdd ∀ (k n: Nat) (room: k ≤ n): n ≤ (n - k) + k :=
  Nat.leCongRight n n
    ((n - k) + k)
    (Eq.trans (Nat.addSubCancel k n room).flipped (Nat.addComm k (n - k)))
    (Nat.leRefl n)

theorem Nat.addSuccLeSucc ∀ (k w n: Nat) (h: k + Succ w ≤ Succ n): k + w ≤ n :=
  Nat.leCongLeft (k + Succ w) (Succ (k + w)) (Succ n) (Nat.addSucc k w) h

theorem Nat.leOfAddLe ∀ (k w n: Nat) (h: k + w ≤ n): k ≤ n := Nat.leTrans k (k + w) n (Nat.leAddRight k w) h

--| Cancelling a positive factor; doubles; stepping along a run `s .. s + c`.
theorem Nat.mulSuccCancel ∀ (b v m: Nat) (e: b * Succ m = v * Succ m): b = v := calc b
  _ = b * Succ m / Succ m :=
    Eq.flipped (Nat.divUnique (b * Succ m) (Succ m) b 0 byComputing (Eq.flipped (Nat.addZero (b * Succ m))))
  _ = v * Succ m / Succ m := Eq.cong (t => t / Succ m) e
  _ = v := Nat.divUnique (v * Succ m) (Succ m) v 0 byComputing (Eq.flipped (Nat.addZero (v * Succ m)))

theorem Nat.mulCancelLeft: ∀ (n: Nat) => 1 ≤ n → ∀ (a b: Nat) => n * a = n * b → a = b
  | Zero, h, a, b, e => cases
  | Succ m, h, a, b, e =>
    Nat.mulSuccCancel a b m
      (calc a * Succ m
        _ = Succ m * a := Nat.mulComm a (Succ m)
        _ = Succ m * b := e
        _ = b * Succ m := Nat.mulComm (Succ m) b)

--| Cancelling a nonzero factor on the right.
theorem Nat.mulRightCancel ∀ (a b c: Nat) (nz: c ≠ 0) (e: a * c = b * c): a = b := match c with
  | Zero => (nz byComputing).impossible
  | Succ m => Nat.mulSuccCancel a b m e

theorem Nat.addSelfNotSelf ∀ (a: Nat) (h: 1 ≤ a) (e: a + a = a): Void :=
  Nat.lessIrrefl a
    (Nat.leCongRight
      (Succ a)
      (a + a)
      a
      e
      (Nat.leCongLeft (a + 1) (Succ a) (a + a) (Nat.addOne a) (Nat.leAddCong a 1 a h)))

theorem Nat.doubleNotOne ∀ (k: Nat) (e: k + k = 1): Void := match k with
  | Zero => Nat.zeroNotSucc 0 e
  | Succ k => Nat.succNotZero (k + k) (Eq.trans (Nat.addSucc k k).flipped (Nat.succInjective e))

theorem Nat.posOfDouble ∀ (k n: Nat) (e: k + k = n) (h: 1 ≤ n): 1 ≤ k := match k with
  | Zero => Void.impossible (Bool.falseNotTrue (rewrite <- e at h))
  | Succ k => byComputing

theorem Nat.leNeSucc ∀ (s v: Nat) (h: s ≤ v) (ne: s ≠ v): Succ s ≤ v :=
  Bool.inspect (Nat.leq (Succ s) v) (u => u = True) (t => byComputing) (f =>
    Void.impossible (ne (Nat.leAntisym s v h f.read)))

theorem Nat.ltAddSucc ∀ (s c b: Nat) (h: b < Succ s + c): b < s + Succ c :=
  Nat.ltCongRight b (Succ s + c) (s + Succ c) (Nat.addSucc s c).flipped h

theorem Nat.ltSuccAdd ∀ (s c b: Nat) (h: b < s + Succ c): b < Succ s + c :=
  Nat.ltCongRight b (s + Succ c) (Succ s + c) (Nat.addSucc s c) h

theorem Nat.ltAddSuccSelf ∀ (s c: Nat): s < s + Succ c := Nat.ltAddSucc s c s (Nat.leAddRight s c)

theorem Nat.predLeSucc ∀ (l j: Nat) (h: l - 1 ≤ j): l ≤ Succ j := match l with
  | Zero => byComputing
  | Succ l => h

--| In the run `s .. s + (n - s) - 1` means below `n`, even when `n < s`
--| (then the run is empty).
theorem Nat.ltOfRunSub ∀ (s d n: Nat) (h1: s ≤ d) (h2: d < s + (n - s)): d < n := match e: Nat.leq s n with
  | True => Nat.ltCongRight d (s + (n - s)) n (Nat.addSubCancel s n e) h2
  | False =>
    Void.impossible
      (Nat.lessIrrefl d
        (Nat.leTrans
          (Succ d)
          s
          d
          (Nat.ltCongRight d
            (s + (n - s))
            s
            (Eq.trans (Eq.cong (t => s + t) (Nat.subEqZero n s (Nat.lessLe n s e.read))) (Nat.addZero s))
            h2)
          h1))

--| Whether the ordering is `Less`.
def Ordering.isLess: (ordering: Ordering) → Bool
  | Less => True
  | Equal => False
  | Greater => False

--| The smaller of two numbers: `Nat.min 3 5` is 3.
def Nat.min (m n: Nat): Nat := if Nat.leq m n then m else n

--| The larger of two numbers: `Nat.max 3 5` is 5.
def Nat.max (m n: Nat): Nat := if Nat.leq m n then n else m

--| The minimum is the left number when it is at most the right.
theorem Nat.minLeft ∀ (m n: Nat) (h: m ≤ n): Nat.min m n = m :=
  J (b q => Bool.ifThenElse b (u => m) (u => n) = m) byComputing h.flipped

theorem Nat.minRight ∀ (m n: Nat) (h: Nat.leq m n = False): Nat.min m n = n :=
  J (b q => Bool.ifThenElse b (u => m) (u => n) = n) byComputing h.flipped

--| The maximum is the left number when the right is at most it.
theorem Nat.maxLeft ∀ (m n: Nat) (h: n ≤ m): Nat.max m n = m :=
  Bool.inspect (Nat.leq m n) (c => Bool.ifThenElse c (u => n) (u => m) = m) (t => Nat.leAntisym n m h t) (f =>
    byComputing)

theorem Nat.maxRight ∀ (m n: Nat) (h: m ≤ n): Nat.max m n = n :=
  J (c q => Bool.ifThenElse c (u => n) (u => m) = n) byComputing h.flipped

theorem Nat.leMaxLeft ∀ (m n: Nat): m ≤ Nat.max m n :=
  Bool.inspect (Nat.leq m n) (c => m ≤ Bool.ifThenElse c (u => n) (u => m)) (t => t) (f => Nat.leRefl m)

--| The right number is at most the maximum.
theorem Nat.leMaxRight ∀ (m n: Nat): n ≤ Nat.max m n :=
  Bool.inspect (Nat.leq m n) (c => n ≤ Bool.ifThenElse c (u => n) (u => m)) (t => Nat.leRefl n) (f =>
    Nat.lessLe n m f.read)

theorem Nat.leqMaxAbove ∀ (x a b: Nat) (h: Nat.leq x a = False): Nat.leq x (Nat.max a b) = Nat.leq x b :=
  Bool.inspect
    (Nat.leq a b)
    (c => Nat.leq x (Bool.ifThenElse c (u => b) (u => a)) = Nat.leq x b)
    (t => byComputing)
    (f => Eq.trans h (Eq.flipped (Nat.leqFalseOfLess b x (Nat.lessTrans b a x f.read h.read))))

theorem Nat.minLeLeft ∀ (m n: Nat): Nat.min m n ≤ m :=
  Bool.inspect (Nat.leq m n) (c => Bool.ifThenElse c (u => m) (u => n) ≤ m) (t => Nat.leRefl m) (f =>
    Nat.lessLe n m f.read)

theorem Nat.minLeRight ∀ (m n: Nat): Nat.min m n ≤ n :=
  Bool.inspect (Nat.leq m n) (c => Bool.ifThenElse c (u => m) (u => n) ≤ n) (t => t) (f => Nat.leRefl n)

theorem Nat.leMin ∀ (a m n: Nat) (hm: a ≤ m) (hn: a ≤ n): a ≤ Nat.min m n :=
  Bool.inspect (Nat.leq m n) (c => a ≤ Bool.ifThenElse c (u => m) (u => n)) (t => hm) (f => hn)

theorem Nat.minSucc ∀ (m n: Nat): Nat.min (Succ m) (Succ n) = Succ (Nat.min m n) :=
  Bool.inspect
    (Nat.leq m n)
    (c => Bool.ifThenElse c (u => Succ m) (u => Succ n) = Succ (Bool.ifThenElse c (u => m) (u => n)))
    (t => byComputing)
    (f => byComputing)

--| The distance between two numbers; `(a - b) + (b - a)`, as one of them is 0.
def Nat.absDiff (m n: Nat): Nat := (m - n) + (n - m)

--| The distance from a number to itself is 0.
theorem Nat.absDiffSelf ∀ (m: Nat): Nat.absDiff m m = 0 := calc m - m + (m - m)
  _ = 0 + (m - m) := Eq.cong (t => t + (m - m)) (Nat.subSelf m)
  _ = 0 + 0 := Eq.cong (t => 0 + t) (Nat.subSelf m)
  _ = 0 := byComputing

--| The distance is symmetric.
theorem Nat.absDiffComm ∀ (m n: Nat): Nat.absDiff m n = Nat.absDiff n m := Nat.addComm (m - n) (n - m)

--| When `m <= n`, the distance is the difference `n - m`.
theorem Nat.absDiffOfLe ∀ (m n: Nat) (h: m ≤ n): Nat.absDiff m n = n - m :=
  Eq.trans (Eq.cong (t => t + (n - m)) (Nat.subEqZero m n h)) byComputing

--| `b` to the power `exponent`: `Nat.pow 2 10` is 1024.
def Nat.pow (b: Nat): (exponent: Nat) → Nat
  | Zero => 1
  | Succ e => Nat.pow b e * b

--| The power with the base on the left, as `b * b^e`.
theorem Nat.powSucc ∀ (b e: Nat): Nat.pow b (Succ e) = b * Nat.pow b e := Nat.mulComm (Nat.pow b e) b

--| Adding exponents multiplies powers: `b^(e1 + e2) = b^e1 * b^e2`.
theorem Nat.powAdd ∀ (b e1 e2: Nat): Nat.pow b (e1 + e2) = Nat.pow b e1 * Nat.pow b e2 := match e1 with
  | Zero => Eq.flipped (Nat.addZero (Nat.pow b e2))
  | Succ e1 =>
    rewrite Nat.powAdd b e1 e2,
        Nat.mulAssoc (Nat.pow b e1) (Nat.pow b e2) b,
        Nat.mulComm (Nat.pow b e2) b,
        Nat.mulAssoc (Nat.pow b e1) b (Nat.pow b e2)

theorem Nat.powSuccPos ∀ (b e: Nat): 0 < Nat.pow (Succ b) e := match e with
  | Zero => byComputing
  | Succ e =>
    Nat.leTrans 1
      (Nat.pow (Succ b) e)
      (Nat.pow (Succ b) e * Succ b)
      (Nat.powSuccPos b e)
      (Nat.leMulPos (Nat.pow (Succ b) e) (Succ b) byComputing)

--| Decides that a power of a positive base is never 0. So `auto` proves
--| `Nat.pow 10 k ≠ 0` (`x % Nat.pow 10 k`), and the same of a definition that
--| unfolds to such a power.
instance Nat.decPowSuccNotZero (b: Nat) (e: Nat): Decidable (Nat.pow (Succ b) e ≠ 0) :=
  Decidable.yes (Nat.nonzeroOfPos (Nat.pow (Succ b) e) (Nat.powSuccPos b e))

theorem Nat.powMono ∀ (b e f: Nat) (h: e ≤ f): Nat.pow (Succ b) e ≤ Nat.pow (Succ b) f :=
  Nat.leCongRight
    (Nat.pow (Succ b) e)
    (Nat.pow (Succ b) e * Nat.pow (Succ b) (f - e))
    (Nat.pow (Succ b) f)
    (Eq.trans (Eq.flipped (Nat.powAdd (Succ b) e (f - e))) (Eq.cong (t => Nat.pow (Succ b) t) (Nat.addSubCancel e f h)))
    (Nat.leMulPos (Nat.pow (Succ b) e) (Nat.pow (Succ b) (f - e)) (Nat.powSuccPos b (f - e)))

theorem Nat.addTwo ∀ (n: Nat): n + 2 = Succ (Succ n) := rewrite Nat.addSucc n 1, Nat.addOne n

--| `m == n` on numbers is `Nat.equal m n`: the test of [`Nat.decEq`].
theorem Nat.eqIsEqual ∀ (m n: Nat): (m == n) = Nat.equal m n := byComputing

--| A number differs from every smaller one.
theorem Nat.equalOfLess ∀ (b v: Nat) (h: b < v): Nat.equal v b = False := match b, v with
  | Zero, Succ v => byComputing
  | Succ b, Succ v => Nat.equalOfLess b v h

--| `Nat.equal` doesn't care which number comes first.
theorem Nat.equalComm ∀ (a b: Nat): Nat.equal a b = Nat.equal b a := match a, b with
  | Zero, Zero => byComputing
  | Zero, Succ b => byComputing
  | Succ a, Zero => byComputing
  | Succ a, Succ b => Nat.equalComm a b

--| A sum is 0 only when both terms are.
theorem Nat.addEqZero ∀ (a b: Nat) (h: a + b = 0): (a = 0) ∧ (b = 0) := match a with
  | Zero => Both byComputing h
  | Succ a => Void.impossible (Nat.succNotZero (a + b) h)

theorem Nat.eqIsEqualExample: (Succ 4 == Succ 2) = (4 == 2) := Eq.trans (Nat.eqIsEqual 5 3) (Nat.eqIsEqual 4 2).flipped

--| `x < u` is "not u <= x".
theorem Nat.lessNotLe ∀ (x u: Nat): Nat.leq (Succ x) u = Bool.not (Nat.leq u x) := match x, u with
  | x, Zero => byComputing
  | Zero, Succ u => byComputing
  | Succ x, Succ u => Nat.lessNotLe x u

--| Dividing a bigger number by the same `d` gives a bigger quotient, for any
--| `d` (both quotients are 0 when `d` is 0).
theorem Nat.divMonoLeft ∀ (a b d: Nat) (below: a ≤ b): a / d ≤ b / d := match d with
  | Zero => rewrite Nat.divZero a
  | Succ n =>
    Nat.leDivOfMulLe (a / Succ n) b (Succ n) (Nat.leTrans ((a / Succ n) * Succ n) a b (Nat.divMulLe a (Succ n)) below)

--| `row * width + column` with `column < width` determines `row`: the cell
--| number of a grid stored row by row divides back to its row.
theorem Nat.mulAddDivSmall ∀ (row width column: Nat) (small: column < width): (row * width + column) / width = row :=
  Nat.divUnique (row * width + column) width row column small byComputing

test "Nat.divMonoLeft" := 7 / 2 ≤ 9 / 2 ∧ 7 / 0 ≤ 9 / 0
test "Nat.mulAddDivSmall" := (3 * 10 + 4) / 10 == 3
test "Nat.mulAddDivMatch" := (3 * 10 + 4 == 34) == (34 % 10 == 4 && 3 == 34 / 10)
