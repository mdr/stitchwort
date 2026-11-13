--| `Nat` arithmetic and its lemmas.
-- This file was the prelude's arithmetic, division and number-helper blocks
-- after the core's division primitives.

--| Arithmetic lemmas (the basic laws of `+` and `*` are in the core, for the
--| `Add` and `Mul` instances): order and subtraction facts proved by induction,
--| then the division law and `n % d < d`.

--| Adding zero on the left leaves the number alone (Lean's `Nat.zero_add`).
theorem Nat.zeroAdd ∀ (n: Nat): 0 + n = n := rfl

--| A successor on the left steps out of the sum (Lean's `Nat.succ_add`).
theorem Nat.succAdd ∀ (m n: Nat): Succ m + n = Succ (m + n) := rfl

theorem Nat.addCancelLeft ∀ (a b c: Nat) (h: a + b = a + c): b = c := match a with
  | Zero => h
  | Succ a => Nat.addCancelLeft a b c (Nat.succInjective h)

theorem Nat.mulDistribLeft ∀ (a: Nat) (b: Nat) (c: Nat): a * (b + c) = a * b + a * c := Eq.trans (Nat.mulComm a (b + c)) (Eq.trans (Nat.mulDistribRight b c a) (Eq.trans (Eq.cong (t => t + c * a) (Nat.mulComm b a)) (Eq.cong (t => a * b + t) (Nat.mulComm c a))))

theorem Nat.zeroLe ∀ (n: Nat): 0 ≤ n := rfl

theorem Nat.leAntisym ∀ (a b: Nat) (h1: a ≤ b) (h2: b ≤ a): a = b := match a, b with
  | Zero, Zero => rfl
  | Succ a, Succ b => Eq.cong Succ (Nat.leAntisym a b h1 h2)

theorem Nat.leAddRight ∀ (n m: Nat): n ≤ n + m := match n with
  | Zero => rfl
  | Succ n => Nat.leAddRight n m

theorem Nat.leAddLeft ∀ (n m: Nat): m ≤ n + m := match n with
  | Zero => Nat.leRefl m
  | Succ n => Nat.leTrans m (n + m) (Succ (n + m)) (Nat.leAddLeft n m) (Nat.leSucc (n + m))

theorem Nat.leqSuccSelf ∀ (n: Nat): Nat.leq (Succ n) n = False := match n with
  | Zero => rfl
  | Succ n => Nat.leqSuccSelf n

theorem Nat.lessIrrefl ∀ (n: Nat): ¬(n < n)
  | h => Bool.falseNotTrue (Eq.trans (Eq.sym (Nat.leqSuccSelf n)) h)

theorem Nat.leLessSucc ∀ (m: Nat) (n: Nat) (h: m ≤ n): m < Succ n := h

theorem Nat.subSelf ∀ (n: Nat): n - n = 0 := match n with
  | Zero => rfl
  | Succ n => Nat.subSelf n

theorem Nat.addSub ∀ (n: Nat) (m: Nat): (n + m) - m = n := match m with
  | Zero => Nat.addZero n
  | Succ m => Eq.trans (Eq.cong (t => t - Succ m) (Nat.addSucc n m)) (Nat.addSub n m)

theorem Nat.subLe ∀ (n m: Nat): n - m ≤ n := match n, m with
  | n, Zero => Nat.leRefl n
  | Zero, Succ m => rfl
  | Succ n, Succ m => Nat.leTrans (n - m) n (Succ n) (Nat.subLe n m) (Nat.leSucc n)
theorem Nat.leCongLeft ∀ (a: Nat) (b: Nat) (n: Nat) (p: a = b) (h: a ≤ n): b ≤ n := rewrite p at h

theorem Nat.leCongRight ∀ (a: Nat) (b: Nat) (n: Nat) (p: b = n) (h: a ≤ b): a ≤ n := rewrite p at h

theorem Nat.ltCongLeft ∀ (a: Nat) (b: Nat) (n: Nat) (p: a = b) (h: a < n): b < n := rewrite p at h

theorem Nat.ltCongRight ∀ (a: Nat) (b: Nat) (n: Nat) (p: b = n) (h: a < b): a < n := rewrite p at h

theorem Nat.leAddCong ∀ (d a b: Nat) (h: a ≤ b): d + a ≤ d + b := match d with
  | Zero => h
  | Succ d => Nat.leAddCong d a b h

theorem Nat.ltAddCong ∀ (d a b: Nat) (h: a < b): d + a < d + b := match d with
  | Zero => h
  | Succ d => Nat.ltAddCong d a b h

theorem Nat.leMulRight ∀ (a b c: Nat) (h: a ≤ b): a * c ≤ b * c := match a, b with
  | Zero, b => rfl
  | Succ a, Succ b => Nat.leAddCong c (a * c) (b * c) (Nat.leMulRight a b c h)

theorem Nat.leMulPos ∀ (x: Nat) (y: Nat) (h: 0 < y): x ≤ x * y := match y with
  | Succ y => Nat.leCongRight x (x + x * y) (x * Succ y) (Eq.sym (Nat.mulSucc x y)) (Nat.leAddRight x (x * y))

theorem Nat.leAddCancel ∀ (d a b: Nat) (h: d + a ≤ d + b): a ≤ b := match d with
  | Zero => h
  | Succ d => Nat.leAddCancel d a b h

theorem Nat.addSubCancel ∀ (d n: Nat) (h: d ≤ n): d + (n - d) = n := match d, n with
  | Zero, n => rfl
  | Succ d, Succ n => Eq.cong Succ (Nat.addSubCancel d n h)

theorem Nat.leqFalse ∀ (d n: Nat) (h: Nat.leq d n = False): n < d := match d, n with
  | Succ d, Zero => rfl
  | Succ d, Succ n => Nat.leqFalse d n h

--| Comparisons from their negations and from equations.
-- (the bridge lemmas of docs/proposals/omega.md §6.4)
theorem Nat.ltOfNotLe ∀ (a: Nat) (b: Nat) (h: ¬(a ≤ b)): b < a := Nat.leqFalse a b (Bool.falseOfNotTrue (Nat.leq a b) h)

theorem Nat.leOfNotLt ∀ (a: Nat) (b: Nat) (h: ¬(a < b)): b ≤ a := Nat.leqFalse (Succ a) b (Bool.falseOfNotTrue (Nat.leq (Succ a) b) h)

theorem Nat.leOfEq ∀ (a: Nat) (b: Nat) (e: a = b): a ≤ b := J (y p => a ≤ y) (Nat.leRefl a) e

theorem Nat.ltOfNotLeExample: 2 < 3 := Nat.ltOfNotLe 3 2 Bool.falseNotTrue

theorem Nat.subLtAdd ∀ (n x d: Nat) (hx: x ≤ n) (h: n < d + x): n - x < d := match n, x with
  | n, Zero => Nat.ltCongRight n (d + 0) d (Nat.addZero d) h
  | Succ n, Succ x => Nat.subLtAdd n x d hx (Nat.ltCongRight (Succ n) (d + Succ x) (Succ (d + x)) (Nat.addSucc d x) h)

theorem Nat.divFuelLeStep ∀ (fuel: Nat) (n: Nat) (d: Nat) (b: Bool) (h: Nat.leq d n = b)
    (ih: ∀ (m: Nat) => Nat.divFuel fuel m d * d ≤ m):
    Nat.divStep b fuel n d * d ≤ n := match d, b with
      | Zero, True => rfl
      | Succ d, True =>
        Nat.leCongRight (Succ d + Nat.divFuel fuel (n - Succ d) (Succ d) * Succ d) (Succ d + (n - Succ d)) n (Nat.addSubCancel (Succ d) n h)
          (Nat.leAddCong (Succ d) (Nat.divFuel fuel (n - Succ d) (Succ d) * Succ d) (n - Succ d) (ih (n - Succ d)))
      | d, False => rfl

theorem Nat.divFuelLe ∀ (fuel n d: Nat): Nat.divFuel fuel n d * d ≤ n := match fuel with
  | Zero => rfl
  | Succ fuel => Nat.divFuelLeStep fuel n d (Nat.leq d n) rfl (m => Nat.divFuelLe fuel m d)

theorem Nat.fuelSub ∀ (n d f: Nat) (ok: d ≠ 0) (h: n ≤ Succ f): n - d ≤ f := match n, d with
  | n, Zero => Void.exfalso (ok rfl)
  | Zero, Succ d => rfl
  | Succ n, Succ d => Nat.leTrans (n - d) n f (Nat.subLe n d) h

theorem Nat.divFuelBoundStep ∀ (fuel: Nat) (n: Nat) (d: Nat) (ok: d ≠ 0) (hn: n ≤ Succ fuel) (b: Bool) (h: Nat.leq d n = b)
    (ih: ∀ (m: Nat) => m ≤ fuel → m < Succ (Nat.divFuel fuel m d) * d):
    n < Succ (Nat.divStep b fuel n d) * d := match d, b with
      | Zero, True => Void.exfalso (ok rfl)
      | Succ d, True =>
        Nat.ltCongLeft (Succ d + (n - Succ d)) n (Succ d + Succ (Nat.divFuel fuel (n - Succ d) (Succ d)) * Succ d) (Nat.addSubCancel (Succ d) n h)
          (Nat.ltAddCong (Succ d) (n - Succ d) (Succ (Nat.divFuel fuel (n - Succ d) (Succ d)) * Succ d) (ih (n - Succ d) (Nat.fuelSub n (Succ d) fuel ok hn)))
      | d, False =>
        Nat.ltCongRight n d (d + 0) (Eq.sym (Nat.addZero d)) (Nat.leqFalse d n h)

theorem Nat.nonzeroPos ∀ (d: Nat) (ok: d ≠ 0): 0 < d := match d with
  | Zero => Void.exfalso (ok rfl)
  | Succ d => rfl

theorem Nat.nonzeroOfPos ∀ (d: Nat) (h: 1 ≤ d): d ≠ 0 := e => Bool.falseNotTrue (rewrite e at h)

theorem Nat.divFuelBound ∀ (fuel n d: Nat) (ok: d ≠ 0) (hn: n ≤ fuel): n < Succ (Nat.divFuel fuel n d) * d :=
  match fuel, n with
    | Zero, Zero => Nat.ltCongRight 0 d (d + 0) (Eq.sym (Nat.addZero d)) (Nat.nonzeroPos d ok)
    | Succ fuel, n => Nat.divFuelBoundStep fuel n d ok hn (Nat.leq d n) rfl (m hm => Nat.divFuelBound fuel m d ok hm)

--| Dividing by 0 gives 0 (Lean's `Nat.div_zero`).
theorem Nat.divZero ∀ (n: Nat): n / 0 = 0 := match n with
  | Zero => rfl
  | Succ n => rfl

--| Counting divisions by 0 gives 0, whatever the fuel: `Nat.divStep` stops at
--| a divisor of 0. `omega` uses it for `n / 0`, which is `Nat.divFuel n n 0`,
--| stuck on the fuel `n` when `n` is unknown.
theorem Nat.divFuelZero ∀ (fuel n: Nat): Nat.divFuel fuel n 0 = 0 := match fuel with
  | Zero => rfl
  | Succ fuel => rfl

--| The remainder of dividing by 0 is the number itself (Lean's `Nat.mod_zero`).
theorem Nat.modZero ∀ (n: Nat): n % 0 = n := match n with
  | Zero => rfl
  | Succ n => rfl

--| `(n / d) * d <= n`: the quotient never overshoots.
theorem Nat.divMulLe ∀ (n: Nat) (d: Nat): (n / d) * d ≤ n := Nat.divFuelLe n n d

theorem Nat.divModEq ∀ (n: Nat) (d: Nat): n = (n / d) * d + n % d := Eq.sym (Nat.addSubCancel ((n / d) * d) n (Nat.divMulLe n d))

--| Quotient and remainder together, as `/` and `%` give them: `Nat.divMod 17 5`
--| is `MkPair 3 2`. `n` is the main value. `Nat.divMod n 0` is `MkPair 0 n`.
def Nat.divMod (n: Nat) (divisor: Nat): Pair Nat Nat := MkPair (n / divisor) (n % divisor)

test "Nat.divMod" := Nat.divMod 17 5 == MkPair 3 2 ∧ Nat.divMod 3 5 == MkPair 0 3 ∧ Nat.divMod 7 0 == MkPair 0 7

theorem Nat.modLess ∀ (n: Nat) (d: Nat) (ok: d ≠ 0): n % d < d := Nat.subLtAdd n ((n / d) * d) d (Nat.divMulLe n d) (Nat.divFuelBound n n d ok (Nat.leRefl n))

--| Division with remainder is unique: if `n = q * d + r` and `r < d`, then
--| `n / d = q` and `n % d = r`. Consequences for small numbers and for adding
--| `d`, and a few facts about subtraction.
theorem Nat.notBelowAdd ∀ (d: Nat) (r: Nat) (m: Nat) (h: r < d) (e: r = d + m): Void := Nat.lessIrrefl r (Nat.leTrans (Succ r) d r h (Nat.leCongRight d (d + m) r (Eq.sym e) (Nat.leAddRight d m)))

theorem Nat.quotUnique ∀ (d: Nat) (q r q2 r2: Nat) (h1: r < d) (h2: r2 < d)
    (e: q * d + r = q2 * d + r2): q = q2 := match q, q2 with
      | Zero, Zero => rfl
      | Zero, Succ k => Void.exfalso (Nat.notBelowAdd d r (k * d + r2) h1 (Eq.trans e (Nat.addAssoc d (k * d) r2)))
      | Succ a, Zero => Void.exfalso (Nat.notBelowAdd d r2 (a * d + r) h2 (Eq.trans (Eq.sym e) (Nat.addAssoc d (a * d) r)))
      | Succ a, Succ b =>
        Eq.cong Succ (Nat.quotUnique d a r b r2 h1 h2
          (Nat.addCancelLeft d (a * d + r) (b * d + r2) (Eq.trans (Eq.sym (Nat.addAssoc d (a * d) r)) (Eq.trans e (Nat.addAssoc d (b * d) r2)))))

theorem Nat.divUnique ∀ (n: Nat) (d: Nat) (q: Nat) (r: Nat) (h: r < d) (e: n = q * d + r): n / d = q :=
  Nat.quotUnique d (n / d) (n % d) q r (Nat.modLess n d (Nat.nonzeroOfPos d (Nat.leTrans 1 (Succ r) d rfl h))) h (Eq.trans (Eq.sym (Nat.divModEq n d)) e)

theorem Nat.modUnique ∀ (n: Nat) (d: Nat) (q: Nat) (r: Nat) (h: r < d) (e: n = q * d + r): n % d = r :=
  Nat.addCancelLeft (q * d) (n % d) r
    (J (y p => y * d + n % d = q * d + r) (Eq.trans (Eq.sym (Nat.divModEq n d)) e) (Nat.divUnique n d q r h e))

theorem Nat.modSmall ∀ (n: Nat) (d: Nat) (h: n < d): n % d = n := Nat.modUnique n d 0 n h rfl

theorem Nat.divSmall ∀ (n: Nat) (d: Nat) (h: n < d): n / d = 0 := Nat.divUnique n d 0 n h rfl

theorem Nat.addDivModSelf ∀ (d: Nat) (n: Nat): d + n = Succ (n / d) * d + n % d := Eq.trans (Eq.cong (t => d + t) (Nat.divModEq n d)) (Eq.sym (Nat.addAssoc d ((n / d) * d) (n % d)))

theorem Nat.addDivSelf ∀ (d: Nat) (n: Nat) [auto ok: d ≠ 0]: (d + n) / d = Succ (n / d) := Nat.divUnique (d + n) d (Succ (n / d)) (n % d) (Nat.modLess n d ok) (Nat.addDivModSelf d n)

theorem Nat.addModSelf ∀ (d n: Nat): (d + n) % d = n % d := match d with
  | Zero => rfl
  | Succ d => Nat.modUnique (Succ d + n) (Succ d) (Succ (n / Succ d)) (n % Succ d) (Nat.modLess n (Succ d) (Nat.succNotZero d)) (Nat.addDivModSelf (Succ d) n)

theorem Nat.zeroSub ∀ (n: Nat): 0 - n = 0 := match n with
  | Zero => rfl
  | Succ n => rfl

theorem Nat.subEqZero ∀ (n m: Nat) (h: n ≤ m): n - m = 0 := match n, m with
  | Zero, m => Nat.zeroSub m
  | Succ n, Succ m => Nat.subEqZero n m h

theorem Nat.addOne ∀ (a: Nat): a + 1 = Succ a := Eq.trans (Nat.addSucc a 0) (Eq.cong Succ (Nat.addZero a))

theorem Nat.modLt ∀ (n: Nat) (d: Nat) [auto ok: d ≠ 0]: n % d < d := Nat.modLess n d ok

theorem Nat.modSelf ∀ (d: Nat): d % d = 0 := match d with
  | Zero => rfl
  | Succ d => Nat.modUnique (Succ d) (Succ d) 1 0 rfl (Eq.sym (Eq.trans (Nat.addZero (Succ d + 0)) (Nat.addZero (Succ d))))

theorem Nat.divOne ∀ (n: Nat): n / 1 = n := Nat.divUnique n 1 n 0 rfl (Eq.sym (Eq.trans (Nat.addZero (n * 1)) (Nat.mulOne n)))

theorem Nat.succAddSub ∀ (m r: Nat): Succ (m + r) - m = Succ r := match m with
  | Zero => rfl
  | Succ m => Nat.succAddSub m r

theorem Nat.subSuccRight ∀ (j t: Nat) (h: Succ j ≤ t): t - j = Succ (t - Succ j) := match j, t with
  | Zero, Succ t => rfl
  | Succ j, Succ t => Nat.subSuccRight j t h

--| `n + 1 - m` (the size of the interval `m..n`): one more than `n - m` when
--| `m <= n`, and 0 otherwise.
theorem Nat.addOneSub ∀ (n: Nat) (m: Nat) (h: m ≤ n): n + 1 - m = n - m + 1 :=
  Eq.trans (Eq.cong (t => t - m) (Nat.addOne n))
    (Eq.trans (Nat.subSuccRight m (Succ n) h) (Eq.sym (Nat.addOne (n - m))))

theorem Nat.addOneSubEqZero ∀ (n: Nat) (m: Nat) (h: Nat.leq m n = False): n + 1 - m = 0 :=
  Eq.trans (Eq.cong (t => t - m) (Nat.addOne n)) (Nat.subEqZero (Succ n) m h.read)

theorem Nat.succSub ∀ (t: Nat): Succ t - t = 1 := match t with
  | Zero => rfl
  | Succ t => Nat.succSub t

--| `n / d` is the largest `q` with `q * d <= n`.
theorem Nat.mulLeOfLeDiv ∀ (q: Nat) (n: Nat) (d: Nat) (h: q ≤ n / d): q * d ≤ n :=
  Nat.leTrans (q * d) ((n / d) * d) n (Nat.leMulRight q (n / d) d h) (Nat.divMulLe n d)

theorem Nat.leDivOfMulLe ∀ (q: Nat) (n: Nat) (d: Nat) [auto ok: d ≠ 0] (h: q * d ≤ n): q ≤ n / d :=
  Bool.inspect (Nat.leq q (n / d)) (c => c = True) (t => rfl)
    (f => Void.exfalso (Nat.lessIrrefl n
      (Nat.leTrans (Succ n) (Succ (n / d) * d) n (Nat.divFuelBound n n d ok (Nat.leRefl n))
        (Nat.leTrans (Succ (n / d) * d) (q * d) n (Nat.leMulRight (Succ (n / d)) q d f.read) h))))

theorem Nat.divLeOfLtMul ∀ (n: Nat) (b: Nat) (d: Nat) (h: n < Succ b * d): n / d ≤ b :=
  Bool.inspect (Nat.leq (n / d) b) (c => c = True) (t => rfl)
    (f => Void.exfalso (Nat.lessIrrefl n
      (Nat.leTrans (Succ n) (Succ b * d) n h
        (Nat.leTrans (Succ b * d) ((n / d) * d) n (Nat.leMulRight (Succ b) (n / d) d f.read) (Nat.divMulLe n d)))))

--| Dividing never makes a number bigger, and makes it smaller when the number
--| is positive and the divisor is at least 2. `omega` knows division by a
--| number itself; for a division by a variable, give the instance as a hint:
--| `omega [Nat.divLe n k]`.
theorem Nat.divLe ∀ (n k: Nat): n / k ≤ n := match k with
  | Zero => Nat.leCongLeft 0 (n / 0) n (Eq.sym (Nat.divZero n)) rfl
  | Succ k => Nat.leTrans (n / Succ k) ((n / Succ k) * Succ k) n (Nat.leMulPos (n / Succ k) (Succ k) rfl) (Nat.divMulLe n (Succ k))

--| `(n + n) / 2 = n`
theorem Nat.halfDouble ∀ (n: Nat): (n + n) / 2 = n :=
  Nat.divUnique (n + n) 2 n 0 rfl (Eq.sym (Eq.trans (Nat.addZero (n * 2)) (Eq.trans (Nat.mulSucc n 1) (Eq.cong (t => n + t) (Nat.mulOne n)))))

-- Remainders and shifts. A multiple of `d` can be added or dropped without
-- changing the remainder, and a sum can be reduced early.

--| Adding a multiple of `d` adds to the quotient and leaves the remainder.
theorem Nat.addMulDivMod ∀ (a: Nat) (b: Nat) (d: Nat): a + b * d = (a / d + b) * d + a % d :=
  Eq.trans (Eq.cong (t => t + b * d) (Nat.divModEq a d))
    (Eq.trans (Nat.addAssoc ((a / d) * d) (a % d) (b * d))
      (Eq.trans (Eq.cong (t => (a / d) * d + t) (Nat.addComm (a % d) (b * d)))
        (Eq.trans (Eq.sym (Nat.addAssoc ((a / d) * d) (b * d) (a % d)))
          (Eq.cong (t => t + a % d) (Eq.sym (Nat.mulDistribRight (a / d) b d))))))

--| `(a + b * d) % d = a % d`
theorem Nat.modAddMul ∀ (a: Nat) (b: Nat) (d: Nat): (a + b * d) % d = a % d := match d with
  | Zero => Eq.trans (Nat.modZero (a + b * 0)) (Eq.trans (Eq.cong (t => a + t) (Nat.mulZero b)) (Eq.sym (Nat.modZero a)))
  | Succ d => Nat.modUnique (a + b * Succ d) (Succ d) (a / Succ d + b) (a % Succ d) (Nat.modLess a (Succ d) (Nat.succNotZero d)) (Nat.addMulDivMod a b (Succ d))

--| `(a + b * d) / d = a / d + b`
theorem Nat.divAddMul ∀ (a: Nat) (b: Nat) (d: Nat) [auto ok: d ≠ 0]: (a + b * d) / d = a / d + b :=
  Nat.divUnique (a + b * d) d (a / d + b) (a % d) (Nat.modLess a d ok) (Nat.addMulDivMod a b d)

--| `a % d % d = a % d`
theorem Nat.modMod ∀ (a: Nat) (d: Nat): a % d % d = a % d := match d with
  | Zero => Nat.modZero (a % 0)
  | Succ d => Nat.modSmall (a % Succ d) (Succ d) (Nat.modLess a (Succ d) (Nat.succNotZero d))

--| `(a % d + b) % d = (a + b) % d`: reducing the first summand early.
theorem Nat.modAddMod ∀ (a: Nat) (b: Nat) (d: Nat): (a % d + b) % d = (a + b) % d :=
  Eq.sym (Eq.trans
    (Eq.cong (t => t % d)
      (Eq.trans (Eq.cong (t => t + b) (Nat.divModEq a d))
        (Eq.trans (Nat.addAssoc ((a / d) * d) (a % d) b) (Nat.addComm ((a / d) * d) (a % d + b)))))
    (Nat.modAddMul (a % d + b) (a / d) d))

--| `(a + b % d) % d = (a + b) % d`: the second.
theorem Nat.addModMod ∀ (a: Nat) (b: Nat) (d: Nat): (a + b % d) % d = (a + b) % d :=
  Eq.trans (Eq.cong (t => t % d) (Nat.addComm a (b % d)))
    (Eq.trans (Nat.modAddMod b a d) (Eq.cong (t => t % d) (Nat.addComm b a)))

--| `a * b` in two parts: the product of the remainder, and whole multiples of `d`.
theorem Nat.mulSplit ∀ (a: Nat) (b: Nat) (d: Nat): a * b = a % d * b + (a / d * b) * d :=
  Eq.trans (Eq.cong (t => t * b) (Nat.divModEq a d))
    (Eq.trans (Nat.mulDistribRight (a / d * d) (a % d) b)
      (Eq.trans (Nat.addComm ((a / d * d) * b) (a % d * b))
        (Eq.cong (t => a % d * b + t)
          (Eq.trans (Nat.mulAssoc (a / d) d b)
            (Eq.trans (Eq.cong (t => a / d * t) (Nat.mulComm d b)) (Eq.sym (Nat.mulAssoc (a / d) b d)))))))

--| `(a % d * b) % d = (a * b) % d`: reducing the first factor early.
theorem Nat.modMulMod ∀ (a: Nat) (b: Nat) (d: Nat): (a % d * b) % d = (a * b) % d :=
  Eq.sym (Eq.trans (Eq.cong (t => t % d) (Nat.mulSplit a b d)) (Nat.modAddMul (a % d * b) (a / d * b) d))

--| `(a * (b % d)) % d = (a * b) % d`: the second.
theorem Nat.mulModMod ∀ (a: Nat) (b: Nat) (d: Nat): (a * (b % d)) % d = (a * b) % d :=
  Eq.trans (Eq.cong (t => t % d) (Nat.mulComm a (b % d)))
    (Eq.trans (Nat.modMulMod b a d) (Eq.cong (t => t % d) (Nat.mulComm b a)))

theorem Nat.leqFalseOfLess ∀ (a: Nat) (b: Nat) (h: a < b): Nat.leq b a = False :=
  Bool.inspect (Nat.leq b a) (c => c = False)
    (t => Void.exfalso (Nat.lessIrrefl a (Nat.leTrans (Succ a) b a h t)))
    (f => rfl)

--| `lo <= x <= hi`, by cases on where `x` is.
theorem Nat.betweenYes ∀ (lo: Nat) (hi: Nat) (x: Nat) (h1: lo ≤ x) (h2: x ≤ hi): (lo ≤ x ≤ hi) = True :=
  J (c q => Bool.ifThenElse c (u => Nat.leq x hi) (u => False) = True)
    h2 (Eq.sym h1)

theorem Nat.betweenBelow ∀ (lo: Nat) (hi: Nat) (x: Nat) (h: Nat.leq lo x = False): (lo ≤ x ≤ hi) = False :=
  J (c q => Bool.ifThenElse c (u => Nat.leq x hi) (u => False) = False) rfl (Eq.sym h)

theorem Nat.betweenAbove ∀ (lo: Nat) (hi: Nat) (x: Nat) (h1: lo ≤ x) (h2: Nat.leq x hi = False): (lo ≤ x ≤ hi) = False :=
  J (c q => Bool.ifThenElse c (u => Nat.leq x hi) (u => False) = False)
    h2 (Eq.sym h1)

theorem Nat.betweenOver ∀ (lo: Nat) (hi: Nat) (x: Nat) (h: Nat.leq x hi = False): (lo ≤ x ≤ hi) = False :=
  Bool.inspect (Nat.leq lo x) (c => (lo ≤ x ≤ hi) = False) (t => Nat.betweenAbove lo hi x t h) (f => Nat.betweenBelow lo hi x f)

--| `lo <= x <= hi` once `lo <= x` is known.
theorem Nat.betweenFrom ∀ (lo: Nat) (hi: Nat) (x: Nat) (h: lo ≤ x): (lo ≤ x ≤ hi) = Nat.leq x hi :=
  J (c q => Bool.ifThenElse c (u => Nat.leq x hi) (u => False) = Nat.leq x hi)
    rfl (Eq.sym h)

--| Each end, from the whole test.
theorem Nat.betweenLo ∀ (lo: Nat) (hi: Nat) (x: Nat) (h: (lo ≤ x ≤ hi) = True): lo ≤ x :=
  Bool.inspect (Nat.leq lo x) (c => c = True) (t => rfl)
    (f => cases)

theorem Nat.betweenHi ∀ (lo: Nat) (hi: Nat) (x: Nat) (h: (lo ≤ x ≤ hi) = True): x ≤ hi :=
  Bool.inspect (Nat.leq x hi) (c => c = True) (t => rfl)
    (f => Void.exfalso (Bool.falseNotTrue (Eq.trans (Eq.sym (Nat.betweenOver lo hi x f)) h)))

--| Rounding up and down: with `d = Succ m`, `lo <= b * d` exactly when
--| `(lo + d - 1) / d <= b`, and `b * d <= hi` exactly when `b <= hi / d`.
theorem Nat.roundUpArg ∀ (lo: Nat) (m: Nat): lo + Succ m - 1 = lo + m := Eq.cong (t => t - 1) (Nat.addSucc lo m)

theorem Nat.roundUpLe ∀ (lo: Nat) (m: Nat) (b: Nat) (h: lo ≤ b * Succ m): (lo + Succ m - 1) / Succ m ≤ b :=
  Nat.leCongLeft ((lo + m) / Succ m) ((lo + Succ m - 1) / Succ m) b (Eq.cong (t => t / Succ m) (Eq.sym (Nat.roundUpArg lo m)))
    (Nat.divLeOfLtMul (lo + m) b (Succ m) (Nat.leCongLeft (m + lo) (lo + m) (m + b * Succ m) (Nat.addComm m lo) (Nat.leAddCong m lo (b * Succ m) h)))

theorem Nat.roundUpGe ∀ (lo: Nat) (m: Nat) (b: Nat) (h: (lo + Succ m - 1) / Succ m ≤ b): lo ≤ b * Succ m :=
  Nat.leTrans lo (((lo + m) / Succ m) * Succ m) (b * Succ m)
    (Nat.leAddCancel m lo (((lo + m) / Succ m) * Succ m)
      (Nat.leCongLeft (lo + m) (m + lo) (m + ((lo + m) / Succ m) * Succ m) (Nat.addComm lo m)
        (Nat.divFuelBound (lo + m) (lo + m) (Succ m) (Nat.succNotZero m) (Nat.leRefl (lo + m)))))
    (Nat.leMulRight ((lo + m) / Succ m) b (Succ m) (Nat.leCongLeft ((lo + Succ m - 1) / Succ m) ((lo + m) / Succ m) b (Eq.cong (t => t / Succ m) (Nat.roundUpArg lo m)) h))

theorem Nat.roundUpNo ∀ (lo: Nat) (m: Nat) (b: Nat) (h: Nat.leq ((lo + Succ m - 1) / Succ m) b = False): Nat.leq lo (b * Succ m) = False :=
  Bool.inspect (Nat.leq lo (b * Succ m)) (c => c = False)
    (t => Void.exfalso (Bool.falseNotTrue (Eq.trans (Eq.sym h) (Nat.roundUpLe lo m b t))))
    (f => rfl)

theorem Nat.roundDownNo ∀ (hi: Nat) (m: Nat) (b: Nat) (h: Nat.leq b (hi / Succ m) = False): Nat.leq (b * Succ m) hi = False :=
  Bool.inspect (Nat.leq (b * Succ m) hi) (c => c = False)
    (t => Void.exfalso (Bool.falseNotTrue (Eq.trans (Eq.sym h) (Nat.leDivOfMulLe b hi (Succ m) t))))
    (f => rfl)

--| Division rounding up: `Nat.ceilDiv 7 2 = 4`. For `divisor != 0` it is the
--| smallest `b` with `n <= b * divisor` ([`Nat.ceilDivLe`], [`Nat.leMulOfCeilDivLe`]),
--| just as `n / divisor` is the largest `q` with `q * divisor <= n`. Like `/`,
--| `Nat.ceilDiv n 0` is 0.
def Nat.ceilDiv (n: Nat) (divisor: Nat): Nat := (n + divisor - 1) / divisor

--| Any `b` with `n <= b * d` is at least `Nat.ceilDiv n d`.
theorem Nat.ceilDivLe ∀ (n: Nat) (b: Nat) (d: Nat) (h: n ≤ b * d): Nat.ceilDiv n d ≤ b := match d with
  | Zero => Nat.leCongLeft 0 (Nat.ceilDiv n 0) b (Eq.sym (Nat.divZero (n + 0 - 1))) rfl
  | Succ m => Nat.roundUpLe n m b h

--| Any `b` at least `Nat.ceilDiv n d` has `n <= b * d`.
theorem Nat.leMulOfCeilDivLe ∀ (n: Nat) (b: Nat) (d: Nat) [auto ok: d ≠ 0] (h: Nat.ceilDiv n d ≤ b): n ≤ b * d :=
  match d with
    | Zero => Void.exfalso (ok rfl)
    | Succ m => Nat.roundUpGe n m b h

--| `Nat.ceilDiv n d` copies of `d` cover `n`.
theorem Nat.leCeilDivMul ∀ (n: Nat) (d: Nat) [auto ok: d ≠ 0]: n ≤ Nat.ceilDiv n d * d :=
  Nat.leMulOfCeilDivLe n (Nat.ceilDiv n d) d (Nat.leRefl (Nat.ceilDiv n d))

test "Nat.ceilDiv" := Nat.ceilDiv 7 2 == 4 ∧ Nat.ceilDiv 8 2 == 4 ∧ Nat.ceilDiv 9 3 == 3 ∧ Nat.ceilDiv 10 3 == 4

test "Nat.ceilDiv, small numerators" := Nat.ceilDiv 0 5 == 0 ∧ Nat.ceilDiv 1 5 == 1 ∧ Nat.ceilDiv 5 1 == 5

test "Nat.ceilDiv by 0" := Nat.ceilDiv 7 0 == 0

theorem Nat.powTenPredLe ∀ (k: Nat): Nat.pow 10 (k - 1) ≤ Nat.pow 10 k := match k with
  | Zero => rfl
  | Succ k => Nat.leMulPos (Nat.pow 10 k) 10 rfl

--| `y * p + p` is at most `t * p` when `y < t`.
theorem Nat.nextMultipleLe ∀ (y: Nat) (t: Nat) (p: Nat) (h: y < t): y * p + p ≤ t * p :=
  Nat.leCongLeft (Succ y * p) (y * p + p) (t * p) (Nat.addComm p (y * p)) (Nat.leMulRight (Succ y) t p h)

theorem Nat.headLessArith ∀ (y: Nat) (t: Nat) (p: Nat) (vs: Nat) (vr: Nat) (bound: vs < p) (h: y < t): y * p + vs ≤ t * p + vr :=
  Nat.leTrans (y * p + vs) (t * p) (t * p + vr)
    (Nat.leTrans (y * p + vs) (y * p + p) (t * p) (Nat.lessLe (y * p + vs) (y * p + p) (Nat.ltAddCong (y * p) vs p bound)) (Nat.nextMultipleLe y t p h))
    (Nat.leAddRight (t * p) vr)

--| `k + (n - k) <= n` when `k <= n`, and the other way round.
theorem Nat.addSubLe ∀ (k: Nat) (n: Nat) (room: k ≤ n): k + (n - k) ≤ n :=
  Nat.leCongRight (k + (n - k)) (k + (n - k)) n (Nat.addSubCancel k n room) (Nat.leRefl (k + (n - k)))

theorem Nat.leSubAdd ∀ (k: Nat) (n: Nat) (room: k ≤ n): n ≤ (n - k) + k :=
  Nat.leCongRight n n ((n - k) + k) (Eq.trans (Eq.sym (Nat.addSubCancel k n room)) (Nat.addComm k (n - k))) (Nat.leRefl n)

theorem Nat.addSuccLeSucc ∀ (k: Nat) (w: Nat) (n: Nat) (h: k + Succ w ≤ Succ n): k + w ≤ n :=
  Nat.leCongLeft (k + Succ w) (Succ (k + w)) (Succ n) (Nat.addSucc k w) h

theorem Nat.leOfAddLe ∀ (k: Nat) (w: Nat) (n: Nat) (h: k + w ≤ n): k ≤ n := Nat.leTrans k (k + w) n (Nat.leAddRight k w) h

--| Cancelling a positive factor; doubles; stepping along a run `s .. s + c`.
theorem Nat.mulSuccCancel ∀ (b: Nat) (v: Nat) (m: Nat) (e: b * Succ m = v * Succ m): b = v :=
  Eq.trans (Eq.sym (Nat.divUnique (b * Succ m) (Succ m) b 0 rfl (Eq.sym (Nat.addZero (b * Succ m)))))
    (Eq.trans (Eq.cong (t => t / Succ m) e) (Nat.divUnique (v * Succ m) (Succ m) v 0 rfl (Eq.sym (Nat.addZero (v * Succ m)))))

theorem Nat.mulCancelLeft: ∀ (n: Nat) => 1 ≤ n → ∀ (a b: Nat) => n * a = n * b → a = b
  | Zero, h, a, b, e => cases
  | Succ m, h, a, b, e => Nat.mulSuccCancel a b m (Eq.trans (Nat.mulComm a (Succ m)) (Eq.trans e (Nat.mulComm (Succ m) b)))

--| Cancelling a nonzero factor on the right.
theorem Nat.mulRightCancel ∀ (a: Nat) (b: Nat) (c: Nat) (nz: c ≠ 0) (e: a * c = b * c): a = b := match c with
  | Zero => Void.exfalso (nz rfl)
  | Succ m => Nat.mulSuccCancel a b m e

theorem Nat.addSelfNotSelf ∀ (a: Nat) (h: 1 ≤ a) (e: a + a = a): Void :=
  Nat.lessIrrefl a (Nat.leCongRight (Succ a) (a + a) a e (Nat.leCongLeft (a + 1) (Succ a) (a + a) (Nat.addOne a) (Nat.leAddCong a 1 a h)))

theorem Nat.doubleNotOne ∀ (k: Nat) (e: k + k = 1): Void := match k with
  | Zero => Nat.zeroNotSucc 0 e
  | Succ k => Nat.succNotZero (k + k) (Eq.trans (Eq.sym (Nat.addSucc k k)) (Nat.succInjective e))

theorem Nat.posOfDouble ∀ (k n: Nat) (e: k + k = n) (h: 1 ≤ n): 1 ≤ k := match k with
  | Zero => Void.exfalso (Bool.falseNotTrue (rewrite <- e at h))
  | Succ k => rfl

theorem Nat.leNeSucc ∀ (s: Nat) (v: Nat) (h: s ≤ v) (ne: s ≠ v): Succ s ≤ v :=
  Bool.inspect (Nat.leq (Succ s) v) (u => u = True) (t => rfl)
    (f => Void.exfalso (ne (Nat.leAntisym s v h f.read)))

theorem Nat.ltAddSucc ∀ (s: Nat) (c: Nat) (b: Nat) (h: b < Succ s + c): b < s + Succ c :=
  Nat.ltCongRight b (Succ s + c) (s + Succ c) (Eq.sym (Nat.addSucc s c)) h

theorem Nat.ltSuccAdd ∀ (s: Nat) (c: Nat) (b: Nat) (h: b < s + Succ c): b < Succ s + c :=
  Nat.ltCongRight b (s + Succ c) (Succ s + c) (Nat.addSucc s c) h

theorem Nat.ltAddSuccSelf ∀ (s: Nat) (c: Nat): s < s + Succ c := Nat.ltAddSucc s c s (Nat.leAddRight s c)

theorem Nat.predLeSucc ∀ (l j: Nat) (h: l - 1 ≤ j): l ≤ Succ j := match l with
  | Zero => rfl
  | Succ l => h

--| In the run `s .. s + (n - s) - 1` means below `n`, even when `n < s`
--| (then the run is empty).
theorem Nat.ltOfRunSub ∀ (s: Nat) (d: Nat) (n: Nat) (h1: s ≤ d) (h2: d < s + (n - s)): d < n :=
  match e: Nat.leq s n with
    | True => Nat.ltCongRight d (s + (n - s)) n (Nat.addSubCancel s n e) h2
    | False =>
      Void.exfalso (Nat.lessIrrefl d (Nat.leTrans (Succ d) s d
        (Nat.ltCongRight d (s + (n - s)) s (Eq.trans (Eq.cong (t => s + t) (Nat.subEqZero n s (Nat.lessLe n s e.read))) (Nat.addZero s)) h2) h1))

--| Whether the ordering is `Less`.
def Ordering.isLess: (ordering: Ordering) → Bool
  | Less => True
  | Equal => False
  | Greater => False

--| The smaller of two numbers: `Nat.min 3 5` is 3.
def Nat.min (m: Nat) (n: Nat): Nat := if Nat.leq m n then m else n

--| The larger of two numbers: `Nat.max 3 5` is 5.
def Nat.max (m: Nat) (n: Nat): Nat := if Nat.leq m n then n else m

--| The minimum is the left number when it is at most the right.
theorem Nat.minLeft ∀ (m: Nat) (n: Nat) (h: m ≤ n): Nat.min m n = m :=
  J (b q => Bool.ifThenElse b (u => m) (u => n) = m) rfl (Eq.sym h)

theorem Nat.minRight ∀ (m: Nat) (n: Nat) (h: Nat.leq m n = False): Nat.min m n = n :=
  J (b q => Bool.ifThenElse b (u => m) (u => n) = n) rfl (Eq.sym h)

--| The maximum is the left number when the right is at most it.
theorem Nat.maxLeft ∀ (m: Nat) (n: Nat) (h: n ≤ m): Nat.max m n = m :=
  Bool.inspect (Nat.leq m n) (c => Bool.ifThenElse c (u => n) (u => m) = m) (t => Nat.leAntisym n m h t) (f => rfl)

theorem Nat.maxRight ∀ (m: Nat) (n: Nat) (h: m ≤ n): Nat.max m n = n :=
  J (c q => Bool.ifThenElse c (u => n) (u => m) = n) rfl (Eq.sym h)

theorem Nat.leMaxLeft ∀ (m: Nat) (n: Nat): m ≤ Nat.max m n :=
  Bool.inspect (Nat.leq m n) (c => m ≤ Bool.ifThenElse c (u => n) (u => m)) (t => t) (f => Nat.leRefl m)

--| The right number is at most the maximum.
theorem Nat.leMaxRight ∀ (m: Nat) (n: Nat): n ≤ Nat.max m n :=
  Bool.inspect (Nat.leq m n) (c => n ≤ Bool.ifThenElse c (u => n) (u => m)) (t => Nat.leRefl n) (f => Nat.lessLe n m f.read)

theorem Nat.leqMaxAbove ∀ (x: Nat) (a: Nat) (b: Nat) (h: Nat.leq x a = False): Nat.leq x (Nat.max a b) = Nat.leq x b :=
  Bool.inspect (Nat.leq a b) (c => Nat.leq x (Bool.ifThenElse c (u => b) (u => a)) = Nat.leq x b)
    (t => rfl)
    (f => Eq.trans h (Eq.sym (Nat.leqFalseOfLess b x (Nat.lessTrans b a x f.read h.read))))

theorem Nat.minLeLeft ∀ (m: Nat) (n: Nat): Nat.min m n ≤ m :=
  Bool.inspect (Nat.leq m n) (c => Bool.ifThenElse c (u => m) (u => n) ≤ m) (t => Nat.leRefl m) (f => Nat.lessLe n m f.read)

theorem Nat.minLeRight ∀ (m: Nat) (n: Nat): Nat.min m n ≤ n :=
  Bool.inspect (Nat.leq m n) (c => Bool.ifThenElse c (u => m) (u => n) ≤ n) (t => t) (f => Nat.leRefl n)

theorem Nat.leMin ∀ (a: Nat) (m: Nat) (n: Nat) (hm: a ≤ m) (hn: a ≤ n): a ≤ Nat.min m n :=
  Bool.inspect (Nat.leq m n) (c => a ≤ Bool.ifThenElse c (u => m) (u => n)) (t => hm) (f => hn)

theorem Nat.minSucc ∀ (m: Nat) (n: Nat): Nat.min (Succ m) (Succ n) = Succ (Nat.min m n) :=
  Bool.inspect (Nat.leq m n) (c => Bool.ifThenElse c (u => Succ m) (u => Succ n) = Succ (Bool.ifThenElse c (u => m) (u => n))) (t => rfl) (f => rfl)

--| The distance between two numbers; `(a - b) + (b - a)`, as one of them is 0.
def Nat.absDiff (m: Nat) (n: Nat): Nat := (m - n) + (n - m)

--| The distance from a number to itself is 0.
theorem Nat.absDiffSelf ∀ (m: Nat): Nat.absDiff m m = 0 :=
  Eq.trans (Eq.cong (t => t + (m - m)) (Nat.subSelf m))
    (Eq.trans (Eq.cong (t => 0 + t) (Nat.subSelf m)) rfl)

--| The distance is symmetric.
theorem Nat.absDiffComm ∀ (m: Nat) (n: Nat): Nat.absDiff m n = Nat.absDiff n m :=
  Nat.addComm (m - n) (n - m)

--| When `m <= n`, the distance is the difference `n - m`.
theorem Nat.absDiffOfLe ∀ (m: Nat) (n: Nat) (h: m ≤ n): Nat.absDiff m n = n - m :=
  Eq.trans (Eq.cong (t => t + (n - m)) (Nat.subEqZero m n h)) rfl

--| `b` to the power `exponent`: `Nat.pow 2 10` is 1024.
def Nat.pow (b: Nat): (exponent: Nat) → Nat
  | Zero => 1
  | Succ e => Nat.pow b e * b

--| The power with the base on the left, as `b * b^e`.
theorem Nat.powSucc ∀ (b: Nat) (e: Nat): Nat.pow b (Succ e) = b * Nat.pow b e := Nat.mulComm (Nat.pow b e) b

--| Adding exponents multiplies powers: `b^(e1 + e2) = b^e1 * b^e2`.
theorem Nat.powAdd ∀ (b: Nat) (e1 e2: Nat): Nat.pow b (e1 + e2) = Nat.pow b e1 * Nat.pow b e2 := match e1 with
  | Zero => Eq.sym (Nat.addZero (Nat.pow b e2))
  | Succ e1 =>
    rewrite Nat.powAdd b e1 e2, Nat.mulAssoc (Nat.pow b e1) (Nat.pow b e2) b, Nat.mulComm (Nat.pow b e2) b,
      Nat.mulAssoc (Nat.pow b e1) b (Nat.pow b e2)

theorem Nat.powSuccPos ∀ (b: Nat) (e: Nat): 0 < Nat.pow (Succ b) e := match e with
  | Zero => rfl
  | Succ e => Nat.leTrans 1 (Nat.pow (Succ b) e) (Nat.pow (Succ b) e * Succ b) (Nat.powSuccPos b e) (Nat.leMulPos (Nat.pow (Succ b) e) (Succ b) rfl)

--| Decides that a power of a positive base is never 0. So `auto` proves
--| `Nat.pow 10 k ≠ 0` (`x % Nat.pow 10 k`), and the same of a definition that
--| unfolds to such a power.
instance Nat.decPowSuccNotZero (b: Nat) (e: Nat): Decidable (Nat.pow (Succ b) e ≠ 0) :=
  Decidable.yes (Nat.nonzeroOfPos (Nat.pow (Succ b) e) (Nat.powSuccPos b e))

theorem Nat.powMono ∀ (b: Nat) (e: Nat) (f: Nat) (h: e ≤ f): Nat.pow (Succ b) e ≤ Nat.pow (Succ b) f :=
  Nat.leCongRight (Nat.pow (Succ b) e) (Nat.pow (Succ b) e * Nat.pow (Succ b) (f - e)) (Nat.pow (Succ b) f)
    (Eq.trans (Eq.sym (Nat.powAdd (Succ b) e (f - e))) (Eq.cong (t => Nat.pow (Succ b) t) (Nat.addSubCancel e f h)))
    (Nat.leMulPos (Nat.pow (Succ b) e) (Nat.pow (Succ b) (f - e)) (Nat.powSuccPos b (f - e)))

theorem Nat.addTwo ∀ (n: Nat): n + 2 = Succ (Succ n) := rewrite Nat.addSucc n 1, Nat.addOne n

--| `m == n` on numbers is `Nat.equal m n`: the test of [`Nat.decEq`].
theorem Nat.eqIsEqual ∀ (m n: Nat): (m == n) = Nat.equal m n := rfl

--| A number differs from every smaller one.
theorem Nat.equalOfLess ∀ (b v: Nat) (h: b < v): Nat.equal v b = False := match b, v with
  | Zero, Succ v => rfl
  | Succ b, Succ v => Nat.equalOfLess b v h

--| `Nat.equal` doesn't care which number comes first.
theorem Nat.equalComm ∀ (a b: Nat): Nat.equal a b = Nat.equal b a := match a, b with
  | Zero, Zero => rfl
  | Zero, Succ b => rfl
  | Succ a, Zero => rfl
  | Succ a, Succ b => Nat.equalComm a b

--| A sum is 0 only when both terms are.
theorem Nat.addEqZero ∀ (a b: Nat) (h: a + b = 0): (a = 0) ∧ (b = 0) := match a with
  | Zero => Both rfl h
  | Succ a => Void.exfalso (Nat.succNotZero (a + b) h)

theorem Nat.eqIsEqualExample: (Succ 4 == Succ 2) = (4 == 2) := Eq.trans (Nat.eqIsEqual 5 3) (Eq.sym (Nat.eqIsEqual 4 2))

theorem Nat.compareSelf ∀ (n: Nat): Nat.compare n n = Equal := match n with
  | Zero => rfl
  | Succ n => Nat.compareSelf n

--| `x < u` is "not u <= x".
theorem Nat.lessNotLe ∀ (x u: Nat): Nat.leq (Succ x) u = Bool.not (Nat.leq u x) := match x, u with
  | x, Zero => rfl
  | Zero, Succ u => rfl
  | Succ x, Succ u => Nat.lessNotLe x u

--| Dividing a bigger number by the same `d` gives a bigger quotient, for any
--| `d` (both quotients are 0 when `d` is 0).
theorem Nat.divMonoLeft ∀ (a: Nat) (b: Nat) (d: Nat) (below: a ≤ b): a / d ≤ b / d := match d with
  | Zero => rewrite Nat.divZero a in rfl
  | Succ n => Nat.leDivOfMulLe (a / Succ n) b (Succ n) (Nat.leTrans ((a / Succ n) * Succ n) a b (Nat.divMulLe a (Succ n)) below)

--| `row * width + column` with `column < width` determines `row`: the cell
--| number of a grid stored row by row divides back to its row.
theorem Nat.mulAddDivSmall ∀ (row: Nat) (width: Nat) (column: Nat) (small: column < width): (row * width + column) / width = row :=
  Nat.divUnique (row * width + column) width row column small rfl

test "Nat.divMonoLeft" := 7 / 2 ≤ 9 / 2 ∧ 7 / 0 ≤ 9 / 0
test "Nat.mulAddDivSmall" := (3 * 10 + 4) / 10 == 3
test "Nat.mulAddDivMatch" := (3 * 10 + 4 == 34) == (34 % 10 == 4 && 3 == 34 / 10)
