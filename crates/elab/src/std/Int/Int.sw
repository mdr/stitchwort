--| `Int` arithmetic for programs: the arithmetic and division laws, proved from
--| the core's definitions and `Int/Basics.sw`'s. (The sum of a list of `Int`s
--| is the generic `List.sum`.)
-- This file was the prelude's blocks of `Int` lemmas after the core's `Int`.

-- Lemmas (checkpoint 1)

theorem Int.toNatCheckedToInt ∀ (n: Nat): Int.toNatChecked (Nat.toInt n) = Some n := rfl

theorem Int.negNeg ∀ (x: Int): Int.neg (Int.neg x) = x := match x with
  | OfNat Zero => rfl
  | OfNat (Succ n) => rfl
  | NegSucc n => rfl

-- These hold by computation; stating them keeps it that way.

--| `Nat.toInt` of a sum is the sum of the `Nat.toInt`s, by computation.
theorem Int.toIntAdd ∀ (m: Nat) (n: Nat): Nat.toInt (m + n) = Int.add (Nat.toInt m) (Nat.toInt n) := rfl

theorem Int.toIntMul ∀ (m: Nat) (n: Nat): Nat.toInt (m * n) = Int.mul (Nat.toInt m) (Nat.toInt n) := rfl

theorem Int.toNatToInt ∀ (n: Nat): Int.toNat (Nat.toInt n) = n := rfl

--| An `Int` that isn't negative is the `Nat.toInt` of its `toNat`.
theorem Int.toIntToNat ∀ (z: Int) (nonneg: 0 ≤ z): Nat.toInt (Int.toNat z) = z := match z with
  | OfNat k => rfl

theorem Int.natAbsToInt ∀ (n: Nat): Int.natAbs (Nat.toInt n) = n := rfl

theorem Int.natAbsNeg ∀ (x: Int): Int.natAbs (Int.neg x) = Int.natAbs x := match x with
  | OfNat Zero => rfl
  | OfNat (Succ n) => rfl
  | NegSucc n => rfl

--| `|x|` is `x` when `x` isn't negative, and `-x` when it is (Lean's
--| `Int.natAbs_dichotomy`). `omega` splits on this for each `Int.natAbs x`
--| it meets, so a goal about sizes needs no case split by hand.
theorem Int.natAbsDichotomy ∀ (x: Int):
    (0 ≤ x ∧ Nat.toInt (Int.natAbs x) = x) ∨ (x < 0 ∧ Nat.toInt (Int.natAbs x) = 0 - x) := match x with
      | OfNat n => Inl (Both rfl rfl)
      | NegSucc n => Inr (Both rfl rfl)

-- Lemmas (checkpoint 2): division. Division is total (`x / 0 = 0`, `x % 0 =
-- x`); the lemmas that need a divisor that isn't 0 take it as an `auto`
-- argument, found as `auto` finds any fact.

--| `x.modNat d < d`; `Int.modNatLt x 100` is the dial's `x.modNat 100 < 100`.
theorem Int.modNatLt ∀ (x: Int) (d: Nat) [auto ok: d ≠ 0]: Int.modNat x d < d := match x, d with
  | x, Zero => Void.exfalso (ok rfl)
  | OfNat m, Succ n => Nat.modLess m (Succ n) (Nat.succNotZero n)
  | NegSucc m, Succ n => Nat.subLe n (m % Succ n)

--| `x % Nat.toInt d`; `auto` proves `Nat.toInt d ≠ 0` from `ok`.
theorem Int.modNatToInt ∀ (x: Int) (d: Nat) [auto ok: d ≠ 0]:
    Nat.toInt (Int.modNat x d) = x % Nat.toInt d := match x, d with
      | x, Zero => Void.exfalso (ok rfl)
      | OfNat m, Succ n => rfl
      | NegSucc m, Succ n => rfl

--| Dividing by 0 gives 0 (Lean's `Int.ediv_zero`), by computation.
theorem Int.divZero ∀ (x: Int): x / 0 = 0 := rfl

--| The remainder of dividing by 0 is the number itself (Lean's
--| `Int.emod_zero`), by computation.
theorem Int.modZero ∀ (x: Int): x % 0 = x := rfl

theorem Int.toIntDiv ∀ (n: Nat) (d: Nat):
    Nat.toInt (n / d) = Nat.toInt n / Nat.toInt d := match d with
      | Zero => Eq.cong Nat.toInt (Nat.divZero n)
      | Succ d => rfl

theorem Int.toIntMod ∀ (n: Nat) (d: Nat):
    Nat.toInt (n % d) = Nat.toInt n % Nat.toInt d := match d with
      | Zero => Eq.cong Nat.toInt (Nat.modZero n)
      | Succ d => rfl

--| A divisor that isn't 0, from a computation: for a number `d`,
--| `Nat.equal (Int.natAbs d) 0` computes to `False`. (`omega`'s facts about
--| `x % k` take it.)
theorem Int.neZeroOfNatAbs ∀ (d: Int) (h: Nat.equal (Int.natAbs d) 0 = False): d ≠ 0 :=
  zero => Nat.equalFalse (Int.natAbs d) 0 h (Eq.cong Int.natAbs zero)

--| Remainder bounds: `0 <= a % d < |d|`, for `d ≠ 0` (`a % 0` is `a`).
theorem Int.modNonneg ∀ (a d: Int) [auto ok: d ≠ 0]: 0 ≤ a % d := match a, d with
  | a, OfNat Zero => Void.exfalso (ok rfl)
  | OfNat m, OfNat (Succ n) => rfl
  | NegSucc m, OfNat (Succ n) => rfl
  | OfNat m, NegSucc n => rfl
  | NegSucc m, NegSucc n => rfl

theorem Int.modLtAbs ∀ (a d: Int) [auto ok: d ≠ 0]: a % d < Nat.toInt (Int.natAbs d) := match a, d with
  | a, OfNat Zero => Void.exfalso (ok rfl)
  | OfNat m, OfNat (Succ n) => Nat.modLess m (Succ n) (Nat.succNotZero n)
  | NegSucc m, OfNat (Succ n) => Nat.subLe n (m % Succ n)
  | OfNat m, NegSucc n => Nat.modLess m (Succ n) (Nat.succNotZero n)
  | NegSucc m, NegSucc n => Nat.subLe n (m % Succ n)

--| The division law's negative-dividend cases.
-- With `q = m / Succ n` and `r = m % Succ n`, `d * (a / d)` computes to
-- `NegSucc (q + n * Succ q)`, and adding `n - r` gives `-(m + 1)`: `Succ (q +
-- n * Succ q) - (n - r)` is `Succ m`, because `q + n * Succ q = m + (n - r)`.
theorem Int.divAddModNeg ∀ (m: Nat) (n: Nat) (q: Nat) (r: Nat) (h: m = q * Succ n + r) (hr: r ≤ n):
    Int.add (NegSucc (q + n * Succ q)) (OfNat (n - r)) = NegSucc m :=
  calc Int.add (NegSucc (q + n * Succ q)) (OfNat (n - r))
    _ = Int.subNatNatFrom (n - r) (Succ (q + n * Succ q))
      (Succ (q + n * Succ q) - (n - r)) := rfl
    _ = Int.subNatNatFrom (n - r) (Succ (q + n * Succ q)) (Succ m) :=
      Eq.cong (Int.subNatNatFrom (n - r) (Succ (q + n * Succ q)))
        (calc Succ (q + n * Succ q) - (n - r)
          _ = Succ (m + (n - r)) - (n - r) :=
            Eq.cong (t => Succ t - (n - r))
              (Eq.sym
                (calc m + (n - r)
                  _ = (q * Succ n + r) + (n - r) := Eq.cong (t => t + (n - r)) h
                  _ = q * Succ n + (r + (n - r)) := Nat.addAssoc (q * Succ n) r (n - r)
                  _ = q * Succ n + n := Eq.cong (t => q * Succ n + t) (Nat.addSubCancel r n hr)
                  _ = Succ n * q + n := Eq.cong (t => t + n) (Nat.mulComm q (Succ n))
                  _ = q + (n * q + n) := Nat.addAssoc q (n * q) n
                  _ = q + (n + n * q) := Eq.cong (t => q + t) (Nat.addComm (n * q) n)
                  _ = q + n * Succ q := Eq.cong (t => q + t) (Eq.sym (Nat.mulSucc n q))))
          _ = Succ m := Nat.addSub (Succ m) (n - r))
    _ = NegSucc m := rfl

--| The non-negative dividend, negative divisor case: `Int.neg (OfNat q)`
--| only computes once `q` is split.
theorem Int.divAddModPosNeg ∀ (m: Nat) (n: Nat) (q r: Nat) (h: m = q * Succ n + r):
    Int.add (Int.mul (NegSucc n) (Int.neg (OfNat q))) (OfNat r) = OfNat m := match q with
      | Zero =>
        Eq.trans (Eq.cong (t => Int.add (Int.neg (OfNat t)) (OfNat r)) (Nat.mulZero n)) (Eq.cong OfNat (Eq.sym h))
      | Succ q =>
        Eq.cong OfNat (Eq.trans (Eq.cong (t => t + r) (Nat.mulComm (Succ n) (Succ q))) (Eq.sym h))

--| The division law: `d * (a / d) + a % d = a`, for every `d` (Lean's `Int.ediv_add_emod`).
theorem Int.divAddMod ∀ (a d: Int): d * (a / d) + a % d = a := match a, d with
  | a, OfNat Zero => Int.zeroAdd a
  | OfNat m, OfNat (Succ n) =>
    Eq.cong OfNat (Eq.trans (Eq.cong (t => t + m % Succ n) (Nat.mulComm (Succ n) (m / Succ n)))
      (Eq.sym (Nat.divModEq m (Succ n))))
  | NegSucc m, OfNat (Succ n) =>
    Int.divAddModNeg m n (m / Succ n) (m % Succ n) (Nat.divModEq m (Succ n))
      (Nat.modLess m (Succ n) (Nat.succNotZero n))
  | OfNat m, NegSucc n =>
    Int.divAddModPosNeg m n (m / Succ n) (m % Succ n) (Nat.divModEq m (Succ n))
  | NegSucc m, NegSucc n =>
    Int.divAddModNeg m n (m / Succ n) (m % Succ n) (Nat.divModEq m (Succ n))
      (Nat.modLess m (Succ n) (Nat.succNotZero n))

theorem Int.subNatNatSelf ∀ (n: Nat): Int.subNatNat n n = OfNat 0 :=
  Eq.trans (Eq.cong (Int.subNatNatFrom n n) (Nat.subSelf n)) (Eq.cong OfNat (Nat.subSelf n))

theorem Int.subOfNats ∀ (m: Nat) (n: Nat): Nat.toInt m - Nat.toInt n = Int.subNatNat m n := match n with
  | Zero => Eq.trans (Eq.cong Nat.toInt (Nat.addZero m)) (Eq.sym (Int.subNatNatZeroRight m))
  | Succ n => rfl

theorem Int.negSubNatNat ∀ (m n: Nat): Int.neg (Int.subNatNat m n) = Int.subNatNat n m := match m, n with
  | Zero, Zero => rfl
  | Zero, Succ n => rfl
  | Succ m, Zero => rfl
  | Succ m, Succ n =>
    Eq.trans (Eq.cong Int.neg (Int.subNatNatSucc m n))
      (Eq.trans (Int.negSubNatNat m n) (Eq.sym (Int.subNatNatSucc n m)))

theorem Int.addNeg ∀ (a: Int): Int.add a (Int.neg a) = OfNat 0 := match a with
  | OfNat Zero => rfl
  | OfNat (Succ n) => Int.subNatNatSelf (Succ n)
  | NegSucc n => Int.subNatNatSelf (Succ n)

theorem Int.subSelf ∀ (a: Int): Int.sub a a = OfNat 0 := Int.addNeg a

theorem Int.negAdd ∀ (a b: Int): Int.neg (Int.add a b) = Int.add (Int.neg a) (Int.neg b) := match a, b with
  | OfNat Zero, OfNat Zero => rfl
  | OfNat Zero, OfNat (Succ n) => rfl
  | OfNat (Succ m), OfNat Zero => Eq.cong NegSucc (Nat.addZero m)
  | OfNat (Succ m), OfNat (Succ n) => Eq.cong NegSucc (Nat.addSucc m n)
  | OfNat Zero, NegSucc n => rfl
  | OfNat (Succ m), NegSucc n => Int.negSubNatNat (Succ m) (Succ n)
  | NegSucc m, OfNat Zero => Eq.cong OfNat (Eq.sym (Nat.addZero (Succ m)))
  | NegSucc m, OfNat (Succ n) => Int.negSubNatNat (Succ n) (Succ m)
  | NegSucc m, NegSucc n => Eq.cong (t => OfNat (Succ t)) (Eq.sym (Nat.addSucc m n))

--| A running total `p - q` of naturals: subtracting `r` adds it to `q`; and
--| `(s + q) - q` is `s`.
theorem Int.subNatNatAddNeg ∀ (p: Nat) (q: Nat) (r: Nat): Int.add (Int.subNatNat p q) (Int.neg (OfNat r)) = Int.subNatNat p (q + r) :=
  match r with
    | Zero => Eq.trans (Int.addZero (Int.subNatNat p q)) (Eq.cong (Int.subNatNat p) (Eq.sym (Nat.addZero q)))
    | Succ r => Eq.trans (Int.subNatNatAddNegSucc r p q) (Eq.cong (Int.subNatNat p) (Eq.sym (Nat.addSucc q r)))

theorem Int.toNatSubNatNat ∀ (s: Nat) (q: Nat): Int.toNat (Int.subNatNat (s + q) q) = s :=
  Eq.trans (Eq.cong (t => Int.toNat (Int.subNatNatFrom (s + q) q t)) (Nat.subEqZero q (s + q) (Nat.leAddLeft s q))) (Nat.addSub s q)

--| Integers modulo a size. The remainder `Int.modNat x d` doesn't change when
--| `d` is added to `x`, hence not for any multiple of `d`.
--| A negative remainder: `m - n` for `m <= n` is as far below 0 as `n - m` is
--| above, so `-(m+1)` is `n - m` on the dial of size `n + 1`.
theorem Int.modNatSubNatNatLe ∀ (m: Nat) (n: Nat) (h: Nat.leq m n = True):
    Int.modNat (Int.subNatNat n m) (Succ n) = n - m % Succ n :=
  Eq.trans (Eq.cong (k => Int.modNat (Int.subNatNatFrom n m k) (Succ n)) (Nat.subEqZero m n h))
    (Eq.trans (Nat.modSmall (n - m) (Succ n) (Nat.subLe n m))
      (Eq.sym (Eq.cong (x => n - x) (Nat.modSmall m (Succ n) h))))

theorem Int.modNatSubNatNatGt ∀ (n: Nat) (r: Nat):
    Int.modNat (Int.subNatNat n (Succ n + r)) (Succ n) = n - (Succ n + r) % Succ n :=
  Eq.trans (Eq.cong (k => Int.modNat (Int.subNatNatFrom n (Succ n + r) k) (Succ n)) (Nat.succAddSub n r))
    (Eq.sym (Eq.cong (x => n - x) (Nat.addModSelf (Succ n) r)))

theorem Int.modNatAddSize ∀ (x: Int) (d: Nat): Int.modNat (x + Nat.toInt d) d = Int.modNat x d := match x, d with
  | x, Zero => Eq.cong (t => Int.modNat t 0) (Int.addZero x)
  | OfNat m, Succ n =>
    Eq.trans (Eq.cong (t => t % Succ n) (Nat.addComm m (Succ n))) (Nat.addModSelf (Succ n) m)
  | NegSucc m, Succ n =>
    Bool.inspect (Nat.leq m n) (b => Int.modNat (NegSucc m + Nat.toInt (Succ n)) (Succ n) = Int.modNat (NegSucc m) (Succ n))
      (h => Eq.trans (Eq.cong (x => Int.modNat x (Succ n)) (Int.subNatNatSucc n m))
        (Int.modNatSubNatNatLe m n h))
      (f => J (y e => Int.modNat (NegSucc y + Nat.toInt (Succ n)) (Succ n) = Int.modNat (NegSucc y) (Succ n))
        (Eq.trans (Eq.cong (x => Int.modNat x (Succ n)) (Int.subNatNatSucc n (Succ n + (m - Succ n))))
          (Int.modNatSubNatNatGt n (m - Succ n)))
        (Nat.addSubCancel (Succ n) m f.read))

--| `Int.modNat (x + k * d) d = Int.modNat x d`
theorem Int.modNatAddMul ∀ (x: Int) (d: Nat) (k: Nat): Int.modNat (x + Nat.toInt (k * d)) d = Int.modNat x d :=
  match k with
    | Zero => Eq.cong (t => Int.modNat t d) (Int.addZero x)
    | Succ k =>
      Eq.trans (Eq.cong (t => Int.modNat t d) (Eq.sym (Int.addAssoc x (Nat.toInt d) (Nat.toInt (k * d)))))
        (Eq.trans (Int.modNatAddMul (x + Nat.toInt d) d k) (Int.modNatAddSize x d))

--| One click left of 0 is the top of the dial: `Int.modNat (0 - 1) (Succ h) = h`.
theorem Int.modNatNegOne ∀ (h: Nat): Int.modNat (Int.subNatNat 0 1) (Succ h) = h :=
  Eq.trans (Eq.sym (Int.modNatAddSize (Int.subNatNat 0 1) (Succ h)))
    (Eq.trans (Eq.cong (x => Int.modNat x (Succ h)) (Eq.trans (Int.subNatNatSucc h 0) (Int.subNatNatZeroRight h)))
      (Nat.modSmall h (Succ h) (Nat.leRefl h)))

-- Adding a multiple of the size, positive or negative, keeps the remainder,
-- so wrapping before adding or negating changes nothing.

--| `x - y + y` and `x + y - y` are `x`.
theorem Int.addNegAdd ∀ (x: Int) (y: Int): Int.add (Int.add x (Int.neg y)) y = x :=
  Eq.trans (Int.addAssoc x (Int.neg y) y)
    (Eq.trans (Eq.cong (Int.add x) (Int.addComm (Int.neg y) y))
      (Eq.trans (Eq.cong (Int.add x) (Int.addNeg y)) (Int.addZero x)))

theorem Int.addAddNeg ∀ (x: Int) (y: Int): Int.add (Int.add x y) (Int.neg y) = x :=
  Eq.trans (Int.addAssoc x y (Int.neg y))
    (Eq.trans (Eq.cong (Int.add x) (Int.addNeg y)) (Int.addZero x))

--| Adding a multiple of `d`, a negative one too, keeps the remainder.
theorem Int.modNatAddMulInt ∀ (x: Int) (d: Nat) (q: Int):
    Int.modNat (Int.add x (Int.mul (Nat.toInt d) q)) d = Int.modNat x d := match q with
      | OfNat k =>
        Eq.trans (Eq.cong (t => Int.modNat (Int.add x (OfNat t)) d) (Nat.mulComm d k))
          (Int.modNatAddMul x d k)
      | NegSucc k =>
        Eq.trans (Eq.sym (Int.modNatAddMul (Int.add x (Int.neg (OfNat (d * Succ k)))) d (Succ k)))
          (Eq.cong (t => Int.modNat t d)
            (Eq.trans (Eq.cong (t => Int.add (Int.add x (Int.neg (OfNat (d * Succ k)))) (OfNat t)) (Nat.mulComm (Succ k) d))
              (Int.addNegAdd x (OfNat (d * Succ k)))))

theorem Int.modNatSubMulInt ∀ (x: Int) (d: Nat) (q: Int):
    Int.modNat (Int.add x (Int.neg (Int.mul (Nat.toInt d) q))) d = Int.modNat x d :=
  Eq.trans (Eq.sym (Int.modNatAddMulInt (Int.add x (Int.neg (Int.mul (Nat.toInt d) q))) d q))
    (Eq.cong (t => Int.modNat t d) (Int.addNegAdd x (Int.mul (Nat.toInt d) q)))

--| The division law with the remainder as `Int.modNat`.
theorem Int.divAddModNat ∀ (x: Int) (d: Nat) [auto ok: d ≠ 0]:
    Int.add (Int.mul (Nat.toInt d) (Int.div x (Nat.toInt d))) (Nat.toInt (Int.modNat x d)) = x :=
  Eq.trans
    (Eq.cong (t => Int.add (Int.mul (Nat.toInt d) (Int.div x (Nat.toInt d))) t)
      (Int.modNatToInt x d [ok := ok]))
    (Int.divAddMod x (Nat.toInt d))

--| Only the remainder of `x` matters to the remainders of `x + y` and `-x`.
theorem Int.addSwapOf ∀ (m: Int) (r: Int) (x: Int) (y: Int) (h: Int.add m r = x): Int.add (Int.add r y) m = Int.add x y :=
  Eq.trans (Int.addComm (Int.add r y) m)
    (Eq.trans (Eq.sym (Int.addAssoc m r y)) (Eq.cong (t => Int.add t y) h))

theorem Int.modNatModAdd ∀ (x: Int) (y: Int) (d: Nat) [auto ok: d ≠ 0]:
    Int.modNat (Int.add (Nat.toInt (Int.modNat x d)) y) d = Int.modNat (Int.add x y) d :=
  Eq.trans
    (Eq.sym (Int.modNatAddMulInt (Int.add (Nat.toInt (Int.modNat x d)) y) d
      (Int.div x (Nat.toInt d))))
    (Eq.cong (t => Int.modNat t d)
      (Int.addSwapOf (Int.mul (Nat.toInt d) (Int.div x (Nat.toInt d)))
        (Nat.toInt (Int.modNat x d)) x y (Int.divAddModNat x d [ok := ok])))

theorem Int.negAddOf ∀ (m: Int) (r: Int) (x: Int) (h: Int.add m r = x): Int.add (Int.neg r) (Int.neg m) = Int.neg x :=
  Eq.trans (Int.addComm (Int.neg r) (Int.neg m)) (Eq.trans (Eq.sym (Int.negAdd m r)) (Eq.cong Int.neg h))

theorem Int.modNatModNeg ∀ (x: Int) (d: Nat) [auto ok: d ≠ 0]:
    Int.modNat (Int.neg (Nat.toInt (Int.modNat x d))) d = Int.modNat (Int.neg x) d :=
  Eq.trans
    (Eq.sym (Int.modNatSubMulInt (Int.neg (Nat.toInt (Int.modNat x d))) d
      (Int.div x (Nat.toInt d))))
    (Eq.cong (t => Int.modNat t d)
      (Int.negAddOf (Int.mul (Nat.toInt d) (Int.div x (Nat.toInt d)))
        (Nat.toInt (Int.modNat x d)) x (Int.divAddModNat x d [ok := ok])))

--| Quotient and remainder together, Euclidean as `/` and `%` are: the
--| remainder is never negative, so `Int.divMod (-7) 2` is `MkPair (-4) 1`.
--| `dividend` is the main value. `Int.divMod x 0` is `MkPair 0 x`.
def Int.divMod (dividend: Int) (divisor: Int): Pair Int Int := MkPair (dividend / divisor) (dividend % divisor)

test "Int.divMod" := Int.divMod (-7) 2 == MkPair (-4) 1 ∧ Int.divMod 7 (-2) == MkPair (-3) 1 ∧ Int.divMod (-7) (-2) == MkPair 4 1

-- Lemmas (checkpoint 3): `a + (b - a) = b`, multiplication's laws, and
-- casting a sum. Everything here is by cases on the constructors or by
-- induction, through `Nat`'s lemmas.

theorem Int.addSubCancel ∀ (a: Int) (b: Int): a + (b - a) = b :=
  Eq.trans (Eq.cong (Int.add a) (Int.addComm b (Int.neg a)))
    (Eq.trans (Eq.sym (Int.addAssoc a (Int.neg a) b))
      (Eq.trans (Eq.cong (t => Int.add t b) (Int.addNeg a)) (Int.zeroAdd b)))

theorem Int.mulComm ∀ (a b: Int): Int.mul a b = Int.mul b a := match a, b with
  | OfNat m, OfNat n => Eq.cong OfNat (Nat.mulComm m n)
  | OfNat m, NegSucc n => Eq.cong (t => Int.neg (OfNat t)) (Nat.mulComm m (Succ n))
  | NegSucc m, OfNat n => Eq.cong (t => Int.neg (OfNat t)) (Nat.mulComm (Succ m) n)
  | NegSucc m, NegSucc n => Eq.cong OfNat (Nat.mulComm (Succ m) (Succ n))

theorem Int.mulZero ∀ (a: Int): Int.mul a (OfNat 0) = OfNat 0 := match a with
  | OfNat m => Eq.cong OfNat (Nat.mulZero m)
  | NegSucc m => Eq.cong (t => Int.neg (OfNat t)) (Nat.mulZero (Succ m))

-- Distributivity. Multiplying by a natural number `k` keeps the difference
-- `m - n` of two naturals: `k * (m - n) = k * m - k * n`.

theorem Int.subNatNatZeroLeft ∀ (q: Nat): Int.subNatNat 0 q = Int.neg (OfNat q) := match q with
  | Zero => rfl
  | Succ q => rfl

theorem Int.subNatNatAddCancel ∀ (p: Nat) (q: Nat) (k: Nat): Int.subNatNat (k + p) (k + q) = Int.subNatNat p q :=
  match k with
    | Zero => rfl
    | Succ k => Eq.trans (Int.subNatNatSucc (k + p) (k + q)) (Int.subNatNatAddCancel p q k)

theorem Int.ofNatMulSubNatNat ∀ (k: Nat) (m n: Nat):
    Int.mul (OfNat k) (Int.subNatNat m n) = Int.subNatNat (k * m) (k * n) := match m, n with
      | Zero, Zero => Eq.trans (Eq.cong OfNat (Nat.mulZero k)) (Eq.sym (Int.subNatNatSelf (k * 0)))
      | Zero, Succ n =>
        Eq.sym (Eq.trans (Eq.cong (t => Int.subNatNat t (k * Succ n)) (Nat.mulZero k)) (Int.subNatNatZeroLeft (k * Succ n)))
      | Succ m, Zero =>
        Eq.trans (Eq.cong (Int.mul (OfNat k)) (Int.subNatNatZeroRight (Succ m)))
          (Eq.sym (Eq.trans (Eq.cong (t => Int.subNatNat (k * Succ m) t) (Nat.mulZero k)) (Int.subNatNatZeroRight (k * Succ m))))
      | Succ m, Succ n =>
        Eq.trans (Eq.cong (Int.mul (OfNat k)) (Int.subNatNatSucc m n))
          (Eq.trans (Int.ofNatMulSubNatNat k m n)
            (Eq.sym (Eq.trans (Eq.cong (t => Int.subNatNat t (k * Succ n)) (Nat.mulSucc k m))
              (Eq.trans (Eq.cong (t => Int.subNatNat (k + k * m) t) (Nat.mulSucc k n))
                (Int.subNatNatAddCancel (k * m) (k * n) k)))))

theorem Int.addNegOfNat ∀ (p: Nat) (q: Nat): Int.add (OfNat p) (Int.neg (OfNat q)) = Int.subNatNat p q := match q with
  | Zero => Eq.trans (Int.addZero (OfNat p)) (Eq.sym (Int.subNatNatZeroRight p))
  | Succ q => rfl

theorem Int.mulNegSucc ∀ (k: Nat) (x: Int): Int.mul (NegSucc k) x = Int.neg (Int.mul (OfNat (Succ k)) x) :=
  match x with
    | OfNat n => rfl
    | NegSucc n => Eq.sym (Int.negNeg (OfNat (Succ k * Succ n)))

theorem Int.ofNatMulAdd ∀ (k: Nat) (b c: Int):
    Int.mul (OfNat k) (Int.add b c) = Int.add (Int.mul (OfNat k) b) (Int.mul (OfNat k) c) := match b, c with
      | OfNat m, OfNat n => Eq.cong OfNat (Nat.mulDistribLeft k m n)
      | OfNat m, NegSucc n =>
        Eq.trans (Int.ofNatMulSubNatNat k m (Succ n)) (Eq.sym (Int.addNegOfNat (k * m) (k * Succ n)))
      | NegSucc m, OfNat n =>
        Eq.trans (Int.ofNatMulSubNatNat k n (Succ m))
          (Eq.trans (Eq.sym (Int.addNegOfNat (k * n) (k * Succ m))) (Int.addComm (OfNat (k * n)) (Int.neg (OfNat (k * Succ m)))))
      | NegSucc m, NegSucc n =>
        Eq.trans (Eq.cong (t => Int.neg (OfNat (k * t))) (Eq.sym (Eq.cong Succ (Nat.addSucc m n))))
          (Eq.trans (Eq.cong (t => Int.neg (OfNat t)) (Nat.mulDistribLeft k (Succ m) (Succ n)))
            (Int.negAdd (OfNat (k * Succ m)) (OfNat (k * Succ n))))

theorem Int.mulDistribLeft ∀ (a b c: Int): Int.mul a (Int.add b c) = Int.add (Int.mul a b) (Int.mul a c) :=
  match a with
    | OfNat k => Int.ofNatMulAdd k b c
    | NegSucc k =>
      Eq.trans (Int.mulNegSucc k (Int.add b c))
        (Eq.trans (Eq.cong Int.neg (Int.ofNatMulAdd (Succ k) b c))
          (Eq.trans (Int.negAdd (Int.mul (OfNat (Succ k)) b) (Int.mul (OfNat (Succ k)) c))
            (Eq.sym (Eq.trans (Eq.cong (t => Int.add t (Int.mul (NegSucc k) c)) (Int.mulNegSucc k b))
              (Eq.cong (Int.add (Int.neg (Int.mul (OfNat (Succ k)) b))) (Int.mulNegSucc k c))))))

theorem Int.mulDistribRight ∀ (a: Int) (b: Int) (c: Int): Int.mul (Int.add a b) c = Int.add (Int.mul a c) (Int.mul b c) :=
  Eq.trans (Int.mulComm (Int.add a b) c)
    (Eq.trans (Int.mulDistribLeft c a b)
      (Eq.trans (Eq.cong (t => Int.add t (Int.mul c b)) (Int.mulComm c a))
        (Eq.cong (Int.add (Int.mul a c)) (Int.mulComm c b))))

theorem Int.mulCommExample: (-3) * 4 = 4 * (-3) := rfl

-- Lemmas (checkpoint 4): order. `0 <= x` is `Int.leq 0 x = True`, which
-- computes to `True` exactly for an `OfNat`, so these are by cases. They are
-- what `omega`'s soundness proof needs (docs/proposals/omega.md §6.6): sums and
-- natural multiples of non-negative numbers are non-negative, a difference
-- `n - m` of naturals is when `m <= n`, and dividing by a positive number and
-- rounding down keeps `0 <= c + d * s`.

theorem Int.addNonneg ∀ (a b: Int) (ha: 0 ≤ a) (hb: 0 ≤ b): 0 ≤ a + b := match a, b with
  | OfNat m, OfNat n => rfl

theorem Int.mulNonneg ∀ (a b: Int) (ha: 0 ≤ a) (hb: 0 ≤ b): 0 ≤ a * b := match a, b with
  | OfNat m, OfNat n => rfl

theorem Int.notNonnegOfIsNeg ∀ (c: Int) (n1: Int.isNeg c = True) (h: 0 ≤ c): Void := match c with
  | NegSucc n => Bool.falseNotTrue h

theorem Int.zeroMul ∀ (a: Int): Int.mul (OfNat 0) a = OfNat 0 := match a with
  | OfNat n => rfl
  | NegSucc n => rfl

theorem Int.negOneMul ∀ (a: Int): Int.mul (NegSucc 0) a = Int.neg a :=
  Eq.trans (Int.mulNegSucc 0 a) (Eq.cong Int.neg (Int.oneMul a))

theorem Int.addAddSwap ∀ (a: Int) (b: Int) (c: Int) (d: Int): (a + b) + (c + d) = (a + c) + (b + d) :=
  calc (a + b) + (c + d)
    _ = a + (b + (c + d)) := Int.addAssoc a b (c + d)
    _ = a + ((b + c) + d) := Eq.cong (Int.add a) (Eq.sym (Int.addAssoc b c d))
    _ = a + ((c + b) + d) := Eq.cong (t => a + (t + d)) (Int.addComm b c)
    _ = a + (c + (b + d)) := Eq.cong (Int.add a) (Int.addAssoc c b d)
    _ = (a + c) + (b + d) := Eq.sym (Int.addAssoc a c (b + d))

theorem Int.subNonnegOfLe ∀ (m: Nat) (n: Nat) (h: m ≤ n): 0 ≤ Nat.toInt n - Nat.toInt m :=
  J (y e => Int.leq (OfNat 0) y = True)
    (J (k e => Int.leq (OfNat 0) (Int.subNatNatFrom n m k) = True) rfl (Eq.sym (Nat.subEqZero m n h)))
    (Eq.sym (Int.subOfNats n m))

--| If `0 <= v` is false, then `0 <= -1 - v`: the two sides of a case split
--| on a whole number.
theorem Int.negOneSubNonneg ∀ (v: Int) (h: Int.leq (OfNat 0) v = False): 0 ≤ Int.add (NegSucc 0) (Int.neg v) :=
  match v with
    | NegSucc n =>
      J (y e => Int.leq (OfNat 0) y = True) rfl
        (Eq.sym (Eq.trans (Int.subNatNatSucc n 0) (Int.subNatNatZeroRight n)))

--| `0 <= (d + 1) * y + r` with `r <= d` means `0 <= y`: a negative `y` makes
--| the product at most `-(d + 1)`, which `r` can't make up.
theorem Int.nonnegOfMulAddSmall ∀ (d: Nat) (r: Nat) (hr: r ≤ d) (y: Int) (h: 0 ≤ OfNat (Succ d) * y + OfNat r): 0 ≤ y :=
  match y with
    | OfNat n => rfl
    | NegSucc n =>
      Void.exfalso (Bool.falseNotTrue
        (rewrite Nat.subSuccRight r (Succ (n + d * Succ n))
          (Nat.leTrans r d (n + d * Succ n) hr
            (Nat.leTrans d (d * Succ n) (n + d * Succ n)
              (rewrite Nat.mulSucc d n in Nat.leAddRight d (d * n))
              (Nat.leAddLeft n (d * Succ n))))
          at h))

theorem Int.nonnegOfMulAddMod ∀ (d: Nat): ∀ (m: Int) => 0 ≤ m → m < OfNat (Succ d) → ∀ (y: Int) => 0 ≤ OfNat (Succ d) * y + m → 0 ≤ y
  | OfNat r, hm, hd, y, h => Int.nonnegOfMulAddSmall d r hd y h
  | NegSucc r, hm, hd, y, h => cases

theorem Int.mulAddAddMul ∀ (d: Int) (q: Int) (m: Int) (s: Int): (d * q + m) + d * s = d * (q + s) + m :=
  calc (d * q + m) + d * s
    _ = d * q + (m + d * s) := Int.addAssoc (d * q) m (d * s)
    _ = d * q + (d * s + m) := Eq.cong (Int.add (d * q)) (Int.addComm m (d * s))
    _ = (d * q + d * s) + m := Eq.sym (Int.addAssoc (d * q) (d * s) m)
    _ = d * (q + s) + m := Eq.cong (t => Int.add t m) (Eq.sym (Int.mulDistribLeft d q s))

--| Dividing by a positive `d` and rounding down: from `0 <= c + d * s`,
--| `0 <= c / d + s` (`/` by a positive number is floor division). The floor is
--| what turns `2 * x - 1 >= 0` into `x - 1 >= 0`; rounding toward zero would
--| give the weaker `x >= 0`, and rounding up would be wrong.
theorem Int.divFloorNonneg ∀ (d: Nat) (c: Int) (s: Int) (h: 0 ≤ c + OfNat (Succ d) * s): 0 ≤ c / OfNat (Succ d) + s :=
  Int.nonnegOfMulAddMod d (c % OfNat (Succ d)) (Int.modNonneg c (OfNat (Succ d))) (Int.modLtAbs c (OfNat (Succ d))) (c / OfNat (Succ d) + s)
    (J (z p => Int.leq (OfNat 0) z = True) h
      (Eq.trans (Eq.cong (t => Int.add t (OfNat (Succ d) * s)) (Eq.sym (Int.divAddMod c (OfNat (Succ d)))))
        (Int.mulAddAddMul (OfNat (Succ d)) (c / OfNat (Succ d)) (c % OfNat (Succ d)) s)))

--| `2 * x - 1 >= 0` gives `x - 1 >= 0`, at `x = 1`.
theorem Int.divFloorNonnegExample: 0 ≤ (-1) / 2 + 1 := Int.divFloorNonneg 1 (-1) 1 rfl

test "Int.divFloorNonneg rounds down" := (-1) / 2 == (-1: Int) ∧ (-3) / 2 == (-2: Int) ∧ 3 / 2 == (1: Int)
