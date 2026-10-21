-- `Int` arithmetic for programs: the arithmetic and division laws, and
-- `Int.modNat`, proved from the core's definitions. This file was the
-- prelude's blocks of `Int` lemmas after the core's `Int`. (The sum of a list
-- of `Int`s is the generic `List.sum`.)

-- Lemmas (checkpoint 1)

theorem Int.toNatCheckedToInt (n: Nat): Int.toNatChecked (Nat.toInt n) = Some n := rfl

theorem Int.negNeg: (x: Int) -> Int.neg (Int.neg x) = x
  | OfNat Zero     => rfl
  | OfNat (Succ n) => rfl
  | NegSucc n      => rfl

-- These hold by computation; stating them keeps it that way.
theorem Int.toIntAdd (m: Nat) (n: Nat): Nat.toInt (m + n) = Int.add (Nat.toInt m) (Nat.toInt n) := rfl

theorem Int.toIntMul (m: Nat) (n: Nat): Nat.toInt (m * n) = Int.mul (Nat.toInt m) (Nat.toInt n) := rfl

theorem Int.toNatToInt (n: Nat): Int.toNat (Nat.toInt n) = n := rfl

theorem Int.natAbsToInt (n: Nat): Int.natAbs (Nat.toInt n) = n := rfl

theorem Int.natAbsNeg: (x: Int) -> Int.natAbs (Int.neg x) = Int.natAbs x
  | OfNat Zero     => rfl
  | OfNat (Succ n) => rfl
  | NegSucc n      => rfl

-- Lemmas (checkpoint 2): division.
--
-- The divisor's proof is an `auto` argument, so at a use such as
-- `Int.divAddMod x 7` it's found the same way as in `x / 7`, and the two
-- terms match: a stuck `x % 7` keeps its proof in it.

theorem Nat.toIntNeZero (d: Nat) (ok: d != 0): Nat.toInt d != 0
  | p => ok (Int.ofNatInjective d 0 p)

-- `x.modNat d < d`; `Int.modNatLt x 100` is the dial's `x.modNat 100 < 100`.
theorem Int.modNatLt: (x: Int) -> (d: Nat) -> [auto ok: d != 0] -> Int.modNat x d < d
  | x,         Zero   => Void.exfalso (ok rfl)
  | OfNat m,   Succ n => Nat.modLess m (Succ n) (Nat.succNotZero n)
  | NegSucc m, Succ n => Nat.subLe n (m % Succ n)

-- For a variable `d`, pass `[ok2 := Nat.toIntNeZero d ok]`.
theorem Int.modNatToInt: (x: Int) -> (d: Nat) -> [auto ok: d != 0] -> [auto ok2: Nat.toInt d != 0] ->
    Nat.toInt (Int.modNat x d) = x % Nat.toInt d
  | x,         Zero   => Void.exfalso (ok rfl)
  | OfNat m,   Succ n => rfl
  | NegSucc m, Succ n => rfl

theorem Int.toIntDiv (n: Nat): (d: Nat) -> [auto ok: d != 0] -> [auto ok2: Nat.toInt d != 0] ->
    Nat.toInt (n / d) = Nat.toInt n / Nat.toInt d
  | Zero   => Void.exfalso (ok rfl)
  | Succ d => rfl

theorem Int.toIntMod (n: Nat): (d: Nat) -> [auto ok: d != 0] -> [auto ok2: Nat.toInt d != 0] ->
    Nat.toInt (n % d) = Nat.toInt n % Nat.toInt d
  | Zero   => Void.exfalso (ok rfl)
  | Succ d => rfl

-- Remainder bounds: `0 <= a % d < |d|`.
theorem Int.modNonneg: (a: Int) -> (d: Int) -> [auto ok: d != 0] -> 0 <= a % d
  | a,         OfNat Zero     => Void.exfalso (ok rfl)
  | OfNat m,   OfNat (Succ n) => rfl
  | NegSucc m, OfNat (Succ n) => rfl
  | OfNat m,   NegSucc n      => rfl
  | NegSucc m, NegSucc n      => rfl

theorem Int.modLtAbs: (a: Int) -> (d: Int) -> [auto ok: d != 0] -> a % d < Nat.toInt (Int.natAbs d)
  | a,         OfNat Zero     => Void.exfalso (ok rfl)
  | OfNat m,   OfNat (Succ n) => Nat.modLess m (Succ n) (Nat.succNotZero n)
  | NegSucc m, OfNat (Succ n) => Nat.subLe n (m % Succ n)
  | OfNat m,   NegSucc n      => Nat.modLess m (Succ n) (Nat.succNotZero n)
  | NegSucc m, NegSucc n      => Nat.subLe n (m % Succ n)

-- The division law's negative-dividend cases. With `q = m / Succ n` and
-- `r = m % Succ n`, `d * (a / d)` computes to `NegSucc (q + n * Succ q)`,
-- and adding `n - r` gives `-(m + 1)`: `Succ (q + n * Succ q) - (n - r)`
-- is `Succ m`, because `q + n * Succ q = m + (n - r)`.
theorem Int.divAddModNeg (m: Nat) (n: Nat) (q: Nat) (r: Nat) (h: m = q * Succ n + r) (hr: r <= n):
    Int.add (NegSucc (q + n * Succ q)) (OfNat (n - r)) = NegSucc m :=
  Eq.cong (Int.subNatNatFrom (n - r) (Succ (q + n * Succ q)))
    (Eq.trans
      (Eq.cong (t => Succ t - (n - r))
        (Eq.sym
          (Eq.trans (Eq.cong (t => t + (n - r)) h)
          (Eq.trans (Nat.addAssoc (q * Succ n) r (n - r))
          (Eq.trans (Eq.cong (t => q * Succ n + t) (Nat.addSubCancel r n hr))
          (Eq.trans (Eq.cong (t => t + n) (Nat.mulComm q (Succ n)))
          (Eq.trans (Nat.addAssoc q (n * q) n)
          (Eq.trans (Eq.cong (t => q + t) (Nat.addComm (n * q) n))
                    (Eq.cong (t => q + t) (Eq.sym (Nat.mulSucc n q)))))))))))
      (Nat.addSub (Succ m) (n - r)))

-- The non-negative dividend, negative divisor case: `Int.neg (OfNat q)`
-- only computes once `q` is split.
theorem Int.divAddModPosNeg (m: Nat) (n: Nat): (q: Nat) -> (r: Nat) -> m = q * Succ n + r ->
    Int.add (Int.mul (NegSucc n) (Int.neg (OfNat q))) (OfNat r) = OfNat m
  | Zero, r, h =>
    Eq.trans (Eq.cong (t => Int.add (Int.neg (OfNat t)) (OfNat r)) (Nat.mulZero n)) (Eq.cong OfNat (Eq.sym h))
  | Succ q, r, h =>
    Eq.cong OfNat (Eq.trans (Eq.cong (t => t + r) (Nat.mulComm (Succ n) (Succ q))) (Eq.sym h))

-- The division law.
theorem Int.divAddMod: (a: Int) -> (d: Int) -> [auto ok: d != 0] -> d * (a / d) + a % d = a
  | a,         OfNat Zero     => Void.exfalso (ok rfl)
  | OfNat m,   OfNat (Succ n) =>
    Eq.cong OfNat (Eq.trans (Eq.cong (t => t + m % Succ n) (Nat.mulComm (Succ n) (m / Succ n)))
      (Eq.sym (Nat.divMod m (Succ n) (Nat.succNotZero n))))
  | NegSucc m, OfNat (Succ n) =>
    Int.divAddModNeg m n (m / Succ n) (m % Succ n) (Nat.divMod m (Succ n) (Nat.succNotZero n))
      (Nat.modLess m (Succ n) (Nat.succNotZero n))
  | OfNat m,   NegSucc n      =>
    Int.divAddModPosNeg m n (m / Succ n) (m % Succ n) (Nat.divMod m (Succ n) (Nat.succNotZero n))
  | NegSucc m, NegSucc n      =>
    Int.divAddModNeg m n (m / Succ n) (m % Succ n) (Nat.divMod m (Succ n) (Nat.succNotZero n))
      (Nat.modLess m (Succ n) (Nat.succNotZero n))

theorem Int.subNatNatSelf (n: Nat): Int.subNatNat n n = OfNat 0 :=
  Eq.trans (Eq.cong (Int.subNatNatFrom n n) (Nat.subSelf n)) (Eq.cong OfNat (Nat.subSelf n))

theorem Int.subOfNats (m: Nat): (n: Nat) -> Nat.toInt m - Nat.toInt n = Int.subNatNat m n
  | Zero   => Eq.trans (Eq.cong Nat.toInt (Nat.addZero m)) (Eq.sym (Int.subNatNatZeroRight m))
  | Succ n => rfl

theorem Int.negSubNatNat: (m: Nat) -> (n: Nat) -> Int.neg (Int.subNatNat m n) = Int.subNatNat n m
  | Zero,   Zero   => rfl
  | Zero,   Succ n => rfl
  | Succ m, Zero   => rfl
  | Succ m, Succ n =>
    Eq.trans (Eq.cong Int.neg (Int.subNatNatSucc m n))
      (Eq.trans (Int.negSubNatNat m n) (Eq.sym (Int.subNatNatSucc n m)))

theorem Int.addNeg: (a: Int) -> Int.add a (Int.neg a) = OfNat 0
  | OfNat Zero     => rfl
  | OfNat (Succ n) => Int.subNatNatSelf (Succ n)
  | NegSucc n      => Int.subNatNatSelf (Succ n)

theorem Int.subSelf (a: Int): Int.sub a a = OfNat 0 := Int.addNeg a

theorem Int.negAdd: (a: Int) -> (b: Int) -> Int.neg (Int.add a b) = Int.add (Int.neg a) (Int.neg b)
  | OfNat Zero,     OfNat Zero     => rfl
  | OfNat Zero,     OfNat (Succ n) => rfl
  | OfNat (Succ m), OfNat Zero     => Eq.cong NegSucc (Nat.addZero m)
  | OfNat (Succ m), OfNat (Succ n) => Eq.cong NegSucc (Nat.addSucc m n)
  | OfNat Zero,     NegSucc n      => rfl
  | OfNat (Succ m), NegSucc n      => Int.negSubNatNat (Succ m) (Succ n)
  | NegSucc m,      OfNat Zero     => Eq.cong OfNat (Eq.sym (Nat.addZero (Succ m)))
  | NegSucc m,      OfNat (Succ n) => Int.negSubNatNat (Succ n) (Succ m)
  | NegSucc m,      NegSucc n      => Eq.cong (t => OfNat (Succ t)) (Eq.sym (Nat.addSucc m n))

-- A running total `p - q` of naturals: subtracting `r` adds it to `q`; and
-- `(s + q) - q` is `s`.
theorem Int.subNatNatAddNeg (p: Nat) (q: Nat): (r: Nat) -> Int.add (Int.subNatNat p q) (Int.neg (OfNat r)) = Int.subNatNat p (q + r)
  | Zero   => Eq.trans (Int.addZero (Int.subNatNat p q)) (Eq.cong (Int.subNatNat p) (Eq.sym (Nat.addZero q)))
  | Succ r => Eq.trans (Int.subNatNatAddNegSucc r p q) (Eq.cong (Int.subNatNat p) (Eq.sym (Nat.addSucc q r)))

theorem Int.toNatSubNatNat (s: Nat) (q: Nat): Int.toNat (Int.subNatNat (s + q) q) = s :=
  Eq.trans (Eq.cong (t => Int.toNat (Int.subNatNatFrom (s + q) q t)) (Nat.subEqZero q (s + q) (Nat.leAddLeft s q))) (Nat.addSub s q)

-- Integers modulo a size. The remainder `Int.modNat x d` doesn't change when
-- `d` is added to `x`, hence not for any multiple of `d`.
-- A negative remainder: `m - n` for `m <= n` is as far below 0 as `n - m` is
-- above, so `-(m+1)` is `n - m` on the dial of size `n + 1`.
theorem Int.modNatSubNatNatLe (m: Nat) (n: Nat) (ok: Succ n != 0) (h: Nat.leq m n = True) :
    Int.modNat (Int.subNatNat n m) (Succ n) [ok := ok] = n - m % Succ n :=
  Eq.trans (Eq.cong (k => Int.modNat (Int.subNatNatFrom n m k) (Succ n) [ok := ok]) (Nat.subEqZero m n h))
    (Eq.trans (Nat.modSmall (n - m) (Succ n) (Nat.subLe n m))
      (Eq.sym (Eq.cong (x => n - x) (Nat.modSmall m (Succ n) h))))

theorem Int.modNatSubNatNatGt (n: Nat) (r: Nat) (ok: Succ n != 0) :
    Int.modNat (Int.subNatNat n (Succ n + r)) (Succ n) [ok := ok] = n - (Succ n + r) % Succ n :=
  Eq.trans (Eq.cong (k => Int.modNat (Int.subNatNatFrom n (Succ n + r) k) (Succ n) [ok := ok]) (Nat.succAddSub n r))
    (Eq.sym (Eq.cong (x => n - x) (Nat.addModSelf (Succ n) r)))

theorem Int.modNatAddSize: (x: Int) -> (d: Nat) -> [auto ok: d != 0] -> Int.modNat (x + Nat.toInt d) d = Int.modNat x d
  | x,         Zero   => Void.exfalso (ok rfl)
  | OfNat m,   Succ n =>
    Eq.trans (Eq.cong (t => t % Succ n) (Nat.addComm m (Succ n))) (Nat.addModSelf (Succ n) m)
  | NegSucc m, Succ n =>
    Bool.inspect (Nat.leq m n) (b => Int.modNat (NegSucc m + Nat.toInt (Succ n)) (Succ n) [ok := ok] = Int.modNat (NegSucc m) (Succ n) [ok := ok])
      (h => Eq.trans (Eq.cong (x => Int.modNat x (Succ n) [ok := ok]) (Int.subNatNatSucc n m))
        (Int.modNatSubNatNatLe m n ok h))
      (f => J (y e => Int.modNat (NegSucc y + Nat.toInt (Succ n)) (Succ n) [ok := ok] = Int.modNat (NegSucc y) (Succ n) [ok := ok])
        (Eq.trans (Eq.cong (x => Int.modNat x (Succ n) [ok := ok]) (Int.subNatNatSucc n (Succ n + (m - Succ n))))
          (Int.modNatSubNatNatGt n (m - Succ n) ok))
        (Nat.addSubCancel (Succ n) m (Nat.leqFalse m n f)))

-- `Int.modNat (x + k * d) d = Int.modNat x d`
theorem Int.modNatAddMul (x: Int) (d: Nat) [auto ok: d != 0]: (k: Nat) -> Int.modNat (x + Nat.toInt (k * d)) d = Int.modNat x d
  | Zero   => Eq.cong (t => Int.modNat t d [ok := ok]) (Int.addZero x)
  | Succ k =>
    Eq.trans (Eq.cong (t => Int.modNat t d [ok := ok]) (Eq.sym (Int.addAssoc x (Nat.toInt d) (Nat.toInt (k * d)))))
      (Eq.trans (Int.modNatAddMul (x + Nat.toInt d) d k) (Int.modNatAddSize x d))

-- One click left of 0 is the top of the dial: `Int.modNat (0 - 1) (Succ h) = h`.
theorem Int.modNatNegOne (h: Nat): Int.modNat (Int.subNatNat 0 1) (Succ h) = h :=
  Eq.trans (Eq.sym (Int.modNatAddSize (Int.subNatNat 0 1) (Succ h)))
    (Eq.trans (Eq.cong (x => Int.modNat x (Succ h) [ok := Nat.succNotZero h]) (Eq.trans (Int.subNatNatSucc h 0) (Int.subNatNatZeroRight h)))
      (Nat.modSmall h (Succ h) (Nat.leRefl h)))
