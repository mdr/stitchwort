-- `Nat` arithmetic and its lemmas. This file was the prelude's arithmetic,
-- division and number-helper blocks after the core's division primitives.

-- Arithmetic lemmas: addition, multiplication, order and subtraction facts proved
-- by induction, then the division law and `n % d < d`.

theorem Nat.addZero: (n: Nat) -> n + 0 = n
  | Zero => rfl
  | Succ n => Eq.cong Succ (Nat.addZero n)

theorem Nat.addSucc: (n: Nat) -> (m: Nat) -> n + Succ m = Succ (n + m)
  | Zero, m => rfl
  | Succ n, m => Eq.cong Succ (Nat.addSucc n m)

theorem Nat.addComm: (m: Nat) -> (n: Nat) -> m + n = n + m
  | Zero, n => Eq.sym (Nat.addZero n)
  | Succ m, n => Eq.trans (Eq.cong Succ (Nat.addComm m n)) (Eq.sym (Nat.addSucc n m))

theorem Nat.addAssoc: (a: Nat) -> (b: Nat) -> (c: Nat) -> (a + b) + c = a + (b + c)
  | Zero, b, c => rfl
  | Succ a, b, c => Eq.cong Succ (Nat.addAssoc a b c)

theorem Nat.addCancelLeft: (a: Nat) -> (b: Nat) -> (c: Nat) -> a + b = a + c -> b = c
  | Zero, b, c, h => h
  | Succ a, b, c, h => Nat.addCancelLeft a b c (Nat.succInjective (a + b) (a + c) h)

theorem Nat.mulZero: (n: Nat) -> n * 0 = 0
  | Zero => rfl
  | Succ n => Nat.mulZero n

theorem Nat.mulOne: (n: Nat) -> n * 1 = n
  | Zero => rfl
  | Succ n => Eq.cong Succ (Nat.mulOne n)

theorem Nat.mulSucc: (n: Nat) -> (m: Nat) -> n * Succ m = n + n * m
  | Zero, m => rfl
  | Succ n, m => Eq.cong Succ (Eq.trans (Eq.cong (t => m + t) (Nat.mulSucc n m)) (Eq.trans (Eq.sym (Nat.addAssoc m n (n * m))) (Eq.trans (Eq.cong (t => t + n * m) (Nat.addComm m n)) (Nat.addAssoc n m (n * m)))))

theorem Nat.mulComm: (n: Nat) -> (m: Nat) -> n * m = m * n
  | Zero, m => Eq.sym (Nat.mulZero m)
  | Succ n, m => Eq.trans (Eq.cong (t => m + t) (Nat.mulComm n m)) (Eq.sym (Nat.mulSucc m n))

theorem Nat.mulDistribRight: (a: Nat) -> (b: Nat) -> (c: Nat) -> (a + b) * c = a * c + b * c
  | Zero, b, c => rfl
  | Succ a, b, c => Eq.trans (Eq.cong (t => c + t) (Nat.mulDistribRight a b c)) (Eq.sym (Nat.addAssoc c (a * c) (b * c)))

theorem Nat.mulDistribLeft (a: Nat) (b: Nat) (c: Nat): a * (b + c) = a * b + a * c := Eq.trans (Nat.mulComm a (b + c)) (Eq.trans (Nat.mulDistribRight b c a) (Eq.trans (Eq.cong (t => t + c * a) (Nat.mulComm b a)) (Eq.cong (t => a * b + t) (Nat.mulComm c a))))

theorem Nat.mulAssoc: (a: Nat) -> (b: Nat) -> (c: Nat) -> (a * b) * c = a * (b * c)
  | Zero, b, c => rfl
  | Succ a, b, c => Eq.trans (Nat.mulDistribRight b (a * b) c) (Eq.cong (t => b * c + t) (Nat.mulAssoc a b c))

theorem Nat.leRefl: (n: Nat) -> n <= n
  | Zero => rfl
  | Succ n => Nat.leRefl n

theorem Nat.zeroLe (n: Nat): 0 <= n := rfl

theorem Nat.leAntisym: (a: Nat) -> (b: Nat) -> a <= b -> b <= a -> a = b
  | Zero, Zero, h1, h2 => rfl
  | Zero, Succ b, h1, h2 => Void.exfalso (Bool.falseNotTrue h2)
  | Succ a, Zero, h1, h2 => Void.exfalso (Bool.falseNotTrue h1)
  | Succ a, Succ b, h1, h2 => Eq.cong Succ (Nat.leAntisym a b h1 h2)

theorem Nat.leAddRight: (n: Nat) -> (m: Nat) -> n <= n + m
  | Zero, m => rfl
  | Succ n, m => Nat.leAddRight n m

theorem Nat.leAddLeft: (n: Nat) -> (m: Nat) -> m <= n + m
  | Zero, m => Nat.leRefl m
  | Succ n, m => Nat.leTrans m (n + m) (Succ (n + m)) (Nat.leAddLeft n m) (Nat.leSucc (n + m))

theorem Nat.leqSuccSelf: (n: Nat) -> Nat.leq (Succ n) n = False
  | Zero => rfl
  | Succ n => Nat.leqSuccSelf n

theorem Nat.lessIrrefl (n: Nat): Not (n < n)
  | h => Bool.falseNotTrue (Eq.trans (Eq.sym (Nat.leqSuccSelf n)) h)

theorem Nat.leLessSucc (m: Nat) (n: Nat) (h: m <= n): m < Succ n := h

theorem Nat.subSelf: (n: Nat) -> n - n = 0
  | Zero => rfl
  | Succ n => Nat.subSelf n

theorem Nat.addSub (n: Nat): (m: Nat) -> (n + m) - m = n
  | Zero => Nat.addZero n
  | Succ m => Eq.trans (Eq.cong (t => t - Succ m) (Nat.addSucc n m)) (Nat.addSub n m)

theorem Nat.subLe: (n: Nat) -> (m: Nat) -> n - m <= n
  | n, Zero => Nat.leRefl n
  | Zero, Succ m => rfl
  | Succ n, Succ m => Nat.leTrans (n - m) n (Succ n) (Nat.subLe n m) (Nat.leSucc n)
theorem Nat.leCongLeft (a: Nat) (b: Nat) (n: Nat) (p: a = b) (h: a <= n): b <= n := J (y q => y <= n) h p

theorem Nat.leCongRight (a: Nat) (b: Nat) (n: Nat) (p: b = n) (h: a <= b): a <= n := J (y q => a <= y) h p

theorem Nat.ltCongLeft (a: Nat) (b: Nat) (n: Nat) (p: a = b) (h: a < n): b < n := J (y q => y < n) h p

theorem Nat.ltCongRight (a: Nat) (b: Nat) (n: Nat) (p: b = n) (h: a < b): a < n := J (y q => a < y) h p

theorem Nat.leAddCong: (d: Nat) -> (a: Nat) -> (b: Nat) -> a <= b -> d + a <= d + b
  | Zero, a, b, h => h
  | Succ d, a, b, h => Nat.leAddCong d a b h

theorem Nat.ltAddCong: (d: Nat) -> (a: Nat) -> (b: Nat) -> a < b -> d + a < d + b
  | Zero, a, b, h => h
  | Succ d, a, b, h => Nat.ltAddCong d a b h

theorem Nat.leMulRight: (a: Nat) -> (b: Nat) -> (c: Nat) -> a <= b -> a * c <= b * c
  | Zero,   b,      c, h => rfl
  | Succ a, Zero,   c, h => Void.exfalso (Bool.falseNotTrue h)
  | Succ a, Succ b, c, h => Nat.leAddCong c (a * c) (b * c) (Nat.leMulRight a b c h)

theorem Nat.leMulPos (x: Nat): (y: Nat) -> 0 < y -> x <= x * y
  | Zero,   h => Void.exfalso (Bool.falseNotTrue h)
  | Succ y, h => Nat.leCongRight x (x + x * y) (x * Succ y) (Eq.sym (Nat.mulSucc x y)) (Nat.leAddRight x (x * y))

theorem Nat.leAddCancel: (d: Nat) -> (a: Nat) -> (b: Nat) -> d + a <= d + b -> a <= b
  | Zero,   a, b, h => h
  | Succ d, a, b, h => Nat.leAddCancel d a b h

theorem Nat.addSubCancel: (d: Nat) -> (n: Nat) -> d <= n -> d + (n - d) = n
  | Zero, n, h => rfl
  | Succ d, Zero, h => Void.exfalso (Bool.falseNotTrue h)
  | Succ d, Succ n, h => Eq.cong Succ (Nat.addSubCancel d n h)

theorem Nat.leqFalse: (d: Nat) -> (n: Nat) -> Nat.leq d n = False -> n < d
  | Zero, n, h => Void.exfalso (Bool.trueNotFalse h)
  | Succ d, Zero, h => rfl
  | Succ d, Succ n, h => Nat.leqFalse d n h

theorem Nat.subLtAdd: (n: Nat) -> (x: Nat) -> (d: Nat) -> x <= n -> n < d + x -> n - x < d
  | n, Zero, d, hx, h => Nat.ltCongRight n (d + 0) d (Nat.addZero d) h
  | Zero, Succ x, d, hx, h => Void.exfalso (Bool.falseNotTrue hx)
  | Succ n, Succ x, d, hx, h => Nat.subLtAdd n x d hx (Nat.ltCongRight (Succ n) (d + Succ x) (Succ (d + x)) (Nat.addSucc d x) h)

theorem Nat.divFuelLeStep (fuel: Nat) (n: Nat) (d: Nat): (b: Bool) -> Nat.leq d n = b ->
    ((m: Nat) -> Nat.divFuel fuel m d * d <= m) ->
    (if b then Succ (Nat.divFuel fuel (n - d) d) else 0) * d <= n
  | True, h, ih =>
    Nat.leCongRight (d + Nat.divFuel fuel (n - d) d * d) (d + (n - d)) n (Nat.addSubCancel d n h)
      (Nat.leAddCong d (Nat.divFuel fuel (n - d) d * d) (n - d) (ih (n - d)))
  | False, h, ih => rfl

theorem Nat.divFuelLe: (fuel: Nat) -> (n: Nat) -> (d: Nat) -> Nat.divFuel fuel n d * d <= n
  | Zero, n, d => rfl
  | Succ fuel, n, d => Nat.divFuelLeStep fuel n d (Nat.leq d n) rfl (m => Nat.divFuelLe fuel m d)

theorem Nat.fuelSub: (n: Nat) -> (d: Nat) -> (f: Nat) -> Not (d = 0) -> n <= Succ f -> n - d <= f
  | n, Zero, f, ok, h => Void.exfalso (ok rfl)
  | Zero, Succ d, f, ok, h => rfl
  | Succ n, Succ d, f, ok, h => Nat.leTrans (n - d) n f (Nat.subLe n d) h

theorem Nat.divFuelBoundStep (fuel: Nat) (n: Nat) (d: Nat) (ok: Not (d = 0)) (hn: n <= Succ fuel): (b: Bool) -> Nat.leq d n = b ->
    ((m: Nat) -> m <= fuel -> m < Succ (Nat.divFuel fuel m d) * d) ->
    n < Succ (if b then Succ (Nat.divFuel fuel (n - d) d) else 0) * d
  | True, h, ih =>
    Nat.ltCongLeft (d + (n - d)) n (d + Succ (Nat.divFuel fuel (n - d) d) * d) (Nat.addSubCancel d n h)
      (Nat.ltAddCong d (n - d) (Succ (Nat.divFuel fuel (n - d) d) * d) (ih (n - d) (Nat.fuelSub n d fuel ok hn)))
  | False, h, ih =>
    Nat.ltCongRight n d (d + 0) (Eq.sym (Nat.addZero d)) (Nat.leqFalse d n h)

theorem Nat.nonzeroPos: (d: Nat) -> Not (d = 0) -> 0 < d
  | Zero, ok => Void.exfalso (ok rfl)
  | Succ d, ok => rfl

theorem Nat.nonzeroOfPos (d: Nat) (h: 1 <= d): d != 0 := e => Bool.falseNotTrue (J (y q => 1 <= y) h e)

theorem Nat.divFuelBound: (fuel: Nat) -> (n: Nat) -> (d: Nat) -> Not (d = 0) -> n <= fuel -> n < Succ (Nat.divFuel fuel n d) * d
  | Zero, Zero, d, ok, hn => Nat.ltCongRight 0 d (d + 0) (Eq.sym (Nat.addZero d)) (Nat.nonzeroPos d ok)
  | Zero, Succ n, d, ok, hn => Void.exfalso (Bool.falseNotTrue hn)
  | Succ fuel, n, d, ok, hn => Nat.divFuelBoundStep fuel n d ok hn (Nat.leq d n) rfl (m hm => Nat.divFuelBound fuel m d ok hm)

-- `(n / d) * d <= n`: the quotient never overshoots.
theorem Nat.divMulLe (n: Nat) (d: Nat) (ok: d != 0): (n / d) * d <= n := Nat.divFuelLe n n d

theorem Nat.divMod (n: Nat) (d: Nat) (ok: d != 0): n = (n / d) * d + n % d := Eq.sym (Nat.addSubCancel ((n / d) * d) n (Nat.divMulLe n d ok))

theorem Nat.modLess (n: Nat) (d: Nat) (ok: d != 0): n % d < d := Nat.subLtAdd n ((n / d) * d) d (Nat.divMulLe n d ok) (Nat.divFuelBound n n d ok (Nat.leRefl n))

-- Division with remainder is unique: if `n = q * d + r` and `r < d`, then
-- `n / d = q` and `n % d = r`. Consequences for small numbers and for adding
-- `d`, and a few facts about subtraction.
theorem Nat.notBelowAdd (d: Nat) (r: Nat) (m: Nat) (h: r < d) (e: r = d + m): Void := Nat.lessIrrefl r (Nat.leTrans (Succ r) d r h (Nat.leCongRight d (d + m) r (Eq.sym e) (Nat.leAddRight d m)))

theorem Nat.quotUnique (d: Nat): (q: Nat) -> (r: Nat) -> (q2: Nat) -> (r2: Nat) -> r < d -> r2 < d ->
    q * d + r = q2 * d + r2 -> q = q2
  | Zero,   r, Zero,   r2, h1, h2, e => rfl
  | Zero,   r, Succ k, r2, h1, h2, e => Void.exfalso (Nat.notBelowAdd d r (k * d + r2) h1 (Eq.trans e (Nat.addAssoc d (k * d) r2)))
  | Succ a, r, Zero,   r2, h1, h2, e => Void.exfalso (Nat.notBelowAdd d r2 (a * d + r) h2 (Eq.trans (Eq.sym e) (Nat.addAssoc d (a * d) r)))
  | Succ a, r, Succ b, r2, h1, h2, e =>
    Eq.cong Succ (Nat.quotUnique d a r b r2 h1 h2
      (Nat.addCancelLeft d (a * d + r) (b * d + r2) (Eq.trans (Eq.sym (Nat.addAssoc d (a * d) r)) (Eq.trans e (Nat.addAssoc d (b * d) r2)))))

theorem Nat.divUnique (n: Nat) (d: Nat) [auto ok: d != 0] (q: Nat) (r: Nat) (h: r < d) (e: n = q * d + r): n / d = q := Nat.quotUnique d (n / d) (n % d) q r (Nat.modLess n d ok) h (Eq.trans (Eq.sym (Nat.divMod n d ok)) e)

theorem Nat.modUnique (n: Nat) (d: Nat) [auto ok: d != 0] (q: Nat) (r: Nat) (h: r < d) (e: n = q * d + r): n % d = r :=
  Nat.addCancelLeft (q * d) (n % d) r
    (J (y p => y * d + n % d = q * d + r) (Eq.trans (Eq.sym (Nat.divMod n d ok)) e) (Nat.divUnique n d q r h e))

theorem Nat.modSmall (n: Nat) (d: Nat) [auto ok: d != 0] (h: n < d): n % d = n := Nat.modUnique n d 0 n h rfl

theorem Nat.divSmall (n: Nat) (d: Nat) [auto ok: d != 0] (h: n < d): n / d = 0 := Nat.divUnique n d 0 n h rfl

theorem Nat.addDivModSelf (d: Nat) (n: Nat): [auto ok: d != 0] -> d + n = Succ (n / d) * d + n % d := Eq.trans (Eq.cong (t => d + t) (Nat.divMod n d ok)) (Eq.sym (Nat.addAssoc d ((n / d) * d) (n % d)))

theorem Nat.addDivSelf (d: Nat) (n: Nat): [auto ok: d != 0] -> (d + n) / d = Succ (n / d) := Nat.divUnique (d + n) d (Succ (n / d)) (n % d) (Nat.modLess n d ok) (Nat.addDivModSelf d n)

theorem Nat.addModSelf (d: Nat) (n: Nat): [auto ok: d != 0] -> (d + n) % d = n % d := Nat.modUnique (d + n) d (Succ (n / d)) (n % d) (Nat.modLess n d ok) (Nat.addDivModSelf d n)

theorem Nat.zeroSub: (n: Nat) -> 0 - n = 0
  | Zero   => rfl
  | Succ n => rfl

theorem Nat.subEqZero: (n: Nat) -> (m: Nat) -> n <= m -> n - m = 0
  | Zero,   m,      h => Nat.zeroSub m
  | Succ n, Zero,   h => Void.exfalso (Bool.falseNotTrue h)
  | Succ n, Succ m, h => Nat.subEqZero n m h

theorem Nat.addOne (a: Nat): a + 1 = Succ a := Eq.trans (Nat.addSucc a 0) (Eq.cong Succ (Nat.addZero a))

theorem Nat.modLt (n: Nat) (d: Nat): [auto ok: d != 0] -> n % d < d := Nat.modLess n d ok

theorem Nat.modSelf (d: Nat): [auto ok: d != 0] -> d % d = 0 := Nat.modUnique d d 1 0 (Nat.nonzeroPos d ok) (Eq.sym (Eq.trans (Nat.addZero (d + 0)) (Nat.addZero d)))

theorem Nat.divOne (n: Nat): n / 1 = n := Nat.divUnique n 1 n 0 rfl (Eq.sym (Eq.trans (Nat.addZero (n * 1)) (Nat.mulOne n)))

theorem Nat.succAddSub: (m: Nat) -> (r: Nat) -> Succ (m + r) - m = Succ r
  | Zero,   r => rfl
  | Succ m, r => Nat.succAddSub m r

theorem Nat.subSuccRight: (j: Nat) -> (t: Nat) -> Succ j <= t -> t - j = Succ (t - Succ j)
  | j,      Zero,   h => Void.exfalso (Bool.falseNotTrue h)
  | Zero,   Succ t, h => rfl
  | Succ j, Succ t, h => Nat.subSuccRight j t h

theorem Nat.succSub: (t: Nat) -> Succ t - t = 1
  | Zero   => rfl
  | Succ t => Nat.succSub t

-- `n / d` is the largest `q` with `q * d <= n`.
theorem Nat.mulLeOfLeDiv (q: Nat) (n: Nat) (d: Nat) [auto ok: d != 0] (h: q <= n / d): q * d <= n :=
  Nat.leTrans (q * d) ((n / d) * d) n (Nat.leMulRight q (n / d) d h) (Nat.divMulLe n d ok)

theorem Nat.leDivOfMulLe (q: Nat) (n: Nat) (d: Nat) [auto ok: d != 0] (h: q * d <= n): q <= n / d :=
  Bool.inspect (Nat.leq q (n / d)) (c => c = True) (t => rfl)
    (f => Void.exfalso (Nat.lessIrrefl n
      (Nat.leTrans (Succ n) (Succ (n / d) * d) n (Nat.divFuelBound n n d ok (Nat.leRefl n))
        (Nat.leTrans (Succ (n / d) * d) (q * d) n (Nat.leMulRight (Succ (n / d)) q d (Nat.leqFalse q (n / d) f)) h))))

theorem Nat.divLeOfLtMul (n: Nat) (b: Nat) (d: Nat) [auto ok: d != 0] (h: n < Succ b * d): n / d <= b :=
  Bool.inspect (Nat.leq (n / d) b) (c => c = True) (t => rfl)
    (f => Void.exfalso (Nat.lessIrrefl n
      (Nat.leTrans (Succ n) (Succ b * d) n h
        (Nat.leTrans (Succ b * d) ((n / d) * d) n (Nat.leMulRight (Succ b) (n / d) d (Nat.leqFalse (n / d) b f)) (Nat.divMulLe n d ok)))))

-- `(n + n) / 2 = n`
theorem Nat.halfDouble (n: Nat): (n + n) / 2 = n :=
  Nat.divUnique (n + n) 2 n 0 rfl (Eq.sym (Eq.trans (Nat.addZero (n * 2)) (Eq.trans (Nat.mulSucc n 1) (Eq.cong (t => n + t) (Nat.mulOne n)))))

-- Remainders and shifts. A multiple of `d` can be added or dropped without
-- changing the remainder, and a sum can be reduced early.
theorem Nat.addMulDivMod (a: Nat) (b: Nat) (d: Nat) [auto ok: d != 0]: a + b * d = (a / d + b) * d + a % d :=
  Eq.trans (Eq.cong (t => t + b * d) (Nat.divMod a d ok))
    (Eq.trans (Nat.addAssoc ((a / d) * d) (a % d) (b * d))
      (Eq.trans (Eq.cong (t => (a / d) * d + t) (Nat.addComm (a % d) (b * d)))
        (Eq.trans (Eq.sym (Nat.addAssoc ((a / d) * d) (b * d) (a % d)))
          (Eq.cong (t => t + a % d) (Eq.sym (Nat.mulDistribRight (a / d) b d))))))

-- `(a + b * d) % d = a % d`
theorem Nat.modAddMul (a: Nat) (b: Nat) (d: Nat) [auto ok: d != 0]: (a + b * d) % d = a % d :=
  Nat.modUnique (a + b * d) d (a / d + b) (a % d) (Nat.modLess a d ok) (Nat.addMulDivMod a b d)

-- `(a + b * d) / d = a / d + b`
theorem Nat.divAddMul (a: Nat) (b: Nat) (d: Nat) [auto ok: d != 0]: (a + b * d) / d = a / d + b :=
  Nat.divUnique (a + b * d) d (a / d + b) (a % d) (Nat.modLess a d ok) (Nat.addMulDivMod a b d)

-- `a % d % d = a % d`
theorem Nat.modMod (a: Nat) (d: Nat) [auto ok: d != 0]: a % d % d = a % d := Nat.modSmall (a % d) d (Nat.modLess a d ok)

-- `(a % d + b) % d = (a + b) % d`: reducing the first summand early.
theorem Nat.modAddMod (a: Nat) (b: Nat) (d: Nat) [auto ok: d != 0]: (a % d + b) % d = (a + b) % d :=
  Eq.sym (Eq.trans
    (Eq.cong (t => t % d)
      (Eq.trans (Eq.cong (t => t + b) (Nat.divMod a d ok))
        (Eq.trans (Nat.addAssoc ((a / d) * d) (a % d) b) (Nat.addComm ((a / d) * d) (a % d + b)))))
    (Nat.modAddMul (a % d + b) (a / d) d))

-- `(a + b % d) % d = (a + b) % d`: the second.
theorem Nat.addModMod (a: Nat) (b: Nat) (d: Nat) [auto ok: d != 0]: (a + b % d) % d = (a + b) % d :=
  Eq.trans (Eq.cong (t => t % d) (Nat.addComm a (b % d)))
    (Eq.trans (Nat.modAddMod b a d) (Eq.cong (t => t % d) (Nat.addComm b a)))

theorem Nat.leqFalseOfLess (a: Nat) (b: Nat) (h: a < b): Nat.leq b a = False :=
  Bool.inspect (Nat.leq b a) (c => c = False)
    (t => Void.exfalso (Nat.lessIrrefl a (Nat.leTrans (Succ a) b a h t)))
    (f => rfl)

-- `lo <= x && x <= hi`, by cases on where `x` is.
theorem Nat.betweenYes (lo: Nat) (hi: Nat) (x: Nat) (h1: lo <= x) (h2: x <= hi): (lo <= x && x <= hi) = True :=
  J (c q => Bool.ifThenElse (Decidable.toBool (Bool.decTrue c)) (u => Decidable.toBool (Bool.decTrue (Nat.leq x hi))) (u => False) = True)
    (J (c q => Decidable.toBool (Bool.decTrue c) = True) rfl (Eq.sym h2)) (Eq.sym h1)

theorem Nat.betweenBelow (lo: Nat) (hi: Nat) (x: Nat) (h: Nat.leq lo x = False): (lo <= x && x <= hi) = False :=
  J (c q => Bool.ifThenElse (Decidable.toBool (Bool.decTrue c)) (u => Decidable.toBool (Bool.decTrue (Nat.leq x hi))) (u => False) = False) rfl (Eq.sym h)

theorem Nat.betweenAbove (lo: Nat) (hi: Nat) (x: Nat) (h1: lo <= x) (h2: Nat.leq x hi = False): (lo <= x && x <= hi) = False :=
  J (c q => Bool.ifThenElse (Decidable.toBool (Bool.decTrue c)) (u => Decidable.toBool (Bool.decTrue (Nat.leq x hi))) (u => False) = False)
    (J (c q => Decidable.toBool (Bool.decTrue c) = False) rfl (Eq.sym h2)) (Eq.sym h1)

theorem Nat.betweenOver (lo: Nat) (hi: Nat) (x: Nat) (h: Nat.leq x hi = False): (lo <= x && x <= hi) = False :=
  Bool.inspect (Nat.leq lo x) (c => (lo <= x && x <= hi) = False) (t => Nat.betweenAbove lo hi x t h) (f => Nat.betweenBelow lo hi x f)

-- `lo <= x && x <= hi` once `lo <= x` is known.
theorem Nat.betweenFrom (lo: Nat) (hi: Nat) (x: Nat) (h: lo <= x): (lo <= x && x <= hi) = Nat.leq x hi :=
  J (c q => Bool.ifThenElse (Decidable.toBool (Bool.decTrue c)) (u => Decidable.toBool (Bool.decTrue (Nat.leq x hi))) (u => False) = Nat.leq x hi)
    (Bool.decTrueToBool (Nat.leq x hi)) (Eq.sym h)

-- Each end, from the whole test.
theorem Nat.betweenLo (lo: Nat) (hi: Nat) (x: Nat) (h: (lo <= x && x <= hi) = True): lo <= x :=
  Bool.inspect (Nat.leq lo x) (c => c = True) (t => rfl)
    (f => Void.exfalso (Bool.falseNotTrue (Eq.trans (Eq.sym (Nat.betweenBelow lo hi x f)) h)))

theorem Nat.betweenHi (lo: Nat) (hi: Nat) (x: Nat) (h: (lo <= x && x <= hi) = True): x <= hi :=
  Bool.inspect (Nat.leq x hi) (c => c = True) (t => rfl)
    (f => Void.exfalso (Bool.falseNotTrue (Eq.trans (Eq.sym (Nat.betweenOver lo hi x f)) h)))

-- Rounding up and down: with `d = Succ m`, `lo <= b * d` exactly when
-- `(lo + d - 1) / d <= b`, and `b * d <= hi` exactly when `b <= hi / d`.
theorem Nat.roundUpArg (lo: Nat) (m: Nat): lo + Succ m - 1 = lo + m := Eq.cong (t => t - 1) (Nat.addSucc lo m)

theorem Nat.roundUpLe (lo: Nat) (m: Nat) (b: Nat) (h: lo <= b * Succ m): (lo + Succ m - 1) / Succ m <= b :=
  Nat.leCongLeft ((lo + m) / Succ m) ((lo + Succ m - 1) / Succ m) b (Eq.cong (t => t / Succ m) (Eq.sym (Nat.roundUpArg lo m)))
    (Nat.divLeOfLtMul (lo + m) b (Succ m) (Nat.leCongLeft (m + lo) (lo + m) (m + b * Succ m) (Nat.addComm m lo) (Nat.leAddCong m lo (b * Succ m) h)))

theorem Nat.roundUpGe (lo: Nat) (m: Nat) (b: Nat) (h: (lo + Succ m - 1) / Succ m <= b): lo <= b * Succ m :=
  Nat.leTrans lo (((lo + m) / Succ m) * Succ m) (b * Succ m)
    (Nat.leAddCancel m lo (((lo + m) / Succ m) * Succ m)
      (Nat.leCongLeft (lo + m) (m + lo) (m + ((lo + m) / Succ m) * Succ m) (Nat.addComm lo m)
        (Nat.divFuelBound (lo + m) (lo + m) (Succ m) (Nat.succNotZero m) (Nat.leRefl (lo + m)))))
    (Nat.leMulRight ((lo + m) / Succ m) b (Succ m) (Nat.leCongLeft ((lo + Succ m - 1) / Succ m) ((lo + m) / Succ m) b (Eq.cong (t => t / Succ m) (Nat.roundUpArg lo m)) h))

theorem Nat.roundUpNo (lo: Nat) (m: Nat) (b: Nat) (h: Nat.leq ((lo + Succ m - 1) / Succ m) b = False): Nat.leq lo (b * Succ m) = False :=
  Bool.inspect (Nat.leq lo (b * Succ m)) (c => c = False)
    (t => Void.exfalso (Bool.falseNotTrue (Eq.trans (Eq.sym h) (Nat.roundUpLe lo m b t))))
    (f => rfl)

theorem Nat.roundDownNo (hi: Nat) (m: Nat) (b: Nat) (h: Nat.leq b (hi / Succ m) = False): Nat.leq (b * Succ m) hi = False :=
  Bool.inspect (Nat.leq (b * Succ m) hi) (c => c = False)
    (t => Void.exfalso (Bool.falseNotTrue (Eq.trans (Eq.sym h) (Nat.leDivOfMulLe b hi (Succ m) t))))
    (f => rfl)

theorem Nat.powTenPredLe: (k: Nat) -> Nat.pow 10 (k - 1) <= Nat.pow 10 k
  | Zero   => rfl
  | Succ k => Nat.leAddRight (Nat.pow 10 k) (9 * Nat.pow 10 k)

-- `y * p + p` is at most `t * p` when `y < t`.
theorem Nat.nextMultipleLe (y: Nat) (t: Nat) (p: Nat) (h: y < t): y * p + p <= t * p :=
  Nat.leCongLeft (Succ y * p) (y * p + p) (t * p) (Nat.addComm p (y * p)) (Nat.leMulRight (Succ y) t p h)

theorem Nat.headLessArith (y: Nat) (t: Nat) (p: Nat) (vs: Nat) (vr: Nat) (bound: vs < p) (h: y < t): y * p + vs <= t * p + vr :=
  Nat.leTrans (y * p + vs) (t * p) (t * p + vr)
    (Nat.leTrans (y * p + vs) (y * p + p) (t * p) (Nat.lessLe (y * p + vs) (y * p + p) (Nat.ltAddCong (y * p) vs p bound)) (Nat.nextMultipleLe y t p h))
    (Nat.leAddRight (t * p) vr)

-- `k + (n - k) <= n` when `k <= n`, and the other way round.
theorem Nat.addSubLe (k: Nat) (n: Nat) (room: k <= n): k + (n - k) <= n :=
  Nat.leCongRight (k + (n - k)) (k + (n - k)) n (Nat.addSubCancel k n room) (Nat.leRefl (k + (n - k)))

theorem Nat.leSubAdd (k: Nat) (n: Nat) (room: k <= n): n <= (n - k) + k :=
  Nat.leCongRight n n ((n - k) + k) (Eq.trans (Eq.sym (Nat.addSubCancel k n room)) (Nat.addComm k (n - k))) (Nat.leRefl n)

theorem Nat.addSuccLeSucc (k: Nat) (w: Nat) (n: Nat) (h: k + Succ w <= Succ n): k + w <= n :=
  Nat.leCongLeft (k + Succ w) (Succ (k + w)) (Succ n) (Nat.addSucc k w) h

theorem Nat.leOfAddLe (k: Nat) (w: Nat) (n: Nat) (h: k + w <= n): k <= n := Nat.leTrans k (k + w) n (Nat.leAddRight k w) h

-- Cancelling a positive factor; doubles; stepping along a run `s .. s + c`.
theorem Nat.mulSuccCancel (b: Nat) (v: Nat) (m: Nat) (e: b * Succ m = v * Succ m): b = v :=
  Eq.trans (Eq.sym (Nat.divUnique (b * Succ m) (Succ m) b 0 rfl (Eq.sym (Nat.addZero (b * Succ m)))))
    (Eq.trans (Eq.cong (t => t / Succ m) e) (Nat.divUnique (v * Succ m) (Succ m) v 0 rfl (Eq.sym (Nat.addZero (v * Succ m)))))

theorem Nat.mulCancelLeft: (n: Nat) -> 1 <= n -> (a: Nat) -> (b: Nat) -> n * a = n * b -> a = b
  | Zero,   h, a, b, e => Void.exfalso (Bool.falseNotTrue h)
  | Succ m, h, a, b, e => Nat.mulSuccCancel a b m (Eq.trans (Nat.mulComm a (Succ m)) (Eq.trans e (Nat.mulComm (Succ m) b)))

theorem Nat.addSelfNotSelf (a: Nat) (h: 1 <= a) (e: a + a = a): Void :=
  Nat.lessIrrefl a (Nat.leCongRight (Succ a) (a + a) a e (Nat.leCongLeft (a + 1) (Succ a) (a + a) (Nat.addOne a) (Nat.leAddCong a 1 a h)))

theorem Nat.doubleNotOne: (k: Nat) -> k + k = 1 -> Void
  | Zero,   e => Nat.zeroNotSucc 0 e
  | Succ k, e => Nat.succNotZero (k + k) (Eq.trans (Eq.sym (Nat.addSucc k k)) (Nat.succInjective (k + Succ k) 0 e))

theorem Nat.posOfDouble: (k: Nat) -> (n: Nat) -> k + k = n -> 1 <= n -> 1 <= k
  | Zero,   n, e, h => Void.exfalso (Bool.falseNotTrue (J (m q => Nat.leq 1 m = True) h (Eq.sym e)))
  | Succ k, n, e, h => rfl

theorem Nat.leNeSucc (s: Nat) (v: Nat) (h: s <= v) (ne: Not (s = v)): Succ s <= v :=
  Bool.inspect (Nat.leq (Succ s) v) (u => u = True) (t => rfl)
    (f => Void.exfalso (ne (Nat.leAntisym s v h (Nat.leqFalse (Succ s) v f))))

theorem Nat.ltAddSucc (s: Nat) (c: Nat) (b: Nat) (h: b < Succ s + c): b < s + Succ c :=
  Nat.ltCongRight b (Succ s + c) (s + Succ c) (Eq.sym (Nat.addSucc s c)) h

theorem Nat.ltSuccAdd (s: Nat) (c: Nat) (b: Nat) (h: b < s + Succ c): b < Succ s + c :=
  Nat.ltCongRight b (s + Succ c) (Succ s + c) (Nat.addSucc s c) h

theorem Nat.ltAddSuccSelf (s: Nat) (c: Nat): s < s + Succ c := Nat.ltAddSucc s c s (Nat.leAddRight s c)

theorem Nat.predLeSucc: (l: Nat) -> (j: Nat) -> l - 1 <= j -> l <= Succ j
  | Zero,   j, h => rfl
  | Succ l, j, h => h

-- In the run `s .. s + (n - s) - 1` means below `n`, even when `n < s`
-- (then the run is empty).
theorem Nat.ltOfRunSub (s: Nat) (d: Nat) (n: Nat) (h1: s <= d) (h2: d < s + (n - s)): d < n :=
  match e: Nat.leq s n with
    | True  => Nat.ltCongRight d (s + (n - s)) n (Nat.addSubCancel s n e) h2
    | False =>
      Void.exfalso (Nat.lessIrrefl d (Nat.leTrans (Succ d) s d
        (Nat.ltCongRight d (s + (n - s)) s (Eq.trans (Eq.cong (t => s + t) (Nat.subEqZero n s (Nat.lessLe n s (Nat.leqFalse s n e)))) (Nat.addZero s)) h2) h1))

def Ordering.isLess: Ordering -> Bool
  | Less    => True
  | Equal   => False
  | Greater => False

-- Number helpers.
def Nat.min (m: Nat) (n: Nat): Nat := if Nat.leq m n then m else n

def Nat.max (m: Nat) (n: Nat): Nat := if Nat.leq m n then n else m

theorem Nat.minLeft (m: Nat) (n: Nat) (h: m <= n): Nat.min m n = m :=
  J (b q => Bool.ifThenElse b (u => m) (u => n) = m) rfl (Eq.sym h)

theorem Nat.minRight (m: Nat) (n: Nat) (h: Nat.leq m n = False): Nat.min m n = n :=
  J (b q => Bool.ifThenElse b (u => m) (u => n) = n) rfl (Eq.sym h)

-- `max` and `min` when the order is known, and their bounds.
theorem Nat.maxLeft (m: Nat) (n: Nat) (h: n <= m): Nat.max m n = m :=
  Bool.inspect (Nat.leq m n) (c => Bool.ifThenElse c (u => n) (u => m) = m) (t => Nat.leAntisym n m h t) (f => rfl)

theorem Nat.maxRight (m: Nat) (n: Nat) (h: m <= n): Nat.max m n = n :=
  J (c q => Bool.ifThenElse c (u => n) (u => m) = n) rfl (Eq.sym h)

theorem Nat.leMaxLeft (m: Nat) (n: Nat): m <= Nat.max m n :=
  Bool.inspect (Nat.leq m n) (c => m <= Bool.ifThenElse c (u => n) (u => m)) (t => t) (f => Nat.leRefl m)

-- `max` from the right, and `x <= max a b` when `x` is above `a`.
theorem Nat.leMaxRight (m: Nat) (n: Nat): n <= Nat.max m n :=
  Bool.inspect (Nat.leq m n) (c => n <= Bool.ifThenElse c (u => n) (u => m)) (t => Nat.leRefl n) (f => Nat.lessLe n m (Nat.leqFalse m n f))

theorem Nat.leqMaxAbove (x: Nat) (a: Nat) (b: Nat) (h: Nat.leq x a = False): Nat.leq x (Nat.max a b) = Nat.leq x b :=
  Bool.inspect (Nat.leq a b) (c => Nat.leq x (Bool.ifThenElse c (u => b) (u => a)) = Nat.leq x b)
    (t => rfl)
    (f => Eq.trans h (Eq.sym (Nat.leqFalseOfLess b x (Nat.lessTrans b a x (Nat.leqFalse a b f) (Nat.leqFalse x a h)))))

theorem Nat.minLeLeft (m: Nat) (n: Nat): Nat.min m n <= m :=
  Bool.inspect (Nat.leq m n) (c => Bool.ifThenElse c (u => m) (u => n) <= m) (t => Nat.leRefl m) (f => Nat.lessLe n m (Nat.leqFalse m n f))

theorem Nat.minLeRight (m: Nat) (n: Nat): Nat.min m n <= n :=
  Bool.inspect (Nat.leq m n) (c => Bool.ifThenElse c (u => m) (u => n) <= n) (t => t) (f => Nat.leRefl n)

theorem Nat.leMin (a: Nat) (m: Nat) (n: Nat) (hm: a <= m) (hn: a <= n): a <= Nat.min m n :=
  Bool.inspect (Nat.leq m n) (c => a <= Bool.ifThenElse c (u => m) (u => n)) (t => hm) (f => hn)

theorem Nat.minSucc (m: Nat) (n: Nat): Nat.min (Succ m) (Succ n) = Succ (Nat.min m n) :=
  Bool.inspect (Nat.leq m n) (c => Bool.ifThenElse c (u => Succ m) (u => Succ n) = Succ (Bool.ifThenElse c (u => m) (u => n))) (t => rfl) (f => rfl)

-- The distance between two numbers; `(a - b) + (b - a)`, as one of them is 0.
def Nat.absDiff (m: Nat) (n: Nat): Nat := (m - n) + (n - m)

-- The distance from a number to itself is 0.
theorem Nat.absDiffSelf (m: Nat): Nat.absDiff m m = 0 :=
  Eq.trans (Eq.cong (t => t + (m - m)) (Nat.subSelf m))
    (Eq.trans (Eq.cong (t => 0 + t) (Nat.subSelf m)) rfl)

-- The distance is symmetric.
theorem Nat.absDiffComm (m: Nat) (n: Nat): Nat.absDiff m n = Nat.absDiff n m :=
  Nat.addComm (m - n) (n - m)

-- When `m <= n`, the distance is the difference `n - m`.
theorem Nat.absDiffOfLe (m: Nat) (n: Nat) (h: m <= n): Nat.absDiff m n = n - m :=
  Eq.trans (Eq.cong (t => t + (n - m)) (Nat.subEqZero m n h)) rfl

-- `Nat.pow b e` is b to the power e.
def Nat.pow (b: Nat): Nat -> Nat
  | Zero   => 1
  | Succ e => b * Nat.pow b e

-- Powers: adding exponents, positive for a positive base, growing with the
-- exponent.
theorem Nat.powAdd (b: Nat): (e1: Nat) -> (e2: Nat) -> Nat.pow b (e1 + e2) = Nat.pow b e1 * Nat.pow b e2
  | Zero,    e2 => Eq.sym (Nat.addZero (Nat.pow b e2))
  | Succ e1, e2 => Eq.trans (Eq.cong (t => b * t) (Nat.powAdd b e1 e2)) (Eq.sym (Nat.mulAssoc b (Nat.pow b e1) (Nat.pow b e2)))

theorem Nat.powSuccPos (b: Nat): (e: Nat) -> 0 < Nat.pow (Succ b) e
  | Zero   => rfl
  | Succ e => Nat.leTrans 1 (Nat.pow (Succ b) e) (Nat.pow (Succ b) e + b * Nat.pow (Succ b) e) (Nat.powSuccPos b e) (Nat.leAddRight (Nat.pow (Succ b) e) (b * Nat.pow (Succ b) e))

theorem Nat.powMono (b: Nat) (e: Nat) (f: Nat) (h: e <= f): Nat.pow (Succ b) e <= Nat.pow (Succ b) f :=
  Nat.leCongRight (Nat.pow (Succ b) e) (Nat.pow (Succ b) e * Nat.pow (Succ b) (f - e)) (Nat.pow (Succ b) f)
    (Eq.trans (Eq.sym (Nat.powAdd (Succ b) e (f - e))) (Eq.cong (t => Nat.pow (Succ b) t) (Nat.addSubCancel e f h)))
    (Nat.leMulPos (Nat.pow (Succ b) e) (Nat.pow (Succ b) (f - e)) (Nat.powSuccPos b (f - e)))

theorem Nat.addTwo (n: Nat): n + 2 = Succ (Succ n) := rewrite Nat.addSucc n 1, Nat.addOne n
