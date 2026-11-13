--| Divisibility: `Nat.divides` and its lemmas, and the remainder by a divisor
--| of the modulus.
-- A file of its own, so that programs using only `Nat` arithmetic don't check
-- these.

--| `x % len % k = x % k` when `len` is a multiple of `k`.
theorem Nat.modModOfMul (x: Nat) (len: Nat) (k: Nat) (t: Nat) (e: len = t * k): x % len % k = x % k :=
  Eq.sym (calc x % k
    _ = (x % len + (x / len) * len) % k := Eq.cong (y => y % k) (Eq.trans (Nat.divModEq x len) (Nat.addComm ((x / len) * len) (x % len)))
    _ = (x % len + (x / len * t) * k) % k
      := Eq.cong (y => (x % len + y) % k) (Eq.trans (Eq.cong (l => (x / len) * l) e) (Eq.sym (Nat.mulAssoc (x / len) t k)))
    _ = x % len % k := Nat.modAddMul (x % len) (x / len * t) k)

--| Divisibility, as a test: `Nat.divides divisor n` when `n` is `t * divisor`
--| for some `t` (so 0 divides only 0). It's a `Bool`, so taking it apart passes
--| the factor to a continuation ([`Nat.dividesElim`]), as [`List.anyRangeElim`]
--| does; `Exists Nat (t => n = t * divisor)` states it as a proposition.
def Nat.divides: (divisor: Nat) → (n: Nat) → Bool
  | Zero, n => n == 0
  | Succ divisor, n => n % Succ divisor == 0

theorem Nat.dividesExample: Nat.divides 3 12 = True := rfl

theorem Nat.dividesNotExample: Nat.divides 5 12 = False := rfl

theorem Nat.dividesMul (d t: Nat): Nat.divides d (t * d) = True :=
  match d with
    | Zero => (Nat.decEq (t * 0) 0).complete (Nat.mulZero t)
    | Succ d => (Nat.decEq ((t * Succ d) % Succ d) 0).complete (Nat.modAddMul 0 t (Succ d))

theorem Nat.dividesSelf (d: Nat): Nat.divides d d = True := J (y q => Nat.divides d y = True) (Nat.dividesMul d 1) (Nat.addZero d)

theorem Nat.dividesElim (goal: Prop): ∀ (d n: Nat) => Nat.divides d n = True → ∀ (cont: ∀ (t: Nat) => n = t * d → goal) => goal
  | Zero, n, h, k => k 0 h.read
  | Succ d, n, h, k =>
    k (n / Succ d)
      (calc n
        _ = (n / Succ d) * Succ d + n % Succ d := Nat.divModEq n (Succ d)
        _ = (n / Succ d) * Succ d + 0 := Eq.cong (r => (n / Succ d) * Succ d + r) h.read
        _ = (n / Succ d) * Succ d := Nat.addZero ((n / Succ d) * Succ d))

--| `Nat.divides` as a proposition: `d` divides `n` exactly when `n` is `t * d`
--| for some `t` (Lean's `Nat.dvd_iff_exists_eq_mul_left`).
theorem Nat.dividesIff (d: Nat) (n: Nat): Nat.divides d n = True ↔ ∃ (t: Nat) => n = t * d :=
  {
    forward = h => Nat.dividesElim (∃ (t: Nat) => n = t * d) d n h (t e => Witness t e),
    backward = found =>
      match found with
        | Witness t e => rewrite e in Nat.dividesMul d t
  }

--| `Nat.divides` is the remainder test (for 0 too, since `n % 0` is `n`).
theorem Nat.dividesMod (m: Nat) (n: Nat): Nat.divides m n = (n % m == 0) :=
  match m with
    | Zero => rewrite Nat.modZero n in rfl
    | Succ d => rfl

--| A divisor of two numbers divides their sum (Lean's `Nat.dvd_add`).
theorem Nat.dividesAdd (d: Nat) (a: Nat) (b: Nat) (ha: Nat.divides d a = True) (hb: Nat.divides d b = True): Nat.divides d (a + b) = True :=
  match Iff.forward (Nat.dividesIff d a) ha, Iff.forward (Nat.dividesIff d b) hb with
    | Witness s es, Witness t et =>
      Iff.backward (Nat.dividesIff d (a + b)) (Witness (s + t) (ring [es, et]))

--| A divisor of `n` divides every multiple `q * n` of it (Lean's
--| `Nat.dvd_mul_left_of_dvd`).
theorem Nat.dividesMulLeft (d: Nat) (n: Nat) (q: Nat) (h: Nat.divides d n = True): Nat.divides d (q * n) = True :=
  match Iff.forward (Nat.dividesIff d n) h with
    | Witness t e => Iff.backward (Nat.dividesIff d (q * n)) (Witness (q * t) (ring [q * e]))

--| Adding a multiple of the modulus leaves the remainder alone, given the
--| multiple as `z % m = 0`; [`Nat.modAddMul`] is the same with `z` written
--| `t * m`.
theorem Nat.modAddOfModZero (x: Nat) (z: Nat) (m: Nat) (h: z % m = 0): (x + z) % m = x % m :=
  calc (x + z) % m
    _ = (x + z % m) % m := Eq.sym (Nat.addModMod x z m)
    _ = (x + 0) % m := rewrite h in rfl
    _ = x % m := rewrite Nat.addZero x in rfl

--| A multiple of a number with remainder 0 has remainder 0 too.
theorem Nat.modMulOfModZero (q: Nat) (z: Nat) (m: Nat) (h: z % m = 0): (q * z) % m = 0 :=
  calc (q * z) % m
    _ = (q * (z % m)) % m := Eq.sym (Nat.mulModMod q z m)
    _ = (q * 0) % m := rewrite h in rfl
    _ = 0 := rewrite Nat.mulZero q in rfl

--| A number from 1 up is divided by nothing bigger than itself.
theorem Nat.dividesSmall (d n: Nat) (h1: 1 ≤ n) (h2: n < d): Nat.divides d n = False :=
  match d with
    | Succ d =>
      Decidable.toBoolOfNot (Nat.decEq (n % Succ d) 0)
        (e => Bool.falseNotTrue (rewrite <- Nat.modSmall n (Succ d) h2, e at h1))

theorem Nat.dividesLe (d: Nat) (n: Nat) (hn: 1 ≤ n) (h: Nat.divides d n = True): d ≤ n :=
  match e: Nat.leq d n with
    | True => rfl
    | False => Void.exfalso (Bool.trueNotFalse (Eq.trans (Eq.sym h) (Nat.dividesSmall d n hn (Nat.leqFalse d n e))))

--| The positive divisors of `n`, ascending: `Nat.divisors 12` is
--| `[1, 2, 3, 4, 6, 12]`. Every number divides 0, so there is no list to give:
--| `Nat.divisors 0` is `[]`. `n` is the main value: `n.divisors`.
def Nat.divisors (n: Nat): List Nat := List.rangeFrom n 1 |> .filter (divisor => Nat.divides divisor n)

test "Nat.divisors" := Nat.divisors 12 == [1, 2, 3, 4, 6, 12] ∧ Nat.divisors 1 == [1] ∧ Nat.divisors 13 == [1, 13]
test "Nat.divisors of zero" := Nat.divisors 0 == []

--| Dividing by 2 or more makes a positive number smaller. (`Nat.divLe n k` is
--| the plain `n / k ≤ n`, in Arith.sw.)
theorem Nat.divLtSucc (m: Nat) (k: Nat) (h: 1 < k): Succ m / k < Succ m :=
  Nat.divLeOfLtMul (Succ m) m k (omega [Nat.leMulRight 2 k (Succ m) h, Nat.mulComm k (Succ m)])

theorem Nat.divLt (n: Nat) (k: Nat) (h0: 0 < n) (h1: 1 < k): n / k < n :=
  match n with
    | Succ m => Nat.divLtSucc m k h1

--| A product is 0 only when a factor is (Lean's `Nat.mul_eq_zero`).
theorem Nat.mulEqZero (m n: Nat) (h: m * n = 0): (m = 0) ∨ (n = 0) :=
  match m, n with
    | Zero, n => Inl rfl
    | Succ m, Zero => Inr rfl
    | Succ m, Succ n => omega [Nat.leMulPos (Succ m) (Succ n) (omega)]

--| A square is 0 only for 0.
theorem Nat.mulSelfZero (n: Nat) (h: n * n = 0): n = 0 :=
  match Nat.mulEqZero n n h with
    | Inl z => z
    | Inr z => z

--| A square is 1 only for 1.
theorem Nat.mulSelfOne (n: Nat) (square: n * n = 1): n = 1 :=
  match n with
    | 0 => Void.exfalso (omega)
    | 1 => rfl
    | Succ (Succ more) => Void.exfalso (omega [Nat.leMulRight 2 (Succ (Succ more)) (Succ (Succ more)) (omega)])

--| The greatest common divisor, by Euclid's algorithm: `Nat.gcd 12 18` is 6,
--| and `Nat.gcd n 0` is `n`, so `Nat.gcd 0 0` is 0.
@[tailrec]
def Nat.gcd (a: Nat) (b: Nat): Nat
    decreasing b
:=
  match b with
    | Zero => a
    | Succ c => Nat.gcd (Succ c) (a % Succ c) [decreasing := Nat.modLt a (Succ c)]

test "Nat.gcd" := Nat.gcd 12 18 == 6 ∧ Nat.gcd 18 12 == 6 ∧ Nat.gcd 7 0 == 7 ∧ Nat.gcd 0 7 == 7 ∧ Nat.gcd 0 0 == 0 ∧ Nat.gcd 17 5 == 1

--| One step of Euclid's algorithm.
theorem Nat.gcdStep (a: Nat) (c: Nat): Nat.gcd a (Succ c) = Nat.gcd (Succ c) (a % Succ c) := rewrite Nat.gcd.unfold a (Succ c) in rfl

theorem Nat.gcdZero (a: Nat): Nat.gcd a 0 = a := rewrite Nat.gcd.unfold a 0 in rfl

--| The gcd divides both numbers (Lean's `Nat.gcd_dvd_left` and `_right`).
theorem Nat.gcdDivides (a: Nat) (b: Nat): (∃ (x: Nat) => a = x * Nat.gcd a b) ∧ (∃ (y: Nat) => b = y * Nat.gcd a b)
    decreasing b
:=
  match b with
    | Zero => Both (Witness 1 (ring)) (Witness 0 rfl)
    | Succ c =>
      let divided := Nat.divModEq a (Succ c)
      match Nat.gcdDivides (Succ c) (a % Succ c) [decreasing := Nat.modLt a (Succ c)] with
        | Both (Witness x hx) (Witness y hy) =>
          rewrite Nat.gcdStep a c in
          Both (Witness (a / Succ c * x + y) (ring [divided, a / Succ c * hx, hy])) (Witness x hx)

--| Bézout's identity: the gcd is `s * a + t * b` for some integers `s` and
--| `t` (Mathlib's `Nat.gcd_eq_gcd_ab`).
theorem Nat.gcdBezout (a: Nat) (b: Nat): ∃ (s: Int) => ∃ (t: Int) => s * a.toInt + t * b.toInt = (Nat.gcd a b).toInt
    decreasing b
:=
  match b with
    | Zero => Witness 1 (Witness 0 (ring))
    | Succ c =>
      let divided := Eq.cong Nat.toInt (Nat.divModEq a (Succ c))
      match Nat.gcdBezout (Succ c) (a % Succ c) [decreasing := Nat.modLt a (Succ c)] with
        | Witness s (Witness t h) =>
          rewrite Nat.gcdStep a c in
          Witness t (Witness (s - t * (a / Succ c).toInt) (ring [h, t * divided]))

--| `v * d + r` is `target`, for a remainder `r < d`, exactly when `target`
--| leaves remainder `r` and quotient `v`: the test a program makes to undo
--| a multiplication and an addition.
theorem Nat.mulAddDivMatch (d: Nat) (r: Nat) (small: r < d) (v: Nat) (target: Nat):
    (v * d + r == target) = (target % d == r && v == target / d) :=
  Bool.eqOf (v * d + r == target) (target % d == r && v == target / d)
    (matches =>
      let same := matches.read
      rewrite Nat.modUnique target d v r small (Eq.sym same), Nat.divUnique target d v r small (Eq.sym same)
        in Both (DecEq.refl r) (DecEq.refl v))
    (both =>
      let Both remainder quotient := both
      rewrite quotient.read, <- remainder.read, <- Nat.divModEq target d in DecEq.refl target)

--| A product of two nonzero numbers is nonzero. (`omega` doesn't multiply
--| two variables, so it needs this as a hint: `omega [Nat.mulNeZero a b ha hb]`.)
theorem Nat.mulNeZero: ∀ (a b: Nat) => a ≠ 0 → b ≠ 0 → a * b ≠ 0
  | Zero, b, aPositive, bPositive, zero => aPositive rfl
  | a, Zero, aPositive, bPositive, zero => bPositive rfl
  | Succ a, Succ b, aPositive, bPositive, zero => omega

--| Taking one `w` off a number at least `w` leaves its remainder by `w`.
theorem Nat.subModSelf (column: Nat) (width: Nat) (past: width ≤ column): (column - width) % width = column % width :=
  match width with
    | Zero => rewrite (omega: column - 0 = column) in rfl
    | Succ n =>
      let back: column - Succ n + 1 * Succ n = column := omega
      let shifted := Nat.modAddMul (column - Succ n) 1 (Succ n)
      rewrite back at shifted in Eq.sym shifted

--| Stepping a counter that wraps at `d`: from a position `a < d`, one step
--| then `n` more cross the same number of multiples of `d` as `Succ n` steps
--| from `a`. The first step crosses one (the `Bool.toNat`) exactly when it
--| lands on a multiple of `d`, that is, wraps back to 0.
theorem Nat.divSuccStep (d: Nat) (a: Nat) (h: a < d) (n: Nat):
    Bool.toNat ((a + 1) % d == 0) + ((a + 1) % d + n) / d = (a + Succ n) / d :=
  if same: Succ a = d then
    calc Bool.toNat ((a + 1) % d == 0) + ((a + 1) % d + n) / d
      _ = Succ (n / d) := rewrite (Eq.trans (Eq.cong (t => t % d) same) (Nat.modSelf d): (a + 1) % d = 0)
      _ = (d + n) / d := Eq.sym (Nat.addDivSelf d n)
      _ = (Succ a + n) / d := rewrite (omega: d = Succ a)
      _ = (a + Succ n) / d := rewrite (ring: a + Succ n = Succ a + n)
  else
    rewrite Nat.modSmall (Succ a) d (omega [same]: Succ a < d) in rfl

--| Counting backwards from the top of a dial of `Succ m` positions: the
--| position `Succ m - v` is on a multiple of `Succ m` exactly when `v` is 0.
theorem Nat.subModBeqZero (m: Nat) (v: Nat) (h: v < Succ m): ((Succ m - v) % Succ m == 0) = (v == 0) :=
  match v with
    | Zero => rewrite Nat.modSelf (Succ m)
    | Succ w => rewrite Nat.modSmall (m - w) (Succ m) omega, (omega: m - w = Succ (m - Succ w))

test "Nat.mulNeZero" := 3 * 4 != 0
test "Nat.subModSelf" := (17 - 5) % 5 == 17 % 5
test "Nat.divSuccStep" := Bool.toNat ((4 + 1) % 5 == 0) + ((4 + 1) % 5 + 7) / 5 == (4 + Succ 7) / 5
test "Nat.subModBeqZero" := ((Succ 9 - 0) % Succ 9 == 0) == (0 == 0) ∧ ((Succ 9 - 4) % Succ 9 == 0) == (4 == 0)
