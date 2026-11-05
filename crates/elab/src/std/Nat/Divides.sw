--| Divisibility: `Nat.divides` and its lemmas, and the remainder by a divisor
--| of the modulus.
-- A file of its own, so that programs using only `Nat` arithmetic don't check
-- these.

--| `x % len % k = x % k` when `len` is a multiple of `k`.
theorem Nat.modModOfMul (x: Nat) (len: Nat) (k: Nat) (t: Nat) [auto hl: len ≠ 0] [auto hk: k ≠ 0] (e: len = t * k): x % len % k = x % k :=
  Eq.sym (calc x % k
    _ = (x % len + (x / len) * len) % k := Eq.cong (y => y % k) (Eq.trans (Nat.divModEq x len hl) (Nat.addComm ((x / len) * len) (x % len)))
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

theorem Nat.dividesMul: (d: Nat) → (t: Nat) → Nat.divides d (t * d) = True
  | Zero, t => Decidable.toBoolOf (Nat.decEq (t * 0) 0) (Nat.mulZero t)
  | Succ d, t => Decidable.toBoolOf (Nat.decEq ((t * Succ d) % Succ d) 0) (Nat.modAddMul 0 t (Succ d))

theorem Nat.dividesSelf (d: Nat): Nat.divides d d = True := J (y q => Nat.divides d y = True) (Nat.dividesMul d 1) (Nat.addZero d)

theorem Nat.dividesElim (goal: Prop): (d: Nat) → (n: Nat) → Nat.divides d n = True → ((t: Nat) → n = t * d → goal) → goal
  | Zero, n, h, k => k 0 (Decidable.toBoolSound (Nat.decEq n 0) h)
  | Succ d, n, h, k =>
    k (n / Succ d)
      (calc n
        _ = (n / Succ d) * Succ d + n % Succ d := Nat.divModEq n (Succ d) (Nat.succNotZero d)
        _ = (n / Succ d) * Succ d + 0 := Eq.cong (r => (n / Succ d) * Succ d + r) (Decidable.toBoolSound (Nat.decEq (n % Succ d) 0) h)
        _ = (n / Succ d) * Succ d := Nat.addZero ((n / Succ d) * Succ d))

--| A number from 1 up is divided by nothing bigger than itself.
theorem Nat.dividesSmall: (d: Nat) → (n: Nat) → 1 ≤ n → n < d → Nat.divides d n = False
  | Zero, n, h1, h2 => Void.exfalso (Bool.falseNotTrue h2)
  | Succ d, n, h1, h2 =>
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
theorem Nat.divLtSucc (m: Nat) (k: Nat) [auto ok: k ≠ 0] (h: 1 < k): Succ m / k < Succ m :=
  Nat.divLeOfLtMul (Succ m) m k (omega [Nat.leMulRight 2 k (Succ m) h, Nat.mulComm k (Succ m)])

theorem Nat.divLt (n: Nat) (k: Nat) [auto ok: k ≠ 0] (h0: 0 < n) (h1: 1 < k): n / k < n :=
  match n with
    | Zero => Void.exfalso (Bool.falseNotTrue h0)
    | Succ m => Nat.divLtSucc m k h1

--| A product is 0 only when a factor is (Lean's `Nat.mul_eq_zero`).
theorem Nat.mulEqZero: (m: Nat) → (n: Nat) → m * n = 0 → (m = 0) ∨ (n = 0)
  | Zero, n, h => Inl rfl
  | Succ m, Zero, h => Inr rfl
  | Succ m, Succ n, h => omega [Nat.leMulPos (Succ m) (Succ n) (omega)]

--| A square is 0 only for 0.
theorem Nat.mulSelfZero (n: Nat) (h: n * n = 0): n = 0 :=
  match Nat.mulEqZero n n h with
    | Inl z => z
    | Inr z => z

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
      let divided := Nat.divModEq a (Succ c) (omega)
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
      let divided := Eq.cong Nat.toInt (Nat.divModEq a (Succ c) (omega))
      match Nat.gcdBezout (Succ c) (a % Succ c) [decreasing := Nat.modLt a (Succ c)] with
        | Witness s (Witness t h) =>
          rewrite Nat.gcdStep a c in
          Witness t (Witness (s - t * (a / Succ c).toInt) (ring [h, t * divided]))
