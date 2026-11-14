--| Integer functions that were in the core: the division variants and others
--| no compiler path names.
-- (docs/proposals/prelude-slim.md stage 3)
-- This file depends on the core alone, so a program that divides doesn't also
-- load the lemmas in `Int.sw`.

--| The number as an `Int`: `(5: Nat).toInt` is `5`.
def Nat.toInt (n: Nat): Int := OfNat n

--| `Nat.toInt` of a nonzero number is nonzero: `auto` uses it to prove the
--| divisor of `x % Nat.toInt d` from `d ≠ 0`.
theorem Nat.toIntNeZero ∀ (d: Nat) (ok: d ≠ 0): Nat.toInt d ≠ 0
  | p => ok (Int.ofNatInjective d 0 p)

--| `|x|`, as an `Int`.
def Int.abs: (x: Int) → Int
  | OfNat n => OfNat n
  | NegSucc n => OfNat (Succ n)

--| `Some x` if `x` isn't negative, otherwise `None`.
def Int.toNatChecked: (x: Int) → Option Nat
  | OfNat n => Some n
  | NegSucc n => None

--| The sign of `x`: `-1`, `0` or `1`.
def Int.sign: (x: Int) → Int
  | OfNat Zero => OfNat Zero
  | OfNat (Succ n) => OfNat 1
  | NegSucc n => NegSucc 0

--| `x % divisor` as a `Nat`, for indexing: `(x.modNat divisor).toInt = x % divisor.toInt`
--| when `divisor` isn't 0 (`Int.modNatToInt`), and below `divisor` (`Int.modNatLt`).
--| For 0 it's `(x % 0).toNat`: `x` if it isn't negative, otherwise 0.
def Int.modNat: (x: Int) → (divisor: Nat) → Nat
  | OfNat m, Zero => m
  | NegSucc m, Zero => 0
  | OfNat m, Succ n => m % Succ n
  | NegSucc m, Succ n => n - m % Succ n

--| Truncating division, rounding toward zero; the remainder has the
--| dividend's sign (C, Rust's `/` and `%`, JavaScript's `BigInt`). Like every
--| division, `Int.tdiv x 0 = 0` and `Int.tmod x 0 = x`.
def Int.tdiv: (dividend: Int) → (divisor: Int) → Int
  | dividend, OfNat Zero => OfNat Zero
  | OfNat m, OfNat (Succ n) => OfNat (m / Succ n)
  | NegSucc m, OfNat (Succ n) => Int.neg (OfNat (Succ m / Succ n))
  | OfNat m, NegSucc n => Int.neg (OfNat (m / Succ n))
  | NegSucc m, NegSucc n => OfNat (Succ m / Succ n)

--| The remainder of truncating division (`Int.tdiv`), with the dividend's sign: `Int.tmod (-7) 2` is `-1`.
def Int.tmod: (dividend: Int) → (divisor: Int) → Int
  | dividend, OfNat Zero => dividend
  | OfNat m, OfNat (Succ n) => OfNat (m % Succ n)
  | NegSucc m, OfNat (Succ n) => Int.neg (OfNat (Succ m % Succ n))
  | OfNat m, NegSucc n => OfNat (m % Succ n)
  | NegSucc m, NegSucc n => Int.neg (OfNat (Succ m % Succ n))

--| Flooring division, rounding toward negative infinity; the remainder has
--| the divisor's sign (Python, Haskell's `div` and `mod`). The same as
--| Euclidean division when the divisor is positive. `Int.fdiv x 0 = 0` and
--| `Int.fmod x 0 = x`.
def Int.fdiv: (dividend: Int) → (divisor: Int) → Int
  | dividend, OfNat Zero => OfNat Zero
  | OfNat m, OfNat (Succ n) => OfNat (m / Succ n)
  | NegSucc m, OfNat (Succ n) => NegSucc (m / Succ n)
  | OfNat Zero, NegSucc n => OfNat Zero
  | OfNat (Succ m), NegSucc n => NegSucc (m / Succ n)
  | NegSucc m, NegSucc n => OfNat (Succ m / Succ n)

--| The remainder of flooring division (`Int.fdiv`), with the divisor's sign: `Int.fmod 7 (-2)` is `-1`.
def Int.fmod: (dividend: Int) → (divisor: Int) → Int
  | dividend, OfNat Zero => dividend
  | OfNat m, OfNat (Succ n) => OfNat (m % Succ n)
  | NegSucc m, OfNat (Succ n) => OfNat (n - m % Succ n)
  | OfNat Zero, NegSucc n => OfNat Zero
  | OfNat (Succ m), NegSucc n => Int.neg (OfNat (n - m % Succ n))
  | NegSucc m, NegSucc n => Int.neg (OfNat (Succ m % Succ n))
