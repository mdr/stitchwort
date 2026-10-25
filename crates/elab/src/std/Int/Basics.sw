-- Integer functions that were in the core (docs/proposals/prelude-slim.md stage
-- 3): the division variants and others no compiler path names. This file depends
-- on the core alone, so a program that divides doesn't also load the lemmas in
-- `Int.sw`.

def Nat.toInt (n: Nat): Int := OfNat n

-- `|x|`, as an `Int`.
def Int.abs: Int → Int
  | OfNat n => OfNat n
  | NegSucc n => OfNat (Succ n)

-- `Some x` if `x` isn't negative, otherwise `None`.
def Int.toNatChecked: Int → Option Nat
  | OfNat n => Some n
  | NegSucc n => None

-- `-1`, `0` or `1`.
def Int.sign: Int → Int
  | OfNat Zero => OfNat Zero
  | OfNat (Succ n) => OfNat 1
  | NegSucc n => NegSucc 0

-- `x % divisor` as a `Nat`, for indexing: `(x.modNat divisor).toInt = x % divisor.toInt`.
def Int.modNat: Int → (divisor: Nat) → [auto ok: divisor ≠ 0] → Nat
  | x, Zero => Void.absurd (ok rfl)
  | OfNat m, Succ n => m % Succ n
  | NegSucc m, Succ n => n - m % Succ n

-- Truncating division, rounding toward zero; the remainder has the
-- dividend's sign (C, Rust's `/` and `%`, JavaScript's `BigInt`).
def Int.tdiv: (dividend: Int) → (divisor: Int) → [auto ok: divisor ≠ OfNat 0] → Int
  | dividend, OfNat Zero => Void.absurd (ok rfl)
  | OfNat m, OfNat (Succ n) => OfNat (m / Succ n)
  | NegSucc m, OfNat (Succ n) => Int.neg (OfNat (Succ m / Succ n))
  | OfNat m, NegSucc n => Int.neg (OfNat (m / Succ n))
  | NegSucc m, NegSucc n => OfNat (Succ m / Succ n)

def Int.tmod: (dividend: Int) → (divisor: Int) → [auto ok: divisor ≠ OfNat 0] → Int
  | dividend, OfNat Zero => Void.absurd (ok rfl)
  | OfNat m, OfNat (Succ n) => OfNat (m % Succ n)
  | NegSucc m, OfNat (Succ n) => Int.neg (OfNat (Succ m % Succ n))
  | OfNat m, NegSucc n => OfNat (m % Succ n)
  | NegSucc m, NegSucc n => Int.neg (OfNat (Succ m % Succ n))

-- Flooring division, rounding toward negative infinity; the remainder has
-- the divisor's sign (Python, Haskell's `div` and `mod`). The same as
-- Euclidean division when the divisor is positive.
def Int.fdiv: (dividend: Int) → (divisor: Int) → [auto ok: divisor ≠ OfNat 0] → Int
  | dividend, OfNat Zero => Void.absurd (ok rfl)
  | OfNat m, OfNat (Succ n) => OfNat (m / Succ n)
  | NegSucc m, OfNat (Succ n) => NegSucc (m / Succ n)
  | OfNat Zero, NegSucc n => OfNat Zero
  | OfNat (Succ m), NegSucc n => NegSucc (m / Succ n)
  | NegSucc m, NegSucc n => OfNat (Succ m / Succ n)

def Int.fmod: (dividend: Int) → (divisor: Int) → [auto ok: divisor ≠ OfNat 0] → Int
  | dividend, OfNat Zero => Void.absurd (ok rfl)
  | OfNat m, OfNat (Succ n) => OfNat (m % Succ n)
  | NegSucc m, OfNat (Succ n) => OfNat (n - m % Succ n)
  | OfNat Zero, NegSucc n => OfNat Zero
  | OfNat (Succ m), NegSucc n => Int.neg (OfNat (n - m % Succ n))
  | NegSucc m, NegSucc n => Int.neg (OfNat (Succ m % Succ n))
