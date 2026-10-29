-- `Float.Model`: IEEE 754 double arithmetic, exact then rounded
-- (docs/proposals/float-laws.md §8). Every finite double is a whole number
-- of units of 2^-1074, the smallest subnormal; an operation computes its
-- exact result from those numbers, then rounds it once to the nearest
-- double, ties to even. `Float`'s rounding operations are these
-- definitions; while a program runs, the machine's double arithmetic
-- computes them instead.
--
-- Everything here is over a double's 64 bits as a `Nat` (the NaN
-- canonical), so that `Float` can use it.

import Float.Model.Location (Exact, BelowHalf, Half, AboveHalf)

-- 2^k, by squaring: `pow2From fuel k` is `Nat.pow 2 k` for every fuel, and
-- takes a step per bit of `k` until the fuel runs out.
def Float.Model.pow2From: Nat → Nat → Nat
  | Zero, k => Nat.pow 2 k
  | Succ fuel, k =>
    if Nat.equal k 0 then 1
    else
      let half: Nat := Float.Model.pow2From fuel (Nat.divFuel k k 2)
      if Nat.equal (k - Nat.divFuel k k 2 * 2) 0 then half * half else half * half * 2

-- 2^k, split on `k`'s size first, so that for an unknown `k` it stays a call
-- instead of unfolding into its squarings.
def Float.Model.pow2 (k: Nat): Nat := Float.Model.pow2When (Nat.leq k 65535) k

def Float.Model.pow2When: Bool → Nat → Nat
  | True, k => Float.Model.pow2From 16 k
  | False, k => Nat.pow 2 k

-- The number of binary digits of `n` (0 for 0), one halving at a time.
def Float.Model.bitLengthSlow: Nat → Nat → Nat
  | Zero, n => 0
  | Succ fuel, n => if Nat.equal n 0 then 0 else Succ (Float.Model.bitLengthSlow fuel (Nat.divFuel n n 2))

-- `p`, `p^2`, `p^4`, … (`k` of them), last first, onto `acc`.
def Float.Model.squaresFrom: Nat → Nat → List Nat → List Nat
  | Zero, p, acc => acc
  | Succ k, p, acc => Float.Model.squaresFrom k (p * p) (Cons p acc)

-- The number of binary digits of `n`, given `powers`, which are 2^width,
-- 2^(width / 2), …, 2^1: at each, the top part of `n` is split off if it
-- has one. For `n < 2^(2 × width)`, one step per power.
def Float.Model.bitLengthBy: List Nat → Nat → Nat → Nat
  | Nil, width, n => Float.Model.bitLengthSlow n n
  | Cons p rest, width, n =>
    let high: Nat := Nat.divFuel n n p
    if Nat.equal high 0 then Float.Model.bitLengthBy rest (Nat.divFuel width width 2) n
    else width + Float.Model.bitLengthBy rest (Nat.divFuel width width 2) high

-- The number of binary digits of `n`: by halving below 2^16, otherwise one
-- step per power of `n`'s size below 2^8192 (and correct beyond it too).
-- Split on the size first, so that for an unknown `n` it stays a call.
def Float.Model.bitLength (n: Nat): Nat := Float.Model.bitLengthWhen (Nat.leq n 65535) n

def Float.Model.bitLengthWhen: Bool → Nat → Nat
  | True, n => Float.Model.bitLengthSlow 16 n
  | False, n => Float.Model.bitLengthBy (Float.Model.squaresFrom 13 2 Nil) 4096 n

-- The sign bit is set: `signBit` of `-0.0` is `True`.
def Float.Model.signBit (bits: Nat): Bool := Nat.leq 9223372036854775808 bits

-- The bits without the sign bit.
def Float.Model.magnitude (bits: Nat): Nat :=
  if Float.Model.signBit bits then bits - 9223372036854775808 else bits

-- A finite double's value in units of 2^-1074: a subnormal's fraction, or a
-- normal double's significand (the fraction with its leading 1) times
-- 2^(e - 1) for exponent field `e`. Both zeros are `0`.
def Float.Model.units (bits: Nat): Int :=
  let m: Nat := Float.Model.magnitude bits
  let e: Nat := Nat.divFuel m m 4503599627370496
  let f: Nat := m - e * 4503599627370496
  Int.signed (Float.Model.signBit bits)
    (if Nat.equal e 0 then f else Float.Model.pow2 (e - 1) * (f + 4503599627370496))

-- Where an exact value lies between two neighbouring candidates: on the
-- lower one, below the point halfway to the upper, on it, or above it.
type Float.Model.Location: Type =
  | Exact
  | BelowHalf
  | Half
  | AboveHalf

-- The location of `q + r / d`, for `r < d`, between `q` and `q + 1`.
def Float.Model.locate (r: Nat) (d: Nat): Float.Model.Location :=
  if Nat.equal r 0 then Exact
  else if Nat.equal (2 * r) d then Half
  else if Nat.leq (2 * r) d then BelowHalf
  else AboveHalf

-- Whether the value at `loc` past `q` rounds up to `q + 1`: past halfway,
-- or halfway with `q` odd (ties to even).
def Float.Model.roundsUp (q: Nat): Float.Model.Location → Bool
  | Exact => False
  | BelowHalf => False
  | Half => Nat.equal (q - Nat.divFuel q q 2 * 2) 1
  | AboveHalf => True

-- The zero with sign bit `negative`.
def Float.Model.zeroBits (negative: Bool): Nat := if negative then 9223372036854775808 else 0

-- The rounding core: the double nearest `(q + loc) × 2^exponent` units, with
-- sign `negative`, where `q < 2^53`, and `q >= 2^52` unless `exponent` is
-- 0. The bits are `exponent × 2^52 + q` after rounding, as the exponent
-- field counts from 1 for normal doubles: a subnormal has `exponent` 0 and
-- `q < 2^52`, and rounding up to 2^53 carries into the exponent. At
-- +infinity's bits or beyond it overflows to infinity.
def Float.Model.roundCore (negative: Bool) (exponent: Nat) (q: Nat) (loc: Float.Model.Location): Nat :=
  let rounded: Nat := if Float.Model.roundsUp q loc then q + 1 else q
  let bits: Nat := exponent * 4503599627370496 + rounded
  let finite: Nat := if Nat.leq 9218868437227405312 bits then 9218868437227405312 else bits
  if negative then finite + 9223372036854775808 else finite

-- `n × 2^shift` and `d`, or `n` and `d × 2^-shift`: a fraction scaled by
-- `2^shift`, both parts whole.
def Float.Model.scaleUp (n: Nat): Int → Nat
  | OfNat k => n * Float.Model.pow2 k
  | NegSucc k => n

def Float.Model.scaleDown (d: Nat): Int → Nat
  | OfNat k => d
  | NegSucc k => d * Float.Model.pow2 (Succ k)

-- The double nearest `n / den × 2^s` units, with sign `negative`, for `n`
-- and `den` positive. The exponent is the one giving a 53-bit quotient (or
-- 0, for a subnormal): at `c = bitLength den + 53 - bitLength n` the
-- scaled quotient has 53 or 54 bits, and one comparison tells which. The
-- division's remainder gives the location.
def Float.Model.roundMagnitude (negative: Bool) (n: Nat) (den: Nat) (s: Int): Nat :=
  let c: Int := Int.subNatNat (Float.Model.bitLength den + 53) (Float.Model.bitLength n)
  let wide: Bool := Nat.leq (Float.Model.scaleDown den c * Float.Model.pow2 53) (Float.Model.scaleUp n c)
  let exponent: Nat := Int.toNat (Int.sub s (if wide then Int.sub c (OfNat 1) else c))
  let shift: Int := Int.sub s (OfNat exponent)
  let top: Nat := Float.Model.scaleUp n shift
  let bottom: Nat := Float.Model.scaleDown den shift
  let q: Nat := Nat.divFuel top top bottom
  Float.Model.roundCore negative exponent q (Float.Model.locate (top - q * bottom) bottom)

-- The double nearest `num / den × 2^scale`, for `den > 0`, ties to even,
-- an infinity past the largest. If `num` is 0 the result is the zero with
-- sign `zeroSign`; a nonzero value that rounds to zero keeps `num`'s sign.
def Float.Model.roundRatio (num: Int) (den: Nat) (scale: Int) (zeroSign: Bool): Nat :=
  if Nat.equal (Int.natAbs num) 0 then Float.Model.zeroBits zeroSign
  else Float.Model.roundMagnitude (Int.isNeg num) (Int.natAbs num) den (Int.add scale (OfNat 1074))

-- The double nearest `n × 2^e`.
def Float.Model.roundScaled (n: Int) (e: Int) (zeroSign: Bool): Nat := Float.Model.roundRatio n 1 e zeroSign

def Float.Model.isNaN (bits: Nat): Bool := Nat.equal bits 9221120237041090560

def Float.Model.isInfinite (bits: Nat): Bool := Nat.equal (Float.Model.magnitude bits) 9218868437227405312

-- `x + y`: the NaN if either is, or for infinities of opposite signs; an
-- infinity if either is; otherwise the exact sum, rounded. The sum of two
-- zeros is `-0.0` only if both are, and a nonzero sum never rounds to zero.
def Float.Model.addBits (a: Nat) (b: Nat): Nat :=
  if Float.Model.isNaN a ∨ Float.Model.isNaN b then 9221120237041090560
  else if Float.Model.isInfinite a then (if Float.Model.isInfinite b ∧ ¬(Nat.equal a b) then 9221120237041090560 else a)
  else if Float.Model.isInfinite b then b
  else
    Float.Model.roundScaled (Int.add (Float.Model.units a) (Float.Model.units b)) (-1074)
      (Float.Model.signBit a ∧ Float.Model.signBit b)

test "Float.Model.pow2" := Float.Model.pow2 0 == 1 ∧ Float.Model.pow2 1 == 2 ∧ Float.Model.pow2 64 == 18446744073709551616
test "Float.Model.bitLength" :=
  Float.Model.bitLength 0 == 0 ∧ Float.Model.bitLength 1 == 1 ∧ Float.Model.bitLength 255 == 8
    ∧ Float.Model.bitLength 256 == 9 ∧ Float.Model.bitLength (Nat.pow 2 2097) == 2098
test "Float.Model.units" :=
  Float.Model.units 1 == OfNat 1 ∧ Float.Model.units 9223372036854775808 == OfNat 0
    ∧ Float.Model.units 4607182418800017408 == OfNat (Nat.pow 2 1074)
-- 0.1 + 0.2, and 1.0 + 2^-53 (a tie, to even: 1.0).
test "Float.Model.addBits" :=
  Float.Model.addBits 4591870180066957722 4596373779694328218 == 4599075939470750516
    ∧ Float.Model.addBits 4607182418800017408 4368491638549381120 == 4607182418800017408
