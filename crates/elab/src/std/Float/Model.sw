--| `Float.Model`: IEEE 754 double arithmetic, exact then rounded. Every finite
--| double is a whole number of units of 2^-1074, the smallest subnormal; an
--| operation computes its exact result from those numbers, then rounds it once
--| to the nearest double, ties to even. `Float`'s rounding operations are these
--| definitions; while a program runs, the machine's double arithmetic computes
--| them instead.
--|
--| Everything here is over a double's 64 bits as a `Nat` (the NaN
--| canonical), so that `Float` can use it.
-- (docs/proposals/float-laws.md §8)

import Float.Model.Location (Exact, BelowHalf, Half, AboveHalf)

--| 2^k, by squaring: `pow2From fuel k` is `Nat.pow 2 k` for every fuel, and
--| takes a step per bit of `k` until the fuel runs out.
def Float.Model.pow2From: (fuel: Nat) → (k: Nat) → Nat
  | Zero, k => Nat.pow 2 k
  | Succ fuel, k =>
    if Nat.equal k 0 then 1
    else
      let half: Nat := Float.Model.pow2From fuel (Nat.divFuel k k 2)
      if Nat.equal (k - Nat.divFuel k k 2 * 2) 0 then half * half else half * half * 2

--| 2^k, split on `k`'s size first, so that for an unknown `k` it stays a call
--| instead of unfolding into its squarings.
def Float.Model.pow2 (k: Nat): Nat := Float.Model.pow2When (Nat.leq k 65535) k

--| 2^k, given whether `k` is at most 65535: by squarings then, otherwise by `Nat.pow`.
def Float.Model.pow2When: (small: Bool) → (k: Nat) → Nat
  | True, k => Float.Model.pow2From 16 k
  | False, k => Nat.pow 2 k

--| The number of binary digits of `n` (0 for 0), one halving at a time.
def Float.Model.bitLengthSlow: (fuel: Nat) → (n: Nat) → Nat
  | Zero, n => 0
  | Succ fuel, n => if Nat.equal n 0 then 0 else Succ (Float.Model.bitLengthSlow fuel (Nat.divFuel n n 2))

--| `p`, `p^2`, `p^4`, … (`k` of them), last first, onto `acc`.
@[tailrec]
def Float.Model.squaresFrom: (count: Nat) → (base: Nat) → (acc: List Nat) → List Nat
  | Zero, p, acc => acc
  | Succ k, p, acc => Float.Model.squaresFrom k (p * p) [p, ..acc]

--| The number of binary digits of `n`, given `powers`, which are 2^width,
--| 2^(width / 2), …, 2^1: at each, the top part of `n` is split off if it
--| has one. For `n < 2^(2 × width)`, one step per power.
def Float.Model.bitLengthBy: (powers: List Nat) → (width: Nat) → (n: Nat) → Nat
  | [], width, n => Float.Model.bitLengthSlow n n
  | [p, ..rest], width, n =>
    let high: Nat := Nat.divFuel n n p
    if Nat.equal high 0 then Float.Model.bitLengthBy rest (Nat.divFuel width width 2) n
    else width + Float.Model.bitLengthBy rest (Nat.divFuel width width 2) high

--| The number of binary digits of `n`: by halving below 2^16, otherwise one
--| step per power of `n`'s size below 2^8192 (and correct beyond it too).
-- Split on the size first, so that for an unknown `n` it stays a call.
def Float.Model.bitLength (n: Nat): Nat := Float.Model.bitLengthWhen (Nat.leq n 65535) n

--| The number of binary digits of `n`, given whether `n` is at most 65535.
def Float.Model.bitLengthWhen: (small: Bool) → (n: Nat) → Nat
  | True, n => Float.Model.bitLengthSlow 16 n
  | False, n => Float.Model.bitLengthBy (Float.Model.squaresFrom 13 2 []) 4096 n

--| The sign bit is set: `signBit` of `-0.0` is `True`.
def Float.Model.signBit (bits: Nat): Bool := Nat.leq 9223372036854775808 bits

--| The bits without the sign bit.
def Float.Model.magnitude (bits: Nat): Nat := if Float.Model.signBit bits then bits - 9223372036854775808 else bits

--| A finite double's value in units of 2^-1074.
--| For a subnormal that is its fraction; for a normal double it is the
--| significand (the fraction with its leading 1) times 2^(e - 1) for
--| exponent field `e`. Both zeros are `0`.
def Float.Model.units (bits: Nat): Int :=
  let m: Nat := Float.Model.magnitude bits
  let e: Nat := Nat.divFuel m m 4503599627370496
  let f: Nat := m - e * 4503599627370496
  Int.signed (Float.Model.signBit bits) (if Nat.equal e 0 then f else Float.Model.pow2 (e - 1) * (f + 4503599627370496))

--| Where an exact value lies between two neighbouring candidates: on the
--| lower one, below the point halfway to the upper, on it, or above it.
type Float.Model.Location: Type = | Exact | BelowHalf | Half | AboveHalf

--| The location of `q + r / d`, for `r < d`, between `q` and `q + 1`.
def Float.Model.locate (r d: Nat): Float.Model.Location :=
  if Nat.equal r 0 then Exact
  else if Nat.equal (2 * r) d then Half
  else if Nat.leq (2 * r) d then BelowHalf
  else AboveHalf

--| Whether the value at `loc` past `q` rounds up to `q + 1`: past halfway,
--| or halfway with `q` odd (ties to even).
def Float.Model.roundsUp (q: Nat): (loc: Float.Model.Location) → Bool
  | Exact | BelowHalf => False
  | Half => Nat.equal (q - Nat.divFuel q q 2 * 2) 1
  | AboveHalf => True

--| The zero with sign bit `negative`.
def Float.Model.zeroBits (negative: Bool): Nat := if negative then 9223372036854775808 else 0

--| The rounding core: the double nearest `(q + loc) × 2^exponent` units, with
--| sign `negative`, where `q < 2^53`, and `q >= 2^52` unless `exponent` is 0.
--| The bits are `exponent × 2^52 + q` after rounding, as the exponent field
--| counts from 1 for normal doubles: a subnormal has `exponent` 0 and
--| `q < 2^52`, and rounding up to 2^53 carries into the exponent. At
--| +infinity's bits or beyond it overflows to infinity.
def Float.Model.roundCore (negative: Bool) (exponent q: Nat) (loc: Float.Model.Location): Nat :=
  let rounded: Nat := if Float.Model.roundsUp q loc then q + 1 else q
  let bits: Nat := exponent * 4503599627370496 + rounded
  let finite: Nat := if Nat.leq 9218868437227405312 bits then 9218868437227405312 else bits
  if negative then finite + 9223372036854775808 else finite

--| The numerator of `n / d` scaled by `2^shift`: `n × 2^shift`, or `n` when the shift is negative.
-- `n × 2^shift` and `d`, or `n` and `d × 2^-shift`: a fraction scaled by
-- `2^shift`, both parts whole.
def Float.Model.scaleUp (n: Nat): (shift: Int) → Nat
  | OfNat k => n * Float.Model.pow2 k
  | NegSucc k => n

--| The denominator of `n / d` scaled by `2^shift`: `d`, or `d × 2^-shift` when the shift is negative.
def Float.Model.scaleDown (d: Nat): (shift: Int) → Nat
  | OfNat k => d
  | NegSucc k => d * Float.Model.pow2 (Succ k)

--| The double nearest `n / den × 2^s` units, with sign `negative`, for `n`
--| and `den` positive. The exponent is the one giving a 53-bit quotient (or
--| 0, for a subnormal): at `c = bitLength den + 53 - bitLength n` the
--| scaled quotient has 53 or 54 bits, and one comparison tells which. The
--| division's remainder gives the location.
def Float.Model.roundMagnitude (negative: Bool) (n den: Nat) (s: Int): Nat :=
  let c: Int := Int.subNatNat (Float.Model.bitLength den + 53) (Float.Model.bitLength n)
  let wide: Bool := Nat.leq (Float.Model.scaleDown den c * Float.Model.pow2 53) (Float.Model.scaleUp n c)
  let exponent: Nat := Int.toNat (Int.sub s (if wide then Int.sub c (OfNat 1) else c))
  let shift: Int := Int.sub s (OfNat exponent)
  let top: Nat := Float.Model.scaleUp n shift
  let bottom: Nat := Float.Model.scaleDown den shift
  let q: Nat := Nat.divFuel top top bottom
  Float.Model.roundCore negative exponent q (Float.Model.locate (top - q * bottom) bottom)

--| The double nearest `num / den × 2^scale`, for `den > 0`, ties to even,
--| an infinity past the largest. If `num` is 0 the result is the zero with
--| sign `zeroSign`; a nonzero value that rounds to zero keeps `num`'s sign.
def Float.Model.roundRatio (num: Int) (den: Nat) (scale: Int) (zeroSign: Bool): Nat :=
  if Nat.equal (Int.natAbs num) 0 then Float.Model.zeroBits zeroSign
  else Float.Model.roundMagnitude (Int.isNeg num) (Int.natAbs num) den (Int.add scale (OfNat 1074))

--| The double nearest `n × 2^e`.
def Float.Model.roundScaled (n e: Int) (zeroSign: Bool): Nat := Float.Model.roundRatio n 1 e zeroSign

--| Whether a bit pattern is the NaN's.
def Float.Model.isNaN (bits: Nat): Bool := Nat.equal bits 9221120237041090560

--| Whether a bit pattern is an infinity's, of either sign.
def Float.Model.isInfinite (bits: Nat): Bool := Nat.equal (Float.Model.magnitude bits) 9218868437227405312

--| `x + y`: the NaN if either is, or for infinities of opposite signs; an
--| infinity if either is; otherwise the exact sum, rounded. The sum of two
--| zeros is `-0.0` only if both are, and a nonzero sum never rounds to zero.
def Float.Model.addBits (a b: Nat): Nat :=
  if Float.Model.isNaN a ∨ Float.Model.isNaN b then 9221120237041090560
  else if Float.Model.isInfinite a then (if Float.Model.isInfinite b ∧ ¬(Nat.equal a b) then 9221120237041090560 else a)
  else if Float.Model.isInfinite b then b
  else
    Float.Model.roundScaled
      (Int.add (Float.Model.units a) (Float.Model.units b))
      (-1074)
      (Float.Model.signBit a ∧ Float.Model.signBit b)

--| The infinity with sign bit `negative`.
def Float.Model.infinityBits (negative: Bool): Nat := if negative then 18442240474082181120 else 9218868437227405312

--| Whether a bit pattern is a zero's, of either sign.
def Float.Model.isZero (bits: Nat): Bool := Nat.equal (Float.Model.magnitude bits) 0

--| `x * y`: the NaN if either is, or for an infinity times a zero; an
--| infinity if either is; otherwise the exact product, rounded. The sign is
--| the operands' signs combined, for zeros and infinities too.
-- The product of two units is in units of 2^-2148.
def Float.Model.mulBits (a b: Nat): Nat :=
  if Float.Model.isNaN a ∨ Float.Model.isNaN b then 9221120237041090560
  else if Float.Model.isInfinite a ∨ Float.Model.isInfinite b then
    (if Float.Model.isZero a ∨ Float.Model.isZero b then 9221120237041090560
     else Float.Model.infinityBits (Bool.xor (Float.Model.signBit a) (Float.Model.signBit b)))
  else
    Float.Model.roundScaled
      (Int.mul (Float.Model.units a) (Float.Model.units b))
      (-2148)
      (Bool.xor (Float.Model.signBit a) (Float.Model.signBit b))

--| The double nearest the integer `i`; `0.0` for 0.
def Float.Model.ofIntBits (i: Int): Nat := Float.Model.roundScaled i 0 False

--| `x / y`: the NaN if either is, for two infinities or two zeros; an
--| infinity for an infinity over a finite double, or a nonzero finite one
--| over a zero; a zero for a finite double over an infinity; otherwise the
--| exact quotient, rounded. The sign is the operands' signs combined.
-- The units' scales cancel, so the quotient of the units is the value;
-- `y`'s sign moves to the numerator so that the denominator is positive.
def Float.Model.divBits (a b: Nat): Nat :=
  if Float.Model.isNaN a ∨ Float.Model.isNaN b then 9221120237041090560
  else if Float.Model.isInfinite a then
    (if Float.Model.isInfinite b then 9221120237041090560
     else Float.Model.infinityBits (Bool.xor (Float.Model.signBit a) (Float.Model.signBit b)))
  else if Float.Model.isInfinite b then Float.Model.zeroBits (Bool.xor (Float.Model.signBit a) (Float.Model.signBit b))
  else if Float.Model.isZero b then
    (if Float.Model.isZero a then 9221120237041090560
     else Float.Model.infinityBits (Bool.xor (Float.Model.signBit a) (Float.Model.signBit b)))
  else
    Float.Model.roundRatio
      (if Float.Model.signBit b then Int.neg (Float.Model.units a) else Float.Model.units a)
      (Int.natAbs (Float.Model.units b))
      (OfNat 0)
      (Bool.xor (Float.Model.signBit a) (Float.Model.signBit b))

--| `x % y`, JS's truncating remainder: the NaN if either is, for an
--| infinite `x` or a zero `y`; `x` for a finite `x` over an infinity;
--| otherwise `x - n × y` for the whole `n` of `x / y` truncated, which is
--| exact, with `x`'s sign (a zero result too).
def Float.Model.remBits (a b: Nat): Nat :=
  if Float.Model.isNaN a ∨ Float.Model.isNaN b ∨ Float.Model.isInfinite a ∨ Float.Model.isZero b then
    9221120237041090560
  else if Float.Model.isInfinite b then a
  else
    let m: Nat := Int.natAbs (Float.Model.units a)
    let d: Nat := Int.natAbs (Float.Model.units b)
    Float.Model.roundScaled
      (Int.signed (Float.Model.signBit a) (m - Nat.divFuel m m d * d))
      (-1074)
      (Float.Model.signBit a)

--| The largest integer at most `v / p`, for `v` the integer with sign
--| `negative` and size `m`, and `p` positive. With `p` 2^1074, the whole
--| part of a value in units.
def Float.Model.floorDiv (negative: Bool) (m p: Nat): Int :=
  let q: Nat := Nat.divFuel m m p
  if negative ∧ ¬(Nat.equal (q * p) m) then NegSucc q else Int.signed negative q

--| Whether a pattern is the NaN's or an infinity's.
def Float.Model.isSpecial (bits: Nat): Bool := Nat.leq 9218868437227405312 (Float.Model.magnitude bits)

--| JS's `Math.floor`: the NaN, the infinities and the zeros as they are;
--| otherwise the largest whole number at most `x`, `-0.0` only for `-0.0`.
def Float.Model.floorBits (a: Nat): Nat :=
  if Float.Model.isSpecial a then a
  else
    Float.Model.roundScaled
      (Float.Model.floorDiv (Float.Model.signBit a) (Int.natAbs (Float.Model.units a)) (Float.Model.pow2 1074))
      0
      (Float.Model.signBit a)

--| JS's `Math.ceil`: `-floor (-x)`, so a negative `x` above -1 gives `-0.0`.
def Float.Model.ceilBits (a: Nat): Nat :=
  if Float.Model.isSpecial a then a
  else
    Float.Model.roundScaled
      (Int.neg
        (Float.Model.floorDiv (¬(Float.Model.signBit a)) (Int.natAbs (Float.Model.units a)) (Float.Model.pow2 1074)))
      0
      (Float.Model.signBit a)

--| JS's `Math.trunc`: the whole part, with `x`'s sign.
def Float.Model.truncBits (a: Nat): Nat :=
  if Float.Model.isSpecial a then a
  else
    let m: Nat := Int.natAbs (Float.Model.units a)
    Float.Model.roundScaled
      (Int.signed (Float.Model.signBit a) (Nat.divFuel m m (Float.Model.pow2 1074)))
      0
      (Float.Model.signBit a)

--| JS's `Math.round`: the largest whole number at most `x + 1/2`, computed
--| exactly (2^1073 units is a half), so a tie goes up towards +infinity; a
--| zero result keeps `x`'s sign (`round (-0.5)` is `-0.0`).
def Float.Model.roundBits (a: Nat): Nat :=
  if Float.Model.isSpecial a then a
  else
    let v: Int := Int.add (Float.Model.units a) (OfNat (Float.Model.pow2 1073))
    Float.Model.roundScaled
      (Float.Model.floorDiv (Int.isNeg v) (Int.natAbs v) (Float.Model.pow2 1074))
      0
      (Float.Model.signBit a)

--| The integer square root of `n` by Newton's method, given a `guess` at
--| least it: each step averages `guess` and `n / guess`, which decreases
--| until it reaches the root, where the average stops falling. The fuel is
--| far beyond the steps needed from `Float.Model.isqrt`'s starting point.
def Float.Model.isqrtFrom: (fuel: Nat) → (n guess: Nat) → Nat
  | Zero, n, guess => guess
  | Succ fuel, n, guess =>
    let sum: Nat := guess + Nat.divFuel n n guess
    let next: Nat := Nat.divFuel sum sum 2
    if Nat.leq guess next then guess else Float.Model.isqrtFrom fuel n next

--| The largest `r` with `r * r <= n`, for `n` positive: Newton's method from
--| the power of two just above the root.
def Float.Model.isqrt (n: Nat): Nat :=
  Float.Model.isqrtFrom 64 n
    (Float.Model.pow2 (Nat.divFuel (Float.Model.bitLength n + 1) (Float.Model.bitLength n + 1) 2))

--| `sqrt x`, IEEE 754's correctly rounded square root: the NaN for the NaN
--| and for any negative number but `-0.0` (which is its own root), `x` for
--| the zeros and `+infinity`; otherwise the exact root, rounded once.
-- A value of `u` units is `u * 2^-1074`, so its root is `sqrt (u * 2^1074)`
-- units, at least 2^537, far above 2^54. The integer root `s` of that
-- radicand, with its remainder, locates the root between `s` and `s + 1`
-- (never on a tie, since a root that isn't whole is irrational); `2 * s`
-- or `2 * s + 1` in half units has that location, and at this size the
-- rounding points are even in half units, so it rounds as the root does.
def Float.Model.sqrtBits (a: Nat): Nat :=
  if Float.Model.isNaN a then 9221120237041090560
  else if Float.Model.isZero a ∨ Nat.equal a 9218868437227405312 then a
  else if Float.Model.signBit a then 9221120237041090560
  else
    let radicand: Nat := Int.natAbs (Float.Model.units a) * Float.Model.pow2 1074
    let root: Nat := Float.Model.isqrt radicand
    Float.Model.roundScaled (OfNat (if Nat.equal radicand (root * root) then 2 * root else 2 * root + 1)) (-1075) False

test "Float.Model.pow2" :=
  Float.Model.pow2 0 == 1 ∧ Float.Model.pow2 1 == 2 ∧ Float.Model.pow2 64 == 18446744073709551616
test "Float.Model.bitLength" :=
  Float.Model.bitLength 0 == 0
    ∧ Float.Model.bitLength 1 == 1
    ∧ Float.Model.bitLength 255 == 8
    ∧ Float.Model.bitLength 256 == 9
    ∧ Float.Model.bitLength (Nat.pow 2 2097) == 2098
test "Float.Model.units" :=
  Float.Model.units 1 == OfNat 1
    ∧ Float.Model.units 9223372036854775808 == OfNat 0
    ∧ Float.Model.units 4607182418800017408 == OfNat (Nat.pow 2 1074)
--| 0.1 + 0.2, and 1.0 + 2^-53 (a tie, to even: 1.0).
test "Float.Model.addBits" :=
  Float.Model.addBits 4591870180066957722 4596373779694328218 == 4599075939470750516
    ∧ Float.Model.addBits 4607182418800017408 4368491638549381120 == 4607182418800017408
--| 0.1 × 3.0; 1.0 + 2^-52 times itself (2^-104 drops, below the tie); the
--| smallest subnormal halved (a tie, to even: `+0.0`) and times 1.5 (up);
--| `-0.0 × 1.0`; infinity times `-0.0`, and times `-1.0`.
test "Float.Model.mulBits" :=
  Float.Model.mulBits 4591870180066957722 4613937818241073152 == 4599075939470750516
    ∧ Float.Model.mulBits 4607182418800017409 4607182418800017409 == 4607182418800017410
    ∧ Float.Model.mulBits 1 4602678819172646912 == 0
    ∧ Float.Model.mulBits 1 4609434218613702656 == 2
    ∧ Float.Model.mulBits 9223372036854775808 4607182418800017408 == 9223372036854775808
    ∧ Float.Model.mulBits 9218868437227405312 9223372036854775808 == 9221120237041090560
    ∧ Float.Model.mulBits 9218868437227405312 13830554455654793216 == 18442240474082181120
--| 2^53 + 1 (a tie, to even: 2^53), -(2^53 + 3) (a tie, up), 2^1024 (overflow).
test "Float.Model.ofIntBits" :=
  Float.Model.ofIntBits (OfNat 9007199254740993) == 4845873199050653696
    ∧ Float.Model.ofIntBits (Int.neg (OfNat 9007199254740995)) == 14069245235905429506
    ∧ Float.Model.ofIntBits (OfNat (Nat.pow 2 1024)) == 9218868437227405312
    ∧ Float.Model.ofIntBits (OfNat 0) == 0
--| 1 / 3 (inexact), 1 / 0 and -1 / 0, 0 / 0, 1 / -infinity (`-0.0`), and
--| the smallest subnormal over 2 (a tie, to even: `+0.0`) and over the
--| double nearest 2/3 (just over 1.5 units: up to 2).
test "Float.Model.divBits" :=
  Float.Model.divBits 4607182418800017408 4613937818241073152 == 4599676419421066581
    ∧ Float.Model.divBits 4607182418800017408 0 == 9218868437227405312
    ∧ Float.Model.divBits 13830554455654793216 0 == 18442240474082181120
    ∧ Float.Model.divBits 0 0 == 9221120237041090560
    ∧ Float.Model.divBits 4607182418800017408 18442240474082181120 == 9223372036854775808
    ∧ Float.Model.divBits 1 4611686018427387904 == 0
    ∧ Float.Model.divBits 1 4604180019048437077 == 2
--| -5.5 % 2.0, 5.0 % -infinity, -0.0 % 1.0, 1.0 % 0.0.
test "Float.Model.remBits" :=
  Float.Model.remBits 13841250504769798144 4611686018427387904 == 13832806255468478464
    ∧ Float.Model.remBits 4617315517961601024 18442240474082181120 == 4617315517961601024
    ∧ Float.Model.remBits 9223372036854775808 4607182418800017408 == 9223372036854775808
    ∧ Float.Model.remBits 4607182418800017408 0 == 9221120237041090560
--| floor -1.5, ceil -0.5 (`-0.0`), trunc -1.5, round -2.5 and 2.5, round
--| 0.49999999999999994 (`+0.0`), round -0.5 (`-0.0`).
test "Float.Model.floorBits" :=
  Float.Model.floorBits 13832806255468478464 == 13835058055282163712
    ∧ Float.Model.ceilBits 13826050856027422720 == 9223372036854775808
    ∧ Float.Model.truncBits 13832806255468478464 == 13830554455654793216
    ∧ Float.Model.roundBits 13836183955189006336 == 13835058055282163712
    ∧ Float.Model.roundBits 4612811918334230528 == 4613937818241073152
    ∧ Float.Model.roundBits 4602678819172646911 == 0
    ∧ Float.Model.roundBits 13826050856027422720 == 9223372036854775808
test "Float.Model.isqrt" :=
  Float.Model.isqrt 1 == 1
    ∧ Float.Model.isqrt 3 == 1
    ∧ Float.Model.isqrt 4 == 2
    ∧ Float.Model.isqrt 99 == 9
    ∧ Float.Model.isqrt 100 == 10
    ∧ Float.Model.isqrt (Float.Model.pow2 200) == Float.Model.pow2 100
test "Float.Model.sqrtBits" :=
  Float.Model.sqrtBits 4616189618054758400 == 4611686018427387904
    ∧ Float.Model.sqrtBits 4611686018427387904 == 4609047870845172685
    ∧ Float.Model.sqrtBits 9223372036854775808 == 9223372036854775808
    ∧ Float.Model.sqrtBits 13830554455654793216 == 9221120237041090560
