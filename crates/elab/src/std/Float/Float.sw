-- `Float`: a 64-bit IEEE 754 double, the JavaScript `number`
-- (docs/proposals/float.md). At run time it is the real double (a Rust
-- `f64`, a JS `number`); in the logic it is the record of its 64 bits, with
-- every NaN as the one NaN, `0x7FF8000000000000`. Two doubles are equal
-- exactly when their bits are, so `0.0` and `-0.0` differ and the NaN equals
-- itself (`Object.is`, not `===`; `===` is `Float.ieeeEq`).
--
-- The exact operations (`neg`, `abs`, `isNaN`, `isFinite`, `==`, the
-- order, the IEEE comparisons, `toInt`) are ordinary definitions over the
-- bits. The rounding ones (`add`, `sub`, `mul`, `div`, `rem`, `floor`,
-- `ceil`, `trunc`, `round`, `ofInt`, `ofNat`) are primitives: the checker
-- computes them on known doubles with Rust's `f64`, under the contract of
-- docs/proposals/float.md §3.3, and otherwise they are unknown functions.
-- `toText` is a primitive the checker never computes: each runtime supplies
-- it (JS's `String(x)`).
--
-- The kernel, the runtime and the JS backend rely on these exact
-- declarations, by content hash: `FLOAT_DATA_HASH` and the native hashes in
-- `crates/core/src/float.rs`. Change one, and update those (a test prints
-- the new ones) with the natives it affects.
--
-- Bit patterns used below: 2^63 = 9223372036854775808 (the sign bit);
-- +infinity 0x7FF0000000000000 = 9218868437227405312; the NaN
-- 0x7FF8000000000000 = 9221120237041090560; -infinity 0xFFF0000000000000 =
-- 18442240474082181120.

-- A double's bits, with the NaN canonical: a non-negative double up to
-- +infinity, the NaN, or a negative double up to -infinity. (Every other
-- pattern below 2^64 is a NaN with another sign or payload.)
def Float.isValid (n: Nat): Bool :=
  (Nat.leq n 9218868437227405312 || Nat.equal n 9221120237041090560)
    || (Nat.leq 9223372036854775808 n && Nat.leq n 18442240474082181120)

type Float = { bits: Nat, valid: Float.isValid bits = True }

-- The witness `Float.make` puts in a record: on a known `b` it is
-- `Eq.refl True` whatever `p` is, so every way of building a `Float` with
-- known bits (a literal, a primitive's result, a definition, a native) gives
-- the same record (docs/proposals/float.md §3.4, D731).
def Bool.canonicalTrue: (b: Bool) -> b = True -> b = True
  | True, _ => rfl
  | False, p => p

-- The one way the definitions here build a `Float`.
def Float.make (n: Nat) (p: Float.isValid n = True): Float :=
  { bits = n, valid = Bool.canonicalTrue (Float.isValid n) p }

def Float.nan: Float := Float.make 9221120237041090560 rfl

def Float.infinity: Float := Float.make 9218868437227405312 rfl

def Float.isNaN (x: Float): Bool := Nat.equal x.bits 9221120237041090560

-- Bit extensionality: two `Float`s with the same bits are equal, whatever
-- their `valid` proofs (proofs of a `Bool` equation are unique).
theorem Float.mkExt (a: Nat) (b: Nat) (p: Float.isValid a = True) (e: a = b):
    (q: Float.isValid b = True) -> ({ bits = a, valid = p }: Float) = { bits = b, valid = q } :=
  J (b' e' => (q': Float.isValid b' = True) -> ({ bits = a, valid = p }: Float) = { bits = b', valid = q' })
    (q' => J (r e'' => ({ bits = a, valid = p }: Float) = { bits = a, valid = r }) rfl
      (Bool.uniqueEq (Float.isValid a) True p q'))
    e

theorem Float.bitsExt (x: Float) (y: Float) (e: x.bits = y.bits): x = y :=
  match x, y with
    | { bits = a, valid = p }, { bits = b, valid = q } => Float.mkExt a b p e q

theorem Float.bitsNe (x: Float) (y: Float) (h: Not (x.bits = y.bits)): Not (x = y) :=
  e => h (Eq.cong (k => k.bits) e)

-- `==`: the same double. For two known doubles this is `Yes (Float.bitsExt
-- x y rfl)` or `No (Float.bitsNe x y (Nat.equalFalse m n rfl))`, which is
-- what the native gives.
def Float.decEqFrom (x: Float) (y: Float): Decidable (x.bits = y.bits) -> Decidable (x = y)
  | Yes h => Yes (Float.bitsExt x y h)
  | No h => No (Float.bitsNe x y h)

def Float.decEq (x: Float) (y: Float): Decidable (x = y) := Float.decEqFrom x y (Nat.decEq x.bits y.bits)

instance Float.instDecEq: DecEq Float := { decide = Float.decEq }

-- JavaScript's `===`: the NaN is not equal to itself, and `0.0` equals `-0.0`.
def Float.isZero (x: Float): Bool := Nat.equal x.bits 0 || Nat.equal x.bits 9223372036854775808

def Float.ieeeEq (x: Float) (y: Float): Bool :=
  !(Float.isNaN x) && (Nat.equal x.bits y.bits || (Float.isZero x && Float.isZero y))

-- The sign bit flipped, and cleared.
def Float.flipSignBits (n: Nat): Nat :=
  if Nat.leq 9223372036854775808 n then n - 9223372036854775808 else n + 9223372036854775808

def Float.clearSignBits (n: Nat): Nat :=
  if Nat.leq 9223372036854775808 n then n - 9223372036854775808 else n

theorem Float.validLow (m: Nat) (h: m <= 9218868437227405312): Float.isValid m = True :=
  Eq.cong (b => (b || Nat.equal m 9221120237041090560)
    || (Nat.leq 9223372036854775808 m && Nat.leq m 18442240474082181120)) h

theorem Float.validHigh (m: Nat) (h1: 9223372036854775808 <= m) (h2: m <= 18442240474082181120):
    Float.isValid m = True :=
  Eq.trans
    (Eq.cong (c => (Nat.leq m 9218868437227405312 || Nat.equal m 9221120237041090560) || c)
      (Bool.andIntro (Nat.leq 9223372036854775808 m) (Nat.leq m 18442240474082181120) h1 h2))
    (Bool.orTrue (Nat.leq m 9218868437227405312 || Nat.equal m 9221120237041090560))

-- A valid pattern with the sign bit set is at most -infinity.
theorem Float.highBound (n: Nat) (v: Float.isValid n = True) (hk: 9223372036854775808 <= n):
    n <= 18442240474082181120 :=
  let v2: ((Nat.leq n 9218868437227405312 || Nat.equal n 9221120237041090560)
      || (Nat.leq 9223372036854775808 n && Nat.leq n 18442240474082181120)) = True := v
  let a: Nat.leq n 9218868437227405312 = False := omega
  let e: Nat.equal n 9221120237041090560 = False :=
    Bool.falseOfNotTrue (Nat.equal n 9221120237041090560) (h => omega)
  omega [rewrite a, e at v2]

-- A valid pattern other than the NaN, with the sign bit clear, is at most
-- +infinity.
theorem Float.lowBound (n: Nat) (v: Float.isValid n = True) (e: Nat.equal n 9221120237041090560 = False)
    (hk: Nat.leq 9223372036854775808 n = False): n <= 9218868437227405312 :=
  let v2: ((Nat.leq n 9218868437227405312 || Nat.equal n 9221120237041090560)
      || (Nat.leq 9223372036854775808 n && Nat.leq n 18442240474082181120)) = True := v
  match a: Nat.leq n 9218868437227405312 with
    | True => rfl
    | False => Void.exfalso (Bool.falseNotTrue (rewrite e, hk at v2))

theorem Float.flipHigh (m: Nat) (h: 9223372036854775808 <= m):
    Float.flipSignBits m = m - 9223372036854775808 :=
  Eq.cong (b => if b then m - 9223372036854775808 else m + 9223372036854775808) h

theorem Float.flipLow (m: Nat) (h: Nat.leq 9223372036854775808 m = False):
    Float.flipSignBits m = m + 9223372036854775808 :=
  Eq.cong (b => if b then m - 9223372036854775808 else m + 9223372036854775808) h

-- Flipping the sign of a valid pattern other than the NaN gives a valid
-- pattern, and not the NaN; flipping it twice gives it back.
theorem Float.flipValidFrom (n: Nat) (v: Float.isValid n = True) (e: Nat.equal n 9221120237041090560 = False):
    (b: Bool) -> Nat.leq 9223372036854775808 n = b
      -> Float.isValid (if b then n - 9223372036854775808 else n + 9223372036854775808) = True
  | True, hk => Float.validLow (n - 9223372036854775808) (omega [Float.highBound n v hk])
  | False, hk => Float.validHigh (n + 9223372036854775808) omega (omega [Float.lowBound n v e hk])

theorem Float.flipValid (n: Nat) (v: Float.isValid n = True) (e: Nat.equal n 9221120237041090560 = False):
    Float.isValid (Float.flipSignBits n) = True :=
  Float.flipValidFrom n v e (Nat.leq 9223372036854775808 n) rfl

theorem Float.flipNotNaNFrom (n: Nat) (v: Float.isValid n = True):
    (b: Bool) -> Nat.leq 9223372036854775808 n = b
      -> Nat.equal (if b then n - 9223372036854775808 else n + 9223372036854775808) 9221120237041090560 = False
  | True, hk =>
    Bool.falseOfNotTrue (Nat.equal (n - 9223372036854775808) 9221120237041090560)
      (h => omega [Float.highBound n v hk])
  | False, hk =>
    Bool.falseOfNotTrue (Nat.equal (n + 9223372036854775808) 9221120237041090560) (h => omega)

theorem Float.flipNotNaN (n: Nat) (v: Float.isValid n = True):
    Nat.equal (Float.flipSignBits n) 9221120237041090560 = False :=
  Float.flipNotNaNFrom n v (Nat.leq 9223372036854775808 n) rfl

theorem Float.flipFlipFrom (n: Nat) (v: Float.isValid n = True):
    (b: Bool) -> Nat.leq 9223372036854775808 n = b
      -> Float.flipSignBits (if b then n - 9223372036854775808 else n + 9223372036854775808) = n
  | True, hk => rewrite Float.flipLow (n - 9223372036854775808) (omega [Float.highBound n v hk]) in omega
  | False, hk => rewrite Float.flipHigh (n + 9223372036854775808) omega in omega

theorem Float.flipFlip (n: Nat) (v: Float.isValid n = True): Float.flipSignBits (Float.flipSignBits n) = n :=
  Float.flipFlipFrom n v (Nat.leq 9223372036854775808 n) rfl

-- Clearing the sign of a valid pattern gives a valid pattern (the NaN's
-- sign is clear already).
theorem Float.clearValidFrom (n: Nat) (v: Float.isValid n = True):
    (b: Bool) -> Nat.leq 9223372036854775808 n = b
      -> Float.isValid (if b then n - 9223372036854775808 else n) = True
  | True, hk => Float.validLow (n - 9223372036854775808) (omega [Float.highBound n v hk])
  | False, hk => v

theorem Float.clearValid (n: Nat) (v: Float.isValid n = True): Float.isValid (Float.clearSignBits n) = True :=
  Float.clearValidFrom n v (Nat.leq 9223372036854775808 n) rfl

-- `-x`: the sign flipped, and the NaN for the NaN (flipping its sign bit
-- would give a pattern `isValid` refuses).
def Float.negFrom (x: Float): (b: Bool) -> Float.isNaN x = b -> Float
  | True, _ => Float.nan
  | False, e => Float.make (Float.flipSignBits x.bits) (Float.flipValid x.bits x.valid e)

def Float.neg (x: Float): Float := Float.negFrom x (Float.isNaN x) rfl

-- `Math.abs`: the sign cleared.
def Float.abs (x: Float): Float := Float.make (Float.clearSignBits x.bits) (Float.clearValid x.bits x.valid)

theorem Float.negNegSecond (x: Float) (e: Float.isNaN x = False):
    (c: Bool) -> (e2: Float.isNaN (Float.make (Float.flipSignBits x.bits) (Float.flipValid x.bits x.valid e)) = c)
      -> Float.negFrom (Float.make (Float.flipSignBits x.bits) (Float.flipValid x.bits x.valid e)) c e2 = x
  | True, e2 => Void.exfalso (Bool.falseNotTrue (Eq.trans (Eq.sym (Float.flipNotNaN x.bits x.valid)) e2))
  | False, e2 =>
    Float.bitsExt (Float.negFrom (Float.make (Float.flipSignBits x.bits) (Float.flipValid x.bits x.valid e)) False e2) x
      (Float.flipFlip x.bits x.valid)

theorem Float.negNegFrom (x: Float): (b: Bool) -> (e: Float.isNaN x = b) -> Float.neg (Float.negFrom x b e) = x
  | True, e => Float.bitsExt Float.nan x (Eq.sym (Nat.equalSound x.bits 9221120237041090560 e))
  | False, e =>
    Float.negNegSecond x e
      (Float.isNaN (Float.make (Float.flipSignBits x.bits) (Float.flipValid x.bits x.valid e))) rfl

theorem Float.negNeg (x: Float): Float.neg (Float.neg x) = x := Float.negNegFrom x (Float.isNaN x) rfl

-- The rounding operations: primitives, with no definition. The kernel
-- computes them on known doubles (rounding to nearest, ties to even, the NaN
-- canonical), and the runtime and JS use the machine's.
def Float.add: Float -> Float -> Float

def Float.sub: Float -> Float -> Float

def Float.mul: Float -> Float -> Float

def Float.div: Float -> Float -> Float

-- JS's `%`: the remainder of truncating division, with the sign of the
-- dividend (`-5.5 % 2.0` is `-1.5`). Exact, like `floor`.
def Float.rem: Float -> Float -> Float

-- JS's `Math.floor`, `Math.ceil`, `Math.trunc` and `Math.round`: a whole
-- double (NaN, the infinities and the zeros as they are). `round` takes a
-- half up, towards +infinity (`round (-2.5)` is `-2.0`), and keeps the sign
-- of a zero result (`round (-0.4)` is `-0.0`).
def Float.floor: Float -> Float

def Float.ceil: Float -> Float

def Float.trunc: Float -> Float

def Float.round: Float -> Float

-- The double nearest the integer, ties to even, or an infinity beyond the
-- largest (JS's `Number(n)` of a `bigint`).
def Float.ofInt: Int -> Float

def Float.ofNat: Nat -> Float

-- JS's `String(x)`: `0.30000000000000004`, `1e+21`, `NaN`, `-Infinity`, and
-- `0` for both zeros. The checker doesn't compute it (each runtime supplies
-- it; docs/proposals/float.md §2.6), so a test about its result runs only at
-- run time.
def Float.toText: Float -> Text

-- Neither infinite nor the NaN.
def Float.isFinite (x: Float): Bool := !(Nat.leq 9218868437227405312 (Float.clearSignBits x.bits))

-- IEEE 754's `totalOrder` as an `Int`: -infinity < ... < -0.0 < 0.0 < ...
-- < +infinity < the NaN. A pattern with the sign bit set is `-(m + 1)` for
-- its magnitude `m`, so `-0.0` is `-1`.
def Float.keyOf (n: Nat) (negative: Bool): Int :=
  if negative then NegSucc (n - 9223372036854775808) else OfNat n

def Float.orderKey (x: Float): Int := Float.keyOf x.bits (Nat.leq 9223372036854775808 x.bits)

theorem Float.keyOfInjective (a: Nat) (b: Nat):
    (p: Bool) -> Nat.leq 9223372036854775808 a = p -> (q: Bool) -> Nat.leq 9223372036854775808 b = q
      -> Float.keyOf a p = Float.keyOf b q -> a = b
  | True, hp, True, hq, e =>
    omega [Int.negSuccInjective (a - 9223372036854775808) (b - 9223372036854775808) e]
  | True, hp, False, hq, e => Void.exfalso (Int.negSuccNotOfNat (a - 9223372036854775808) b e)
  | False, hp, True, hq, e => Void.exfalso (Int.ofNatNotNegSucc a (b - 9223372036854775808) e)
  | False, hp, False, hq, e => Int.ofNatInjective a b e

theorem Float.orderKeyInjective (x: Float) (y: Float) (e: Float.orderKey x = Float.orderKey y): x = y :=
  Float.bitsExt x y
    (Float.keyOfInjective x.bits y.bits (Nat.leq 9223372036854775808 x.bits) rfl
      (Nat.leq 9223372036854775808 y.bits) rfl e)

-- The total order: what `<`, `<=`, sorting, `Map Float` and `Set Float`
-- use. `-0.0 < 0.0`, and the NaN is above everything, equal to itself.
def Float.compare (x: Float) (y: Float): Ordering := Int.compare (Float.orderKey x) (Float.orderKey y)

instance Float.instOrd: Ord Float :=
  Ord.fromCompare Float.compare
    (x y h => Float.orderKeyInjective x y (Int.compareEqual (Float.orderKey x) (Float.orderKey y) h))
    (x y => Int.compareFlip (Float.orderKey x) (Float.orderKey y))
    (x y z => Int.compareTrans (Float.orderKey x) (Float.orderKey y) (Float.orderKey z))

-- JavaScript's `<` and `<=`: false when either is the NaN, and `0.0` and
-- `-0.0` are equal. Port `a > b` as `Float.ieeeLt b a` (docs/syntax.md).
def Float.ieeeLt (x: Float) (y: Float): Bool :=
  !(Float.isNaN x) && !(Float.isNaN y) && !(Float.isZero x && Float.isZero y)
    && Int.less (Float.orderKey x) (Float.orderKey y)

def Float.ieeeLe (x: Float) (y: Float): Bool :=
  !(Float.isNaN x) && !(Float.isNaN y)
    && ((Float.isZero x && Float.isZero y) || Int.leq (Float.orderKey x) (Float.orderKey y))

theorem Float.keyLessLeq: (i: Int) -> (j: Int) -> Int.less i j = True -> Int.leq i j = True
  | OfNat m, OfNat n, h => omega
  | OfNat m, NegSucc n, h => Void.exfalso (Bool.falseNotTrue h)
  | NegSucc m, OfNat n, h => rfl
  | NegSucc m, NegSucc n, h => omega

theorem Float.ltLeBools: (a: Bool) -> (b: Bool) -> (c: Bool) -> (i: Int) -> (j: Int)
    -> (a && b && !c && Int.less i j) = True -> (a && b && (c || Int.leq i j)) = True
  | True, True, False, i, j, h => Float.keyLessLeq i j h
  | True, True, True, i, j, h => rfl
  | True, False, c, i, j, h => Void.exfalso (Bool.falseNotTrue h)
  | False, b, c, i, j, h => Void.exfalso (Bool.falseNotTrue h)

-- JS's `a < b` implies `a <= b`.
theorem Float.ieeeLtLe (x: Float) (y: Float) (h: Float.ieeeLt x y = True): Float.ieeeLe x y = True :=
  Float.ltLeBools (!(Float.isNaN x)) (!(Float.isNaN y)) (Float.isZero x && Float.isZero y)
    (Float.orderKey x) (Float.orderKey y) h

-- `m / d`, if `d` (positive) divides `m`.
def Float.exactDiv (m: Nat) (d: Nat): Option Nat :=
  if Nat.equal (Nat.divFuel m m d * d) m then Some (Nat.divFuel m m d) else None

-- The integer `m * 2^(e - 1075)`, if it is one: a normal double's value,
-- from its exponent field `e` and its significand `m` (the fraction with
-- the leading 1).
def Float.wholeMagnitude (e: Nat) (m: Nat): Option Nat :=
  if Nat.leq 1075 e then Some (m * Nat.pow 2 (e - 1075)) else Float.exactDiv m (Nat.pow 2 (1075 - e))

def Float.withSign (negative: Bool) (n: Nat): Int := if negative then Int.neg (OfNat n) else OfNat n

-- From the sign and the exponent field `e`, and the rest of the bits, `m =
-- e * 2^52 + f`.
def Float.toIntFrom (negative: Bool) (e: Nat) (m: Nat): Option Int :=
  if Nat.equal e 2047 then None
  else if Nat.equal e 0 then (if Nat.equal m 0 then Some (OfNat 0) else None)
  else match Float.wholeMagnitude e (m - e * 4503599627370496 + 4503599627370496) with
    | Some n => Some (Float.withSign negative n)
    | None => None

-- The integer the double is, if it is a whole number: `None` for a
-- fraction, the infinities and the NaN. Every whole double, of any size:
-- `Float.toInt 1e100` is the integer 1e100's bits stand for, which isn't
-- 10^100. Both zeros are `Some 0`.
def Float.toInt (x: Float): Option Int :=
  Float.toIntFrom (Nat.leq 9223372036854775808 x.bits)
    (Nat.divFuel (Float.clearSignBits x.bits) (Float.clearSignBits x.bits) 4503599627370496)
    (Float.clearSignBits x.bits)

-- `toInt`, if the integer is a `SafeInt` (or a `SafeNat`).
def Float.toSafeInt (x: Float): Option SafeInt :=
  match Float.toInt x with
    | Some n => SafeInt.ofInt n
    | None => None

def Float.toSafeNat (x: Float): Option SafeNat :=
  match Float.toInt x with
    | Some (OfNat n) => SafeNat.ofNat n
    | _ => None

-- Exact: every safe integer is a double.
def SafeInt.toFloat (n: SafeInt): Float := Float.ofInt n.value

def SafeNat.toFloat (n: SafeNat): Float := Float.ofNat n.value

-- `toText` with `.0` after a whole number, so that it reads back as a
-- `Float` (`3.0`, `1e+21`, `0.5`).
def Float.pointed (t: Text): Text :=
  if Text.contains "." t || Text.contains "e" t then t else Text.append t ".0"

-- Source for the double that reads back as the same double: `1.5`, `3.0`,
-- `-0.0`, `Float.nan`, `Float.infinity`, `-Float.infinity`. The last four
-- are decided from the bits, so the checker computes them; the rest go
-- through `toText`.
def Float.toSource (x: Float): Text :=
  if Nat.equal x.bits 9221120237041090560 then "Float.nan"
  else if Nat.equal x.bits 9218868437227405312 then "Float.infinity"
  else if Nat.equal x.bits 18442240474082181120 then "-Float.infinity"
  else if Nat.equal x.bits 9223372036854775808 then "-0.0"
  else Float.pointed (Float.toText x)

instance Float.instShow: Show Float := { toText = Float.toText, toSource = Float.toSource }
