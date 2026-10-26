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
  (Nat.leq n 9218868437227405312 ∨ Nat.equal n 9221120237041090560)
    ∨ (Nat.leq 9223372036854775808 n ∧ Nat.leq n 18442240474082181120)

type Float = { bits: Nat, valid: Float.isValid bits = True }

-- The witness `Float.make` puts in a record: on a known `b` it is
-- `Eq.refl True` whatever `p` is, so every way of building a `Float` with
-- known bits (a literal, a primitive's result, a definition, a native) gives
-- the same record (docs/proposals/float.md §3.4, D731).
def Bool.canonicalTrue: (b: Bool) → b = True → b = True
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
    (q: Float.isValid b = True) → ({ bits = a, valid = p }: Float) = { bits = b, valid = q } :=
  J (b' e' => (q': Float.isValid b' = True) → ({ bits = a, valid = p }: Float) = { bits = b', valid = q' })
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
def Float.decEqFrom (x: Float) (y: Float): Decidable (x.bits = y.bits) → Decidable (x = y)
  | Yes h => Yes (Float.bitsExt x y h)
  | No h => No (Float.bitsNe x y h)

def Float.decEq (x: Float) (y: Float): Decidable (x = y) := Float.decEqFrom x y (Nat.decEq x.bits y.bits)

instance Float.instDecEq: DecEq Float := { decide = Float.decEq }

-- JavaScript's `===`: the NaN is not equal to itself, and `0.0` equals `-0.0`.
def Float.isZero (x: Float): Bool := Nat.equal x.bits 0 ∨ Nat.equal x.bits 9223372036854775808

def Float.ieeeEq (x: Float) (y: Float): Bool :=
  ¬(Float.isNaN x) ∧ (Nat.equal x.bits y.bits ∨ (Float.isZero x ∧ Float.isZero y))

-- The sign bit flipped, and cleared.
def Float.flipSignBits (n: Nat): Nat :=
  if Nat.leq 9223372036854775808 n then n - 9223372036854775808 else n + 9223372036854775808

def Float.clearSignBits (n: Nat): Nat :=
  if Nat.leq 9223372036854775808 n then n - 9223372036854775808 else n

theorem Float.validLow (m: Nat) (h: m ≤ 9218868437227405312): Float.isValid m = True :=
  Eq.cong (b => (b ∨ Nat.equal m 9221120237041090560)
    ∨ (Nat.leq 9223372036854775808 m ∧ Nat.leq m 18442240474082181120)) h

theorem Float.validHigh (m: Nat) (h1: 9223372036854775808 ≤ m) (h2: m ≤ 18442240474082181120):
    Float.isValid m = True :=
  Eq.trans
    (Eq.cong (c => (Nat.leq m 9218868437227405312 ∨ Nat.equal m 9221120237041090560) ∨ c)
      (Bool.andIntro (Nat.leq 9223372036854775808 m) (Nat.leq m 18442240474082181120) h1 h2))
    (Bool.orTrue (Nat.leq m 9218868437227405312 ∨ Nat.equal m 9221120237041090560))

-- A valid pattern with the sign bit set is at most -infinity.
theorem Float.highBound (n: Nat) (v: Float.isValid n = True) (hk: 9223372036854775808 ≤ n):
    n ≤ 18442240474082181120 :=
  let v2: ((Nat.leq n 9218868437227405312 ∨ Nat.equal n 9221120237041090560)
    ∨ (Nat.leq 9223372036854775808 n ∧ Nat.leq n 18442240474082181120)) = True := v
  let a: Nat.leq n 9218868437227405312 = False := omega
  let e: Nat.equal n 9221120237041090560 = False :=
    Bool.falseOfNotTrue (Nat.equal n 9221120237041090560) (h => omega)
  omega [rewrite a, e at v2]

-- A valid pattern other than the NaN, with the sign bit clear, is at most
-- +infinity.
theorem Float.lowBound (n: Nat) (v: Float.isValid n = True) (e: Nat.equal n 9221120237041090560 = False)
    (hk: Nat.leq 9223372036854775808 n = False): n ≤ 9218868437227405312 :=
  let v2: ((Nat.leq n 9218868437227405312 ∨ Nat.equal n 9221120237041090560)
    ∨ (Nat.leq 9223372036854775808 n ∧ Nat.leq n 18442240474082181120)) = True := v
  match a: Nat.leq n 9218868437227405312 with
    | True => rfl
    | False => Void.exfalso (Bool.falseNotTrue (rewrite e, hk at v2))

theorem Float.flipHigh (m: Nat) (h: 9223372036854775808 ≤ m):
    Float.flipSignBits m = m - 9223372036854775808 :=
  Eq.cong (b => if b then m - 9223372036854775808 else m + 9223372036854775808) h

theorem Float.flipLow (m: Nat) (h: Nat.leq 9223372036854775808 m = False):
    Float.flipSignBits m = m + 9223372036854775808 :=
  Eq.cong (b => if b then m - 9223372036854775808 else m + 9223372036854775808) h

-- Flipping the sign of a valid pattern other than the NaN gives a valid
-- pattern, and not the NaN; flipping it twice gives it back.
theorem Float.flipValidFrom (n: Nat) (v: Float.isValid n = True) (e: Nat.equal n 9221120237041090560 = False):
    (b: Bool) → Nat.leq 9223372036854775808 n = b
      → Float.isValid (if b then n - 9223372036854775808 else n + 9223372036854775808) = True
  | True, hk => Float.validLow (n - 9223372036854775808) (omega [Float.highBound n v hk])
  | False, hk => Float.validHigh (n + 9223372036854775808) omega (omega [Float.lowBound n v e hk])

theorem Float.flipValid (n: Nat) (v: Float.isValid n = True) (e: Nat.equal n 9221120237041090560 = False):
    Float.isValid (Float.flipSignBits n) = True :=
  Float.flipValidFrom n v e (Nat.leq 9223372036854775808 n) rfl

theorem Float.flipNotNaNFrom (n: Nat) (v: Float.isValid n = True):
    (b: Bool) → Nat.leq 9223372036854775808 n = b
      → Nat.equal (if b then n - 9223372036854775808 else n + 9223372036854775808) 9221120237041090560 = False
  | True, hk =>
    Bool.falseOfNotTrue (Nat.equal (n - 9223372036854775808) 9221120237041090560)
      (h => omega [Float.highBound n v hk])
  | False, hk =>
    Bool.falseOfNotTrue (Nat.equal (n + 9223372036854775808) 9221120237041090560) (h => omega)

theorem Float.flipNotNaN (n: Nat) (v: Float.isValid n = True):
    Nat.equal (Float.flipSignBits n) 9221120237041090560 = False :=
  Float.flipNotNaNFrom n v (Nat.leq 9223372036854775808 n) rfl

theorem Float.flipFlipFrom (n: Nat) (v: Float.isValid n = True):
    (b: Bool) → Nat.leq 9223372036854775808 n = b
      → Float.flipSignBits (if b then n - 9223372036854775808 else n + 9223372036854775808) = n
  | True, hk => rewrite Float.flipLow (n - 9223372036854775808) (omega [Float.highBound n v hk]) in omega
  | False, hk => rewrite Float.flipHigh (n + 9223372036854775808) omega in omega

theorem Float.flipFlip (n: Nat) (v: Float.isValid n = True): Float.flipSignBits (Float.flipSignBits n) = n :=
  Float.flipFlipFrom n v (Nat.leq 9223372036854775808 n) rfl

-- Clearing the sign of a valid pattern gives a valid pattern (the NaN's
-- sign is clear already).
theorem Float.clearValidFrom (n: Nat) (v: Float.isValid n = True):
    (b: Bool) → Nat.leq 9223372036854775808 n = b
      → Float.isValid (if b then n - 9223372036854775808 else n) = True
  | True, hk => Float.validLow (n - 9223372036854775808) (omega [Float.highBound n v hk])
  | False, hk => v

theorem Float.clearValid (n: Nat) (v: Float.isValid n = True): Float.isValid (Float.clearSignBits n) = True :=
  Float.clearValidFrom n v (Nat.leq 9223372036854775808 n) rfl

-- `-x`: the sign flipped, and the NaN for the NaN (flipping its sign bit
-- would give a pattern `isValid` refuses).
def Float.negFrom (x: Float): (b: Bool) → Float.isNaN x = b → Float
  | True, _ => Float.nan
  | False, e => Float.make (Float.flipSignBits x.bits) (Float.flipValid x.bits x.valid e)

def Float.neg (x: Float): Float := Float.negFrom x (Float.isNaN x) rfl

-- `Math.abs`: the sign cleared.
def Float.abs (x: Float): Float := Float.make (Float.clearSignBits x.bits) (Float.clearValid x.bits x.valid)

theorem Float.negNegSecond (x: Float) (e: Float.isNaN x = False):
    (c: Bool) → (e2: Float.isNaN (Float.make (Float.flipSignBits x.bits) (Float.flipValid x.bits x.valid e)) = c)
      → Float.negFrom (Float.make (Float.flipSignBits x.bits) (Float.flipValid x.bits x.valid e)) c e2 = x
  | True, e2 => Void.exfalso (Bool.falseNotTrue (Eq.trans (Eq.sym (Float.flipNotNaN x.bits x.valid)) e2))
  | False, e2 =>
    Float.bitsExt (Float.negFrom (Float.make (Float.flipSignBits x.bits) (Float.flipValid x.bits x.valid e)) False e2) x
      (Float.flipFlip x.bits x.valid)

theorem Float.negNegFrom (x: Float): (b: Bool) → (e: Float.isNaN x = b) → Float.neg (Float.negFrom x b e) = x
  | True, e => Float.bitsExt Float.nan x (Eq.sym (Nat.equalSound x.bits 9221120237041090560 e))
  | False, e =>
    Float.negNegSecond x e
      (Float.isNaN (Float.make (Float.flipSignBits x.bits) (Float.flipValid x.bits x.valid e))) rfl

theorem Float.negNeg (x: Float): Float.neg (Float.neg x) = x := Float.negNegFrom x (Float.isNaN x) rfl

-- The rounding operations: primitives, with no definition. The kernel
-- computes them on known doubles (rounding to nearest, ties to even, the NaN
-- canonical), and the runtime and JS use the machine's.
def Float.add: Float → Float → Float

def Float.sub: Float → Float → Float

def Float.mul: Float → Float → Float

def Float.div: Float → Float → Float

-- JS's `%`: the remainder of truncating division, with the sign of the
-- dividend (`-5.5 % 2.0` is `-1.5`). Exact, like `floor`.
def Float.rem: Float → Float → Float

-- JS's `Math.floor`, `Math.ceil`, `Math.trunc` and `Math.round`: a whole
-- double (NaN, the infinities and the zeros as they are). `round` takes a
-- half up, towards +infinity (`round (-2.5)` is `-2.0`), and keeps the sign
-- of a zero result (`round (-0.4)` is `-0.0`).
def Float.floor: Float → Float

def Float.ceil: Float → Float

def Float.trunc: Float → Float

def Float.round: Float → Float

-- The double nearest the integer, ties to even, or an infinity beyond the
-- largest (JS's `Number(n)` of a `bigint`).
def Float.ofInt: Int → Float

def Float.ofNat: Nat → Float

-- JS's `String(x)`: `0.30000000000000004`, `1e+21`, `NaN`, `-Infinity`, and
-- `0` for both zeros. The checker doesn't compute it (each runtime supplies
-- it; docs/proposals/float.md §2.6), so a test about its result runs only at
-- run time.
def Float.toText: Float → Text

-- Neither infinite nor the NaN.
def Float.isFinite (x: Float): Bool := ¬(Nat.leq 9218868437227405312 (Float.clearSignBits x.bits))

-- IEEE 754's `totalOrder` as an `Int`: -infinity < ... < -0.0 < 0.0 < ...
-- < +infinity < the NaN. A pattern with the sign bit set is `-(m + 1)` for
-- its magnitude `m`, so `-0.0` is `-1`.
def Float.keyOf (n: Nat) (negative: Bool): Int :=
  if negative then NegSucc (n - 9223372036854775808) else OfNat n

def Float.orderKey (x: Float): Int := Float.keyOf x.bits (Nat.leq 9223372036854775808 x.bits)

theorem Float.keyOfInjective (a: Nat) (b: Nat):
    (p: Bool) → Nat.leq 9223372036854775808 a = p → (q: Bool) → Nat.leq 9223372036854775808 b = q
      → Float.keyOf a p = Float.keyOf b q → a = b
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

-- The total order's `<=` and `<` as `Bool`s, what `x <= y` and `x < y` on
-- `Float` compute (not JS's: `Float.ieeeLe` and `Float.ieeeLt`).
def Float.leq (x: Float) (y: Float): Bool := Int.leq (Float.orderKey x) (Float.orderKey y)

def Float.less (x: Float) (y: Float): Bool := Int.less (Float.orderKey x) (Float.orderKey y)

def Float.LessEq (x: Float) (y: Float): Prop := Float.leq x y = True

def Float.LessThan (x: Float) (y: Float): Prop := Float.less x y = True

instance Float.decLessEq (x: Float) (y: Float): Decidable (Float.LessEq x y) := Bool.decTrue (Float.leq x y)

instance Float.decLessThan (x: Float) (y: Float): Decidable (Float.LessThan x y) := Bool.decTrue (Float.less x y)

-- A record, not `Ord.fromCompare`, so that `<=` and `<` decide by
-- `Float.leq` and `Float.less` directly (one native call each in the
-- runtimes) rather than through `Float.compare`'s `Ordering`.
instance Float.instOrd: Ord Float := {
  compare = Float.compare,
  lessThan = Float.LessThan,
  lessEq = Float.LessEq,
  decLessThan = Float.decLessThan,
  decLessEq = Float.decLessEq,
  equal = x y h => Float.orderKeyInjective x y (Int.compareEqual (Float.orderKey x) (Float.orderKey y) h),
  flip = x y => Int.compareFlip (Float.orderKey x) (Float.orderKey y),
  trans = x y z => Int.compareTrans (Float.orderKey x) (Float.orderKey y) (Float.orderKey z),
  lessThanOf = x y => Int.lessOfCompare (Float.orderKey x) (Float.orderKey y),
  lessThanTo = x y => Int.compareOfLess (Float.orderKey x) (Float.orderKey y),
  lessEqOf = x y => Int.leOfCompare (Float.orderKey x) (Float.orderKey y),
  lessEqTo = x y => Int.compareOfLe (Float.orderKey x) (Float.orderKey y)
}

-- JavaScript's `<` and `<=`: false when either is the NaN, and `0.0` and
-- `-0.0` are equal. Port `a > b` as `Float.ieeeLt b a` (docs/syntax.md).
def Float.ieeeLt (x: Float) (y: Float): Bool :=
  ¬(Float.isNaN x) ∧ ¬(Float.isNaN y) ∧ ¬(Float.isZero x ∧ Float.isZero y)
    ∧ Int.less (Float.orderKey x) (Float.orderKey y)

def Float.ieeeLe (x: Float) (y: Float): Bool :=
  ¬(Float.isNaN x) ∧ ¬(Float.isNaN y)
    ∧ ((Float.isZero x ∧ Float.isZero y) ∨ Int.leq (Float.orderKey x) (Float.orderKey y))

theorem Float.keyLessLeq: (i: Int) → (j: Int) → Int.less i j = True → Int.leq i j = True
  | OfNat m, OfNat n, h => omega
  | OfNat m, NegSucc n, h => Void.exfalso (Bool.falseNotTrue h)
  | NegSucc m, OfNat n, h => rfl
  | NegSucc m, NegSucc n, h => omega

theorem Float.ltLeBools: (a: Bool) → (b: Bool) → (c: Bool) → (i: Int) → (j: Int)
    → (a ∧ b ∧ ¬c ∧ Int.less i j) = True → (a ∧ b ∧ (c ∨ Int.leq i j)) = True
  | True, True, False, i, j, h => Float.keyLessLeq i j h
  | True, True, True, i, j, h => rfl
  | True, False, c, i, j, h => Void.exfalso (Bool.falseNotTrue h)
  | False, b, c, i, j, h => Void.exfalso (Bool.falseNotTrue h)

-- JS's `a < b` implies `a <= b`.
theorem Float.ieeeLtLe (x: Float) (y: Float) (h: Float.ieeeLt x y = True): Float.ieeeLe x y = True :=
  Float.ltLeBools (¬(Float.isNaN x)) (¬(Float.isNaN y)) (Float.isZero x ∧ Float.isZero y)
    (Float.orderKey x) (Float.orderKey y) h

-- JS's `<=` and `<` as `Nat`'s, through a rank of the doubles: -infinity
-- is 0, both zeros are +infinity's bits (9218868437227405312), and
-- +infinity is twice that. A negative double's rank is -infinity's bits
-- less its own; any other's is +infinity's bits plus its own. For doubles
-- other than the NaN, `Float.ieeeLe x y` is `ieeeRank x <= ieeeRank y` and
-- `Float.ieeeLt x y` is `ieeeRank x < ieeeRank y` (`Float.ieeeLeRank` and
-- `Float.rankIeeeLe`, `Float.ieeeLtRank` and `Float.rankIeeeLt`), so the
-- laws below come from `Nat`'s, by `omega`, and so can a program's.
def Float.rankOf (n: Nat): Bool → Nat
  | True => 18442240474082181120 - n
  | False => 9218868437227405312 + n

def Float.ieeeRank (x: Float): Nat := Float.rankOf x.bits (Nat.leq 9223372036854775808 x.bits)

theorem Float.ieeeRankZeros: Float.ieeeRank 0.0 = Float.ieeeRank (-0.0) := rfl

theorem Float.ieeeRankExample: Float.ieeeRank (-Float.infinity) = 0 := rfl

theorem Float.notTrueFalse: (b: Bool) → (¬b) = True → b = False
  | True, h => Void.exfalso (Bool.falseNotTrue h)
  | False, h => rfl

-- Both zeros have the same rank.
theorem Float.rankZero (n: Nat) (z: (Nat.equal n 0 ∨ Nat.equal n 9223372036854775808) = True):
    Float.rankOf n (Nat.leq 9223372036854775808 n) = 9218868437227405312 :=
  Bool.orElim (Nat.equal n 0) (Nat.equal n 9223372036854775808)
    (Float.rankOf n (Nat.leq 9223372036854775808 n) = 9218868437227405312) z
    (e => rewrite Nat.equalSound n 0 e in rfl)
    (e => rewrite Nat.equalSound n 9223372036854775808 e in rfl)

-- The ranks, from the order keys `ieeeLe` and `ieeeLt` compare, and back.
theorem Float.rankLeOfKeys (m: Nat) (n: Nat):
    (p: Bool) → Nat.leq 9223372036854775808 m = p → (q: Bool) → Nat.leq 9223372036854775808 n = q
      → Int.leq (Float.keyOf m p) (Float.keyOf n q) = True → Float.rankOf m p ≤ Float.rankOf n q
  | True, hp, True, hq, h => omega
  | True, hp, False, hq, h => omega
  | False, hp, True, hq, h => Void.exfalso (Bool.falseNotTrue h)
  | False, hp, False, hq, h => omega

theorem Float.rankLtOfKeys (m: Nat) (n: Nat) (vm: Float.isValid m = True)
    (z: ((Nat.equal m 0 ∨ Nat.equal m 9223372036854775808) ∧ (Nat.equal n 0 ∨ Nat.equal n 9223372036854775808)) = False):
    (p: Bool) → Nat.leq 9223372036854775808 m = p → (q: Bool) → Nat.leq 9223372036854775808 n = q
      → Int.less (Float.keyOf m p) (Float.keyOf n q) = True → Float.rankOf m p < Float.rankOf n q
  | True, hp, True, hq, h => omega [Float.highBound m vm hp]
  | True, hp, False, hq, h =>
    match c: Nat.equal n 0 with
      | False => omega
      | True =>
        match d: Nat.equal m 9223372036854775808 with
          | False => omega
          | True =>
            let e0: Nat.equal m 0 = False := Bool.falseOfNotTrue (Nat.equal m 0) (e => omega)
            Void.exfalso (Bool.trueNotFalse (rewrite e0 at z))
  | False, hp, True, hq, h => Void.exfalso (Bool.falseNotTrue h)
  | False, hp, False, hq, h => omega

theorem Float.keysOfRankLe (m: Nat) (n: Nat) (vm: Float.isValid m = True) (vn: Float.isValid n = True):
    (p: Bool) → Nat.leq 9223372036854775808 m = p → (q: Bool) → Nat.leq 9223372036854775808 n = q
      → Float.rankOf m p ≤ Float.rankOf n q
      → (((Nat.equal m 0 ∨ Nat.equal m 9223372036854775808) ∧ (Nat.equal n 0 ∨ Nat.equal n 9223372036854775808))
        ∨ Int.leq (Float.keyOf m p) (Float.keyOf n q)) = True
  | True, hp, True, hq, h =>
    Bool.orRight ((Nat.equal m 0 ∨ Nat.equal m 9223372036854775808) ∧ (Nat.equal n 0 ∨ Nat.equal n 9223372036854775808))
      (Nat.leq (n - 9223372036854775808) (m - 9223372036854775808))
      (omega [Float.highBound m vm hp, Float.highBound n vn hq])
  | True, hp, False, hq, h =>
    Bool.orTrue ((Nat.equal m 0 ∨ Nat.equal m 9223372036854775808) ∧ (Nat.equal n 0 ∨ Nat.equal n 9223372036854775808))
  | False, hp, True, hq, h =>
    let m0: m = 0 := omega
    let nS: n = 9223372036854775808 := omega
    rewrite m0, nS in rfl
  | False, hp, False, hq, h =>
    Bool.orRight ((Nat.equal m 0 ∨ Nat.equal m 9223372036854775808) ∧ (Nat.equal n 0 ∨ Nat.equal n 9223372036854775808))
      (Nat.leq m n) omega

theorem Float.keysOfRankLt (m: Nat) (n: Nat) (vm: Float.isValid m = True) (vn: Float.isValid n = True):
    (p: Bool) → Nat.leq 9223372036854775808 m = p → (q: Bool) → Nat.leq 9223372036854775808 n = q
      → Float.rankOf m p < Float.rankOf n q
      → (¬((Nat.equal m 0 ∨ Nat.equal m 9223372036854775808) ∧ (Nat.equal n 0 ∨ Nat.equal n 9223372036854775808))
        ∧ Int.less (Float.keyOf m p) (Float.keyOf n q)) = True
  | True, hp, True, hq, h =>
    let e0: Nat.equal m 0 = False := Bool.falseOfNotTrue (Nat.equal m 0) (e => omega)
    let eS: Nat.equal m 9223372036854775808 = False :=
      Bool.falseOfNotTrue (Nat.equal m 9223372036854775808) (e => omega [Float.highBound m vm hp])
    rewrite e0, eS in omega [Float.highBound m vm hp]
  | True, hp, False, hq, h =>
    let e0: Nat.equal m 0 = False := Bool.falseOfNotTrue (Nat.equal m 0) (e => omega)
    match c: Nat.equal n 0 with
      | True =>
        let eS: Nat.equal m 9223372036854775808 = False := Bool.falseOfNotTrue (Nat.equal m 9223372036854775808) (e => omega)
        rewrite e0, eS in rfl
      | False =>
        let nS: Nat.equal n 9223372036854775808 = False := Bool.falseOfNotTrue (Nat.equal n 9223372036854775808) (e => omega)
        match d: Nat.equal m 9223372036854775808 with
          | True => rewrite e0, nS in rfl
          | False => rewrite e0 in rfl
  | False, hp, True, hq, h => omega
  | False, hp, False, hq, h =>
    let mS: Nat.equal m 9223372036854775808 = False := Bool.falseOfNotTrue (Nat.equal m 9223372036854775808) (e => omega)
    let n0: Nat.equal n 0 = False := Bool.falseOfNotTrue (Nat.equal n 0) (e => omega)
    let nS: Nat.equal n 9223372036854775808 = False := Bool.falseOfNotTrue (Nat.equal n 9223372036854775808) (e => omega)
    match c: Nat.equal m 0 with
      | True => rewrite n0, nS in omega
      | False => rewrite mS in omega

-- `x <= y` and `x < y` in JS order the ranks.
theorem Float.ieeeLeRank (x: Float) (y: Float) (h: Float.ieeeLe x y = True): Float.ieeeRank x ≤ Float.ieeeRank y :=
  let rest: ((Float.isZero x ∧ Float.isZero y) ∨ Int.leq (Float.orderKey x) (Float.orderKey y)) = True :=
    Bool.andRight (¬(Float.isNaN y)) ((Float.isZero x ∧ Float.isZero y) ∨ Int.leq (Float.orderKey x) (Float.orderKey y))
      (Bool.andRight (¬(Float.isNaN x)) (¬(Float.isNaN y) ∧ ((Float.isZero x ∧ Float.isZero y) ∨ Int.leq (Float.orderKey x) (Float.orderKey y))) h)
  Bool.orElim (Float.isZero x ∧ Float.isZero y) (Int.leq (Float.orderKey x) (Float.orderKey y)) (Float.ieeeRank x ≤ Float.ieeeRank y) rest
    (z => omega [Float.rankZero x.bits (Bool.andLeft (Float.isZero x) (Float.isZero y) z), Float.rankZero y.bits (Bool.andRight (Float.isZero x) (Float.isZero y) z)])
    (l => Float.rankLeOfKeys x.bits y.bits (Nat.leq 9223372036854775808 x.bits) rfl (Nat.leq 9223372036854775808 y.bits) rfl l)

theorem Float.ieeeLtRank (x: Float) (y: Float) (h: Float.ieeeLt x y = True): Float.ieeeRank x < Float.ieeeRank y :=
  let rest: (¬(Float.isZero x ∧ Float.isZero y) ∧ Int.less (Float.orderKey x) (Float.orderKey y)) = True :=
    Bool.andRight (¬(Float.isNaN y)) (¬(Float.isZero x ∧ Float.isZero y) ∧ Int.less (Float.orderKey x) (Float.orderKey y))
      (Bool.andRight (¬(Float.isNaN x)) (¬(Float.isNaN y) ∧ (¬(Float.isZero x ∧ Float.isZero y) ∧ Int.less (Float.orderKey x) (Float.orderKey y))) h)
  Float.rankLtOfKeys x.bits y.bits x.valid
    (Float.notTrueFalse (Float.isZero x ∧ Float.isZero y)
      (Bool.andLeft (¬(Float.isZero x ∧ Float.isZero y)) (Int.less (Float.orderKey x) (Float.orderKey y)) rest))
    (Nat.leq 9223372036854775808 x.bits) rfl (Nat.leq 9223372036854775808 y.bits) rfl
    (Bool.andRight (¬(Float.isZero x ∧ Float.isZero y)) (Int.less (Float.orderKey x) (Float.orderKey y)) rest)

-- And back, for doubles other than the NaN.
theorem Float.rankIeeeLe (x: Float) (y: Float) (nx: Float.isNaN x = False) (ny: Float.isNaN y = False)
    (h: Float.ieeeRank x ≤ Float.ieeeRank y): Float.ieeeLe x y = True :=
  rewrite nx, ny in
  Float.keysOfRankLe x.bits y.bits x.valid y.valid (Nat.leq 9223372036854775808 x.bits) rfl (Nat.leq 9223372036854775808 y.bits) rfl h

theorem Float.rankIeeeLt (x: Float) (y: Float) (nx: Float.isNaN x = False) (ny: Float.isNaN y = False)
    (h: Float.ieeeRank x < Float.ieeeRank y): Float.ieeeLt x y = True :=
  rewrite nx, ny in
  Float.keysOfRankLt x.bits y.bits x.valid y.valid (Nat.leq 9223372036854775808 x.bits) rfl (Nat.leq 9223372036854775808 y.bits) rfl h

-- JS's `<=` and `<` are false when either side is the NaN.
theorem Float.ieeeLeNotNaN (x: Float) (y: Float) (h: Float.ieeeLe x y = True): And (Float.isNaN x = False) (Float.isNaN y = False) :=
  Both (Float.notTrueFalse (Float.isNaN x) (Bool.andLeft (¬(Float.isNaN x)) (¬(Float.isNaN y) ∧ ((Float.isZero x ∧ Float.isZero y) ∨ Int.leq (Float.orderKey x) (Float.orderKey y))) h))
    (Float.notTrueFalse (Float.isNaN y)
      (Bool.andLeft (¬(Float.isNaN y)) ((Float.isZero x ∧ Float.isZero y) ∨ Int.leq (Float.orderKey x) (Float.orderKey y))
        (Bool.andRight (¬(Float.isNaN x)) (¬(Float.isNaN y) ∧ ((Float.isZero x ∧ Float.isZero y) ∨ Int.leq (Float.orderKey x) (Float.orderKey y))) h)))

theorem Float.ieeeLtNotNaN (x: Float) (y: Float) (h: Float.ieeeLt x y = True): And (Float.isNaN x = False) (Float.isNaN y = False) :=
  Float.ieeeLeNotNaN x y (Float.ieeeLtLe x y h)

-- `<` is irreflexive and asymmetric, `<=` reflexive (but on the NaN).
theorem Float.ieeeLtIrrefl (x: Float): Float.ieeeLt x x = False :=
  match h: Float.ieeeLt x x with
    | True => omega [Float.ieeeLtRank x x h]
    | False => rfl

theorem Float.ieeeLtAsymm (x: Float) (y: Float) (h: Float.ieeeLt x y = True): Float.ieeeLt y x = False :=
  match k: Float.ieeeLt y x with
    | True => omega [Float.ieeeLtRank x y h, Float.ieeeLtRank y x k]
    | False => rfl

theorem Float.ieeeLeRefl (x: Float) (nx: Float.isNaN x = False): Float.ieeeLe x x = True :=
  Float.rankIeeeLe x x nx nx (Nat.leRefl (Float.ieeeRank x))

-- Both are transitive, also mixed. (`<=` needs no hypothesis about the NaN:
-- `x <= y` already says neither is the NaN.)
theorem Float.ieeeLtTrans (x: Float) (y: Float) (z: Float) (h1: Float.ieeeLt x y = True) (h2: Float.ieeeLt y z = True): Float.ieeeLt x z = True :=
  Float.rankIeeeLt x z (And.left (Float.ieeeLtNotNaN x y h1)) (And.right (Float.ieeeLtNotNaN y z h2))
    (omega [Float.ieeeLtRank x y h1, Float.ieeeLtRank y z h2])

theorem Float.ieeeLeTrans (x: Float) (y: Float) (z: Float) (h1: Float.ieeeLe x y = True) (h2: Float.ieeeLe y z = True): Float.ieeeLe x z = True :=
  Float.rankIeeeLe x z (And.left (Float.ieeeLeNotNaN x y h1)) (And.right (Float.ieeeLeNotNaN y z h2))
    (omega [Float.ieeeLeRank x y h1, Float.ieeeLeRank y z h2])

theorem Float.ieeeLtLeTrans (x: Float) (y: Float) (z: Float) (h1: Float.ieeeLt x y = True) (h2: Float.ieeeLe y z = True): Float.ieeeLt x z = True :=
  Float.rankIeeeLt x z (And.left (Float.ieeeLtNotNaN x y h1)) (And.right (Float.ieeeLeNotNaN y z h2))
    (omega [Float.ieeeLtRank x y h1, Float.ieeeLeRank y z h2])

theorem Float.ieeeLeLtTrans (x: Float) (y: Float) (z: Float) (h1: Float.ieeeLe x y = True) (h2: Float.ieeeLt y z = True): Float.ieeeLt x z = True :=
  Float.rankIeeeLt x z (And.left (Float.ieeeLeNotNaN x y h1)) (And.right (Float.ieeeLtNotNaN y z h2))
    (omega [Float.ieeeLeRank x y h1, Float.ieeeLtRank y z h2])

-- Without the NaN, `<=` is total: if `x <= y` is false, `y <= x`; and if
-- `x < y` is false, `y <= x`.
theorem Float.ieeeLeTotal (x: Float) (y: Float) (nx: Float.isNaN x = False) (ny: Float.isNaN y = False)
    (h: Float.ieeeLe x y = False): Float.ieeeLe y x = True :=
  Float.rankIeeeLe y x ny nx
    (match c: Nat.leq (Float.ieeeRank x) (Float.ieeeRank y) with
      | True => Void.exfalso (Bool.trueNotFalse (Eq.trans (Eq.sym (Float.rankIeeeLe x y nx ny c)) h))
      | False => omega)

theorem Float.ieeeNotLtLe (x: Float) (y: Float) (nx: Float.isNaN x = False) (ny: Float.isNaN y = False)
    (h: Float.ieeeLt x y = False): Float.ieeeLe y x = True :=
  Float.rankIeeeLe y x ny nx
    (match c: Nat.leq (Succ (Float.ieeeRank x)) (Float.ieeeRank y) with
      | True => Void.exfalso (Bool.trueNotFalse (Eq.trans (Eq.sym (Float.rankIeeeLt x y nx ny c)) h))
      | False => omega)

theorem Float.ieeeLeOr (x: Float) (y: Float) (nx: Float.isNaN x = False) (ny: Float.isNaN y = False):
    Or (Float.ieeeLe x y = True) (Float.ieeeLe y x = True) :=
  match c: Float.ieeeLe x y with
    | True => Inl rfl
    | False => Inr (Float.ieeeLeTotal x y nx ny c)

theorem Float.ieeeLtTransExample: Float.ieeeLt (-1.5) 2.0 = True := Float.ieeeLtTrans (-1.5) (-0.0) 2.0 rfl rfl

theorem Float.ieeeLeTotalExample: Float.ieeeLe 1.0 2.0 = True := Float.ieeeLeTotal 2.0 1.0 rfl rfl rfl

-- `m / divisor`, if `divisor` (positive) divides `m`.
def Float.exactDiv (m: Nat) (divisor: Nat): Option Nat :=
  if Nat.equal (Nat.divFuel m m divisor * divisor) m then Some (Nat.divFuel m m divisor) else None

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
def Float.pointed (text: Text): Text :=
  if Text.contains text "." ∨ Text.contains text "e" then text else Text.append text ".0"

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
