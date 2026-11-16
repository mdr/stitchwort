--| `Float.Theory`: laws about `Float`'s rounding operations, proved from the
--| model (std/Float/Model.sw). The rounding specification says what
--| `Float.Model.roundRatio` computes: the double nearest the exact value,
--| ties to even, an infinity from the overflow threshold on, and the sign
--| rules for zeros. The lemmas about rounding are proved from that
--| specification, and the laws about `Float.add` from those lemmas.

--| A double's value in units of 2^-1074.
def Float.Theory.units (x: Float): Int := Float.Model.units x.bits

-- Powers of two and bit lengths

--| `pow2From` is `Nat.pow 2`, whatever its fuel.
theorem Float.Theory.pow2FromPow ∀ (fuel k: Nat): Float.Model.pow2From fuel k = Nat.pow 2 k := match fuel with
  | Zero => byComputing
  | Succ fuel =>
    match z: Nat.equal k 0 with
      | True => rewrite z.read then byComputing
      | False =>
        let d: Nat := Nat.divFuel k k 2
        let low: d * 2 ≤ k := Nat.divFuelLe k k 2
        let high: k < Succ d * 2 := Nat.divFuelBound k k 2 (Nat.nonzeroOfPos 2 byComputing) (Nat.leRefl k)
        rewrite Float.Theory.pow2FromPow fuel d then
          match odd: Nat.equal (k - d * 2) 0 with
            | True =>
              let e: d + d = k := arithmetic [odd]
              Eq.trans (Nat.powAdd 2 d d).flipped (Eq.cong (Nat.pow 2) e)
            | False =>
              let ne: k - d * 2 ≠ 0 := Nat.equalFalse (k - d * 2) 0 odd
              let e: Succ (d + d) = k := arithmetic
              Eq.trans (Eq.cong (t => t * 2) (Nat.powAdd 2 d d).flipped) (Eq.cong (Nat.pow 2) e)

theorem Float.Theory.pow2Pow ∀ (k: Nat): Float.Model.pow2 k = Nat.pow 2 k := match c: Nat.leq k 65535 with
  | True => Float.Theory.pow2FromPow 16 k
  | False => byComputing

--| Every number is below its power of two.
theorem Float.Theory.ltPow ∀ (n: Nat): n < Nat.pow 2 n := match n with
  | Zero => byComputing
  | Succ n => arithmetic [Float.Theory.ltPow n]

--| `b` is the number of binary digits of a positive `n`: `n < 2^b <= 2n`.
def Float.Theory.IsBitLength (n b: Nat): Prop := (n < Nat.pow 2 b) ∧ (Nat.pow 2 b ≤ n + n)

theorem Float.Theory.bitLengthSlowZero ∀ (fuel: Nat): Float.Model.bitLengthSlow fuel 0 = 0 := match fuel with
  | Zero => byComputing
  | Succ fuel => byComputing

theorem Float.Theory.bitLengthSlowSpec ∀ (fuel n: Nat)
    (pos: 0 < n)
    (h: n < Nat.pow 2 fuel):
    Float.Theory.IsBitLength n (Float.Model.bitLengthSlow fuel n) :=
  match fuel with
    | Zero => arithmetic
    | Succ fuel =>
      let low: Nat.divFuel n n 2 * 2 ≤ n := Nat.divFuelLe n n 2
      let high: n < Succ (Nat.divFuel n n 2) * 2 :=
        Nat.divFuelBound n n 2 (Nat.nonzeroOfPos 2 byComputing) (Nat.leRefl n)
      rewrite Nat.equalOfLess 0 n pos then
        match z: Nat.equal (Nat.divFuel n n 2) 0 with
          | True => rewrite z.read, Float.Theory.bitLengthSlowZero fuel then Both arithmetic arithmetic
          | False =>
            let ne: Nat.divFuel n n 2 ≠ 0 := Nat.equalFalse (Nat.divFuel n n 2) 0 z
            let ih: Float.Theory.IsBitLength (Nat.divFuel n n 2) (Float.Model.bitLengthSlow fuel (Nat.divFuel n n 2)) :=
              Float.Theory.bitLengthSlowSpec fuel (Nat.divFuel n n 2) arithmetic arithmetic
            Both (arithmetic [ih.left]) (arithmetic [ih.right])

--| `powers` are 2^width, 2^(width / 2), …, as `bitLengthBy` needs them.
@[tailrec]
def Float.Theory.powersFit: (powers: List Nat) → (width: Nat) → Bool
  | [], width => True
  | [p, ..rest], width => Nat.equal p (Float.Model.pow2 width) ∧ Float.Theory.powersFit rest (Nat.divFuel width width 2)

theorem Float.Theory.bitLengthBySpec ∀ (powers: List Nat) (width n: Nat)
    (fit: Float.Theory.powersFit powers width = True)
    (pos: 0 < n):
    Float.Theory.IsBitLength n (Float.Model.bitLengthBy powers width n) :=
  match powers with
    | [] => Float.Theory.bitLengthSlowSpec n n pos (Float.Theory.ltPow n)
    | [p, ..rest] =>
      let Both powFit restFit := fit
      let pe: p = Nat.pow 2 width := Eq.trans powFit.read (Float.Theory.pow2Pow width)
      let ppos: 0 < p := rewrite pe then Nat.powSuccPos 1 width
      match z: Nat.equal (Nat.divFuel n n p) 0 with
        | True => Float.Theory.bitLengthBySpec rest (Nat.divFuel width width 2) n restFit pos
        | False =>
          let ne: Nat.divFuel n n p ≠ 0 := Nat.equalFalse (Nat.divFuel n n p) 0 z
          let low: Nat.divFuel n n p * p ≤ n := Nat.divFuelLe n n p
          let high: n < Succ (Nat.divFuel n n p) * p := Nat.divFuelBound n n p (Nat.nonzeroOfPos p ppos) (Nat.leRefl n)
          let ih: Float.Theory.IsBitLength
            (Nat.divFuel n n p)
            (Float.Model.bitLengthBy rest (Nat.divFuel width width 2) (Nat.divFuel n n p)) :=
            Float.Theory.bitLengthBySpec rest (Nat.divFuel width width 2) (Nat.divFuel n n p) restFit arithmetic
          let b: Nat := Float.Model.bitLengthBy rest (Nat.divFuel width width 2) (Nat.divFuel n n p)
          let up: Succ (Nat.divFuel n n p) * p ≤ Nat.pow 2 b * p :=
            Nat.leMulRight (Succ (Nat.divFuel n n p)) (Nat.pow 2 b) p ih.left
          let down: Nat.pow 2 b * p ≤ (Nat.divFuel n n p + Nat.divFuel n n p) * p :=
            Nat.leMulRight (Nat.pow 2 b) (Nat.divFuel n n p + Nat.divFuel n n p) p ih.right
          let split: (Nat.divFuel n n p + Nat.divFuel n n p) * p = Nat.divFuel n n p * p + Nat.divFuel n n p * p :=
            Nat.mulDistribRight (Nat.divFuel n n p) (Nat.divFuel n n p) p
          rewrite Nat.powAdd 2 width b, <- pe then Both arithmetic arithmetic

--| `bitLength` gives the number of binary digits.
theorem Float.Theory.bitLengthSpec ∀ (n: Nat) (pos: 0 < n): Float.Theory.IsBitLength n (Float.Model.bitLength n) :=
  match c: Nat.leq n 65535 with
    | True => Float.Theory.bitLengthSlowSpec 16 n pos arithmetic
    | False => Float.Theory.bitLengthBySpec (Float.Model.squaresFrom 13 2 []) 4096 n byComputing pos

-- Units

-- Below: 2^52 = 4503599627370496 (a normal double's leading significand
-- bit), 2^53 = 9007199254740992, +infinity's bits 9218868437227405312 (2047
-- × 2^52), and the sign bit 2^63 = 9223372036854775808. A known number is
-- kept to the right of `+` and `*` when the other side is unknown, since
-- both recurse on their left.

--| A pattern's value in units of 2^-1074, without its sign: what
--| `Float.Model.units` gives the magnitude.
def Float.Theory.magUnits (m: Nat): Nat :=
  let e: Nat := Nat.divFuel m m 4503599627370496
  let f: Nat := m - e * 4503599627370496
  if Nat.equal e 0 then f else Float.Model.pow2 (e - 1) * (f + 4503599627370496)

theorem Float.Theory.unitsMag ∀ (bits: Nat):
    Float.Model.units bits
      = Int.signed (Float.Model.signBit bits) (Float.Theory.magUnits (Float.Model.magnitude bits)) :=
  byComputing

--| The units of the pattern with exponent field `e` and fraction `f`.
theorem Float.Theory.magUnitsField ∀ (e f: Nat)
    (h: f < 4503599627370496):
    Float.Theory.magUnits (e * 4503599627370496 + f)
      = (if Nat.equal e 0 then f else Nat.pow 2 (e - 1) * (f + 4503599627370496)) :=
  let d: Nat.divFuel (e * 4503599627370496 + f) (e * 4503599627370496 + f) 4503599627370496 = e :=
    Nat.divUnique (e * 4503599627370496 + f) 4503599627370496 e f h byComputing
  rewrite d, (arithmetic: e * 4503599627370496 + f - e * 4503599627370496 = f), Float.Theory.pow2Pow (e - 1) then
    byComputing

--| A normal pattern, exponent field `e + 1`.
theorem Float.Theory.magUnitsFieldNext ∀ (e f: Nat)
    (h: f < 4503599627370496):
    Float.Theory.magUnits (e * 4503599627370496 + 4503599627370496 + f) = Nat.pow 2 e * (f + 4503599627370496) :=
  Eq.trans
    (Eq.cong Float.Theory.magUnits
      (arithmetic: e * 4503599627370496 + 4503599627370496 + f = (e + 1) * 4503599627370496 + f))
    (Eq.trans (Float.Theory.magUnitsField (e + 1) f h) byComputing)

--| A subnormal's units are its bits.
theorem Float.Theory.magUnitsLow ∀ (q: Nat) (h: q < 4503599627370496): Float.Theory.magUnits q = q :=
  Float.Theory.magUnitsField 0 q h

--| `e × 2^52 + q`, for a significand `q` with its leading bit, is
--| `2^e × q` units.
theorem Float.Theory.magUnitsNormal ∀ (e q: Nat)
    (lo: 4503599627370496 ≤ q)
    (hi: q < 9007199254740992):
    Float.Theory.magUnits (e * 4503599627370496 + q) = Nat.pow 2 e * q :=
  Eq.trans
    (Eq.cong Float.Theory.magUnits
      (arithmetic: e * 4503599627370496 + q = e * 4503599627370496 + 4503599627370496 + (q - 4503599627370496)))
    (Eq.trans
      (Float.Theory.magUnitsFieldNext e (q - 4503599627370496) arithmetic)
      (Eq.cong (t => Nat.pow 2 e * t) (arithmetic: q - 4503599627370496 + 4503599627370496 = q)))

--| The first pattern of exponent field `e + 1`, and of `e + 2`.
theorem Float.Theory.magUnitsWholeAt ∀ (e z: Nat)
    (hz: z = 0):
    Float.Theory.magUnits (e * 4503599627370496 + 4503599627370496 + z) = Nat.pow 2 e * 4503599627370496 :=
  Eq.trans
    (Float.Theory.magUnitsFieldNext e z (arithmetic: z < 4503599627370496))
    (Eq.trans
      (algebra: Nat.pow 2 e * (z + 4503599627370496) = z * Nat.pow 2 e + Nat.pow 2 e * 4503599627370496)
      (Eq.cong (t => t * Nat.pow 2 e + Nat.pow 2 e * 4503599627370496) hz))

theorem Float.Theory.magUnitsWhole ∀ (e: Nat):
    Float.Theory.magUnits (e * 4503599627370496 + 4503599627370496) = Nat.pow 2 e * 4503599627370496 :=
  Eq.trans
    (Eq.cong Float.Theory.magUnits
      (arithmetic: e * 4503599627370496 + 4503599627370496 = e * 4503599627370496 + 4503599627370496 + 0))
    (Float.Theory.magUnitsWholeAt e 0 byComputing)

theorem Float.Theory.magUnitsCarry ∀ (e: Nat):
    Float.Theory.magUnits (e * 4503599627370496 + 9007199254740992) = Nat.pow 2 e * 9007199254740992 :=
  Eq.trans
    (Eq.cong Float.Theory.magUnits
      (arithmetic: e * 4503599627370496 + 9007199254740992 = (e + 1) * 4503599627370496 + 4503599627370496))
    (Eq.trans
      (Float.Theory.magUnitsWhole (e + 1))
      (Eq.trans
        (Eq.cong (t => Nat.pow 2 t * 4503599627370496) (Nat.addOne e))
        (algebra: Nat.pow 2 e * 2 * 4503599627370496 = Nat.pow 2 e * 9007199254740992)))

--| A pattern as its exponent field and fraction.
theorem Float.Theory.magUnitsSplit ∀ (m e: Nat)
    (low: e * 4503599627370496 ≤ m)
    (high: m < e * 4503599627370496 + 4503599627370496):
    Float.Theory.magUnits m
      = (if Nat.equal e 0 then m - e * 4503599627370496
         else Nat.pow 2 (e - 1) * (m - e * 4503599627370496 + 4503599627370496)) :=
  Eq.trans
    (Eq.cong Float.Theory.magUnits (arithmetic: m = e * 4503599627370496 + (m - e * 4503599627370496)))
    (Float.Theory.magUnitsField e (m - e * 4503599627370496) arithmetic)

theorem Float.Theory.magUnitsStepWithin ∀ (m e: Nat)
    (low: e * 4503599627370496 ≤ m)
    (high: Succ m < e * 4503599627370496 + 4503599627370496):
    Float.Theory.magUnits m < Float.Theory.magUnits (Succ m) :=
  rewrite Float.Theory.magUnitsSplit m e low arithmetic,
      Float.Theory.magUnitsSplit (Succ m) e arithmetic high,
      (arithmetic: Succ m - e * 4503599627370496 + 4503599627370496
        = Succ (m - e * 4503599627370496 + 4503599627370496)) then
    match z: Nat.equal e 0 with
      | True => arithmetic
      | False =>
        arithmetic [
          Nat.powSuccPos 1 (e - 1),
          (algebra: Nat.pow 2 (e - 1) * Succ (m - e * 4503599627370496 + 4503599627370496)
            = Nat.pow 2 (e - 1) * (m - e * 4503599627370496 + 4503599627370496) + Nat.pow 2 (e - 1))
        ]

theorem Float.Theory.magUnitsStepAcross ∀ (m e: Nat)
    (low: e * 4503599627370496 ≤ m)
    (full: Succ m = e * 4503599627370496 + 4503599627370496):
    Float.Theory.magUnits m < Float.Theory.magUnits (Succ m) :=
  rewrite Float.Theory.magUnitsSplit m e low arithmetic,
      (Eq.trans (Eq.cong Float.Theory.magUnits full) (Float.Theory.magUnitsWhole e): Float.Theory.magUnits (Succ m)
        = Nat.pow 2 e * 4503599627370496) then
    match z: Nat.equal e 0 with
      | True => rewrite z.read then arithmetic
      | False =>
        rewrite (Eq.cong (Nat.pow 2) (arithmetic: e = Succ (e - 1)): Nat.pow 2 e = Nat.pow 2 (Succ (e - 1))) then
          arithmetic [
            Nat.powSuccPos 1 (e - 1),
            (algebra: Nat.pow 2 (e - 1) * (m - e * 4503599627370496 + 4503599627370496)
              = (m - e * 4503599627370496) * Nat.pow 2 (e - 1) + Nat.pow 2 (e - 1) * 4503599627370496),
            (Eq.cong
              (t => Nat.pow 2 (e - 1) * t)
              (arithmetic: Succ (m - e * 4503599627370496) = 4503599627370496): Nat.pow 2 (e - 1)
              * Succ (m - e * 4503599627370496)
              = Nat.pow 2 (e - 1) * 4503599627370496),
            (algebra: Nat.pow 2 (e - 1) * Succ (m - e * 4503599627370496)
              = Nat.pow 2 (e - 1) * (m - e * 4503599627370496) + Nat.pow 2 (e - 1))
          ]

--| The next pattern has more units.
theorem Float.Theory.magUnitsStep ∀ (m: Nat): Float.Theory.magUnits m < Float.Theory.magUnits (Succ m) :=
  match c: Nat.equal (Succ m) (Nat.divFuel m m 4503599627370496 * 4503599627370496 + 4503599627370496) with
    | True =>
      Float.Theory.magUnitsStepAcross m
        (Nat.divFuel m m 4503599627370496)
        (Nat.divFuelLe m m 4503599627370496)
        (Nat.equalSound (Succ m) (Nat.divFuel m m 4503599627370496 * 4503599627370496 + 4503599627370496) c)
    | False =>
      Float.Theory.magUnitsStepWithin m
        (Nat.divFuel m m 4503599627370496)
        (Nat.divFuelLe m m 4503599627370496)
        (arithmetic [
          Nat.divFuelBound m m 4503599627370496 (Nat.nonzeroOfPos 4503599627370496 byComputing) (Nat.leRefl m),
          Nat.equalFalse (Succ m) (Nat.divFuel m m 4503599627370496 * 4503599627370496 + 4503599627370496) c
        ])

theorem Float.Theory.magUnitsAbove ∀ (k m: Nat): Float.Theory.magUnits m < Float.Theory.magUnits (Succ k + m) :=
  match k with
    | Zero => Float.Theory.magUnitsStep m
    | Succ k =>
      Nat.lessTrans
        (Float.Theory.magUnits m)
        (Float.Theory.magUnits (Succ k + m))
        (Float.Theory.magUnits (Succ (Succ k) + m))
        (Float.Theory.magUnitsAbove k m)
        (Float.Theory.magUnitsStep (Succ k + m))

--| `magUnits` is strictly increasing.
theorem Float.Theory.magUnitsLess ∀ (m n: Nat) (h: m < n): Float.Theory.magUnits m < Float.Theory.magUnits n :=
  rewrite (arithmetic: n = Succ (n - Succ m) + m) then Float.Theory.magUnitsAbove (n - Succ m) m

theorem Float.Theory.magUnitsLe ∀ (m n: Nat) (h: m ≤ n): Float.Theory.magUnits m ≤ Float.Theory.magUnits n :=
  match c: Nat.equal m n with
    | True => rewrite c.read then Nat.leRefl (Float.Theory.magUnits n)
    | False => arithmetic [Float.Theory.magUnitsLess m n (arithmetic [Nat.equalFalse m n c])]

--| `magUnits` reflects order: patterns whose units are in order are in order.
theorem Float.Theory.magUnitsLeReflect ∀ (m n: Nat) (h: Float.Theory.magUnits m ≤ Float.Theory.magUnits n): m ≤ n :=
  match c: Nat.leq m n with
    | True => arithmetic [c]
    | False => arithmetic [Float.Theory.magUnitsLess n m (arithmetic [c])]

theorem Float.Theory.magUnitsInjective ∀ (m n: Nat) (e: Float.Theory.magUnits m = Float.Theory.magUnits n): m = n :=
  arithmetic [Float.Theory.magUnitsLeReflect m n (arithmetic [e]), Float.Theory.magUnitsLeReflect n m (arithmetic [e])]

--| The pattern `e × 2^52 + q`, for `q ≤ 2^53` with its leading bit unless
--| `e` is 0, is `2^e × q` units.
theorem Float.Theory.magUnitsGrid ∀ (e q: Nat)
    (hq: q ≤ 9007199254740992)
    (lead: (e = 0) ∨ (4503599627370496 ≤ q)):
    Float.Theory.magUnits (e * 4503599627370496 + q) = Nat.pow 2 e * q :=
  match c: Nat.leq 4503599627370496 q with
    | False =>
      match lead with
        | Inl z => rewrite z then Eq.trans (Float.Theory.magUnitsLow q (arithmetic [c])) (arithmetic: q = 1 * q)
        | Inr l => Void.impossible (arithmetic [l, c])
    | True =>
      match d: Nat.equal q 9007199254740992 with
        | True => rewrite d.read then Float.Theory.magUnitsCarry e
        | False => Float.Theory.magUnitsNormal e q c (arithmetic [Nat.equalFalse q 9007199254740992 d])

-- The rounding specification

theorem Float.Theory.absDiffDef ∀ (a b: Nat): Nat.absDiff a b = (a - b) + (b - a) := byComputing

theorem Float.Theory.mulLtRight ∀ (a c d: Nat) (h: a < c) (pos: 0 < d): a * d < c * d :=
  arithmetic [Nat.leMulRight (Succ a) c d h, (algebra: Succ a * d = a * d + d)]

--| The pattern's last bit is 0.
def Float.Theory.IsEven (n: Nat): Prop := Nat.equal (n - Nat.divFuel n n 2 * 2) 0 = True

theorem Float.Theory.isEvenOf ∀ (n h: Nat) (e: n = h * 2): Float.Theory.IsEven n :=
  let d: Nat.divFuel n n 2 = h := Nat.divUnique n 2 h 0 byComputing (arithmetic [e])
  rewrite d, (arithmetic [e]: n - h * 2 = 0) then byComputing

--| Halfway between the largest finite double and 2^1024, in units: from
--| here on, a value rounds to infinity.
def Float.Theory.overflowUnits: Nat := Float.Model.pow2 2044 * 18014398509481983

--| What rounding `t / d` units to a magnitude pattern gives.
--| The result is at most infinity's pattern, infinity exactly from the
--| overflow threshold on, and otherwise the nearest finite pattern, the even
--| one of two equally near.
type Float.Theory.RoundsTo (t: Nat) (d: Nat) (r: Nat): Prop = {
  bounded: r ≤ 9218868437227405312,
  overflow: r = 9218868437227405312 → d * Float.Theory.overflowUnits ≤ t,
  inRange: r < 9218868437227405312 → t < d * Float.Theory.overflowUnits,
  nearest: ∀ (m: Nat) => m < 9218868437227405312
    → r < 9218868437227405312
    → Nat.absDiff (Float.Theory.magUnits r * d) t ≤ Nat.absDiff (Float.Theory.magUnits m * d) t,
  tiesEven: ∀ (m: Nat) => m < 9218868437227405312
    → r < 9218868437227405312
    → m ≠ r
    → Nat.absDiff (Float.Theory.magUnits r * d) t = Nat.absDiff (Float.Theory.magUnits m * d) t
    → Float.Theory.IsEven r
}

--| Infinity's pattern if `r` is at it or beyond, as `roundCore` clamps.
def Float.Theory.clamp (r: Nat): Nat := if Nat.leq 9218868437227405312 r then 9218868437227405312 else r

--| Between patterns `p` and `p + 1`, taking the lower: the value is at most
--| halfway, and even `p` at halfway.
def Float.Theory.PickLow (t b p r: Nat): Prop :=
  (r = p)
    ∧ ((t + t ≤ Float.Theory.magUnits p * b + Float.Theory.magUnits (Succ p) * b)
      ∧ (t + t = Float.Theory.magUnits p * b + Float.Theory.magUnits (Succ p) * b → Float.Theory.IsEven p))

--| Between patterns `p` and `p + 1`, taking the upper: the value is at least
--| halfway, and even `p + 1` at halfway.
def Float.Theory.PickHigh (t b p r: Nat): Prop :=
  (r = Succ p)
    ∧ ((Float.Theory.magUnits p * b + Float.Theory.magUnits (Succ p) * b ≤ t + t)
      ∧ (t + t = Float.Theory.magUnits p * b + Float.Theory.magUnits (Succ p) * b → Float.Theory.IsEven (Succ p)))

theorem Float.Theory.unitsAtInfinity: Float.Theory.magUnits 9218868437227405312 = Float.Model.pow2 2098 := byComputing

theorem Float.Theory.unitsAtLargest: Float.Theory.magUnits 9218868437227405311
      = Float.Model.pow2 2045 * 9007199254740991 :=
  byComputing

theorem Float.Theory.largestOdd: ¬(Float.Theory.IsEven 9218868437227405311) := Bool.falseNotTrue

--| The threshold, times `b`, is halfway between the two patterns' values.
theorem Float.Theory.overflowHalf ∀ (b: Nat):
    Float.Theory.magUnits 9218868437227405311 * b + Float.Theory.magUnits 9218868437227405312 * b
      = b * Float.Theory.overflowUnits + b * Float.Theory.overflowUnits :=
  Eq.trans
    (Eq.flipped
      (Nat.mulDistribRight (Float.Theory.magUnits 9218868437227405311) (Float.Theory.magUnits 9218868437227405312) b))
    (Eq.trans
      (Eq.cong
        (k => k * b)
        (byComputing: Float.Theory.magUnits 9218868437227405311 + Float.Theory.magUnits 9218868437227405312
          = Float.Theory.overflowUnits + Float.Theory.overflowUnits))
      (Eq.trans
        (Nat.mulDistribRight Float.Theory.overflowUnits Float.Theory.overflowUnits b)
        (Eq.cong (k => k + k) (Nat.mulComm Float.Theory.overflowUnits b))))

theorem Float.Theory.largestBelow ∀ (b: Nat)
    (pos: 0 < b):
    Float.Theory.magUnits 9218868437227405311 * b < b * Float.Theory.overflowUnits :=
  J
    (y q => Float.Theory.magUnits 9218868437227405311 * b < y)
    (Float.Theory.mulLtRight (Float.Theory.magUnits 9218868437227405311) Float.Theory.overflowUnits b byComputing pos)
    (Nat.mulComm Float.Theory.overflowUnits b)

theorem Float.Theory.infinityAbove ∀ (b: Nat):
    b * Float.Theory.overflowUnits ≤ Float.Theory.magUnits 9218868437227405312 * b :=
  J
    (y q => y ≤ Float.Theory.magUnits 9218868437227405312 * b)
    (Nat.leMulRight Float.Theory.overflowUnits (Float.Theory.magUnits 9218868437227405312) b byComputing)
    (Nat.mulComm Float.Theory.overflowUnits b)

--| A pattern's value times `b`, against `p`'s.
theorem Float.Theory.scaledLe ∀ (m p b: Nat) (h: m ≤ p): Float.Theory.magUnits m * b ≤ Float.Theory.magUnits p * b :=
  Nat.leMulRight (Float.Theory.magUnits m) (Float.Theory.magUnits p) b (Float.Theory.magUnitsLe m p h)

theorem Float.Theory.scaledLess ∀ (m p b: Nat)
    (h: m < p)
    (pos: 0 < b):
    Float.Theory.magUnits m * b < Float.Theory.magUnits p * b :=
  Float.Theory.mulLtRight (Float.Theory.magUnits m) (Float.Theory.magUnits p) b (Float.Theory.magUnitsLess m p h) pos

theorem Float.Theory.halfLe ∀ (x y z w: Nat) (e: x + y = z + z) (h: x + y ≤ w + w): z ≤ w := arithmetic

theorem Float.Theory.halfLess ∀ (x y z w: Nat) (e: x + y = z + z) (h: w + w ≤ x + y) (ne: w + w ≠ x + y): w < z :=
  arithmetic

theorem Float.Theory.notLessSelf ∀ (n: Nat) (h: n < n): Void := arithmetic

--| Rounding between neighbouring patterns `p` and `p + 1`, at or past
--| infinity's pattern.
theorem Float.Theory.roundsToInfinity ∀ (t b p r: Nat)
    (pos: 0 < b)
    (low: Float.Theory.magUnits p * b ≤ t)
    (hr: 9218868437227405312 ≤ r)
    (pick: (Float.Theory.PickLow t b p r) ∨ (Float.Theory.PickHigh t b p r)):
    Float.Theory.RoundsTo t b 9218868437227405312 :=
  let beyond: 9218868437227405312 ≤ p → b * Float.Theory.overflowUnits ≤ t := hp =>
    Nat.leTrans
      (b * Float.Theory.overflowUnits)
      (Float.Theory.magUnits p * b)
      t
      (Nat.leTrans
        (b * Float.Theory.overflowUnits)
        (Float.Theory.magUnits 9218868437227405312 * b)
        (Float.Theory.magUnits p * b)
        (Float.Theory.infinityAbove b)
        (Float.Theory.scaledLe 9218868437227405312 p b hp))
      low
  let over: (e: 9218868437227405312 = 9218868437227405312) → b * Float.Theory.overflowUnits ≤ t := e =>
    (match pick with
      | Inl (Both er rest) => beyond (arithmetic [er, hr])
      | Inr (Both er (Both h1 h2)) =>
        match c: Nat.leq 9218868437227405312 p with
          | True => beyond (arithmetic [c])
          | False =>
            let ep: p = 9218868437227405311 := arithmetic [er, hr, c]
            Float.Theory.halfLe
              (Float.Theory.magUnits p * b)
              (Float.Theory.magUnits (Succ p) * b)
              (b * Float.Theory.overflowUnits)
              t
              (Eq.trans
                (Eq.cong
                  (k => Float.Theory.magUnits k * b + Float.Theory.magUnits (Succ k) * b)
                  ep: Float.Theory.magUnits p * b + Float.Theory.magUnits (Succ p) * b
                  = Float.Theory.magUnits 9218868437227405311 * b + Float.Theory.magUnits 9218868437227405312 * b)
                (Float.Theory.overflowHalf b))
              h1)
  {
    bounded = Nat.leRefl 9218868437227405312,
    overflow = over,
    inRange = h => Void.impossible (Float.Theory.notLessSelf 9218868437227405312 h),
    nearest = m hm h => Void.impossible (Float.Theory.notLessSelf 9218868437227405312 h),
    tiesEven = m hm h ne e => Void.impossible (Float.Theory.notLessSelf 9218868437227405312 h)
  }

theorem Float.Theory.roundsToFinite ∀ (t b p r: Nat)
    (pos: 0 < b)
    (low: Float.Theory.magUnits p * b ≤ t)
    (high: t < Float.Theory.magUnits (Succ p) * b)
    (hr: r < 9218868437227405312)
    (pick: (Float.Theory.PickLow t b p r) ∨ (Float.Theory.PickHigh t b p r)):
    Float.Theory.RoundsTo t b r :=
  let below: Succ p ≤ 9218868437227405311 → t < b * Float.Theory.overflowUnits := hp =>
    Nat.lessTrans t
      (Float.Theory.magUnits 9218868437227405311 * b)
      (b * Float.Theory.overflowUnits)
      (Nat.leTrans
        (Succ t)
        (Float.Theory.magUnits (Succ p) * b)
        (Float.Theory.magUnits 9218868437227405311 * b)
        high
        (Float.Theory.scaledLe (Succ p) 9218868437227405311 b hp))
      (Float.Theory.largestBelow b pos)
  let inRange: r < 9218868437227405312 → t < b * Float.Theory.overflowUnits := hr2 =>
    (match pick with
      | Inl (Both er (Both h1 h2)) =>
        match c: Nat.leq (Succ p) 9218868437227405311 with
          | True => below (arithmetic [c])
          | False =>
            let ep: p = 9218868437227405311 := arithmetic [er, hr, c]
            let half: Float.Theory.magUnits p * b + Float.Theory.magUnits (Succ p) * b
              = b * Float.Theory.overflowUnits + b * Float.Theory.overflowUnits :=
              Eq.trans
                (Eq.cong
                  (k => Float.Theory.magUnits k * b + Float.Theory.magUnits (Succ k) * b)
                  ep: Float.Theory.magUnits p * b + Float.Theory.magUnits (Succ p) * b
                  = Float.Theory.magUnits 9218868437227405311 * b + Float.Theory.magUnits 9218868437227405312 * b)
                (Float.Theory.overflowHalf b)
            match d: Nat.equal (t + t) (Float.Theory.magUnits p * b + Float.Theory.magUnits (Succ p) * b) with
              | True => Void.impossible (Float.Theory.largestOdd (J (y q => Float.Theory.IsEven y) (h2 d.read) ep))
              | False =>
                Float.Theory.halfLess
                  (Float.Theory.magUnits p * b)
                  (Float.Theory.magUnits (Succ p) * b)
                  (b * Float.Theory.overflowUnits)
                  t
                  half
                  h1
                  (Nat.equalFalse (t + t) (Float.Theory.magUnits p * b + Float.Theory.magUnits (Succ p) * b) d)
      | Inr (Both er rest) => below (arithmetic [er, hr]))
  let lowSide: ∀ (m: Nat) => m ≤ p → Float.Theory.magUnits m * b ≤ Float.Theory.magUnits p * b := m h =>
    Float.Theory.scaledLe m p b h
  let highSide: ∀ (m: Nat) => Succ p ≤ m → Float.Theory.magUnits (Succ p) * b ≤ Float.Theory.magUnits m * b := m h =>
    Float.Theory.scaledLe (Succ p) m b h
  {
    bounded = Nat.lessLe r 9218868437227405312 hr,
    overflow = e => Void.impossible (Float.Theory.notLessSelf r (J (y q => r < y) hr e.flipped)),
    inRange = inRange,
    nearest = m hm h =>
      match pick with
        | Inl (Both er (Both h1 h2)) =>
          rewrite er,
              Float.Theory.absDiffDef (Float.Theory.magUnits p * b) t,
              Float.Theory.absDiffDef (Float.Theory.magUnits m * b) t then
            match c: Nat.leq m p with
              | True => arithmetic [low, high, h1, lowSide m c]
              | False => arithmetic [low, high, h1, highSide m (arithmetic [c])]
        | Inr (Both er (Both h1 h2)) =>
          rewrite er,
              Float.Theory.absDiffDef (Float.Theory.magUnits (Succ p) * b) t,
              Float.Theory.absDiffDef (Float.Theory.magUnits m * b) t then
            match c: Nat.leq m p with
              | True => arithmetic [low, high, h1, lowSide m c]
              | False => arithmetic [low, high, h1, highSide m (arithmetic [c])],
    tiesEven = m hm h ne e =>
      match pick with
        | Inl (Both er (Both h1 h2)) =>
          let e2: Nat.absDiff (Float.Theory.magUnits p * b) t = Nat.absDiff (Float.Theory.magUnits m * b) t :=
            J (y q => Nat.absDiff (Float.Theory.magUnits y * b) t = Nat.absDiff (Float.Theory.magUnits m * b) t) e er
          let d1: Nat.absDiff (Float.Theory.magUnits p * b) t
            = Float.Theory.magUnits p * b - t + (t - Float.Theory.magUnits p * b) :=
            Float.Theory.absDiffDef (Float.Theory.magUnits p * b) t
          let d2: Nat.absDiff (Float.Theory.magUnits m * b) t
            = Float.Theory.magUnits m * b - t + (t - Float.Theory.magUnits m * b) :=
            Float.Theory.absDiffDef (Float.Theory.magUnits m * b) t
          rewrite er then
            match c: Nat.leq m p with
              | True =>
                match z: Nat.equal m p with
                  | True => Void.impossible (ne (arithmetic [er, z]))
                  | False =>
                    Void.impossible
                      (arithmetic [
                        low,
                        high,
                        h1,
                        e2,
                        d1,
                        d2,
                        Float.Theory.scaledLess m p b (arithmetic [c, Nat.equalFalse m p z]) pos
                      ])
              | False => h2 (arithmetic [low, high, h1, e2, d1, d2, highSide m (arithmetic [c])])
        | Inr (Both er (Both h1 h2)) =>
          let e2: Nat.absDiff (Float.Theory.magUnits (Succ p) * b) t = Nat.absDiff (Float.Theory.magUnits m * b) t :=
            J (y q => Nat.absDiff (Float.Theory.magUnits y * b) t = Nat.absDiff (Float.Theory.magUnits m * b) t) e er
          let d1: Nat.absDiff (Float.Theory.magUnits (Succ p) * b) t
            = Float.Theory.magUnits (Succ p) * b - t + (t - Float.Theory.magUnits (Succ p) * b) :=
            Float.Theory.absDiffDef (Float.Theory.magUnits (Succ p) * b) t
          let d2: Nat.absDiff (Float.Theory.magUnits m * b) t
            = Float.Theory.magUnits m * b - t + (t - Float.Theory.magUnits m * b) :=
            Float.Theory.absDiffDef (Float.Theory.magUnits m * b) t
          rewrite er then
            match c: Nat.leq m p with
              | True => h2 (arithmetic [low, high, h1, e2, d1, d2, lowSide m c])
              | False =>
                match z: Nat.equal m (Succ p) with
                  | True => Void.impossible (ne (arithmetic [er, z]))
                  | False =>
                    Void.impossible
                      (arithmetic [
                        low,
                        high,
                        h1,
                        e2,
                        d1,
                        d2,
                        Float.Theory.scaledLess (Succ p) m b (arithmetic [c, Nat.equalFalse m (Succ p) z]) pos
                      ])
  }
--| Rounding to one of two neighbouring patterns, clamped at infinity.
theorem Float.Theory.roundsToNeighbour ∀ (t b p r: Nat)
    (pos: 0 < b)
    (low: Float.Theory.magUnits p * b ≤ t)
    (high: t < Float.Theory.magUnits (Succ p) * b)
    (pick: (Float.Theory.PickLow t b p r) ∨ (Float.Theory.PickHigh t b p r)):
    Float.Theory.RoundsTo t b (Float.Theory.clamp r) :=
  match c: Nat.leq 9218868437227405312 r with
    | True => Float.Theory.roundsToInfinity t b p r pos low c pick
    | False => Float.Theory.roundsToFinite t b p r pos low high (arithmetic [c]) pick

-- The rounding core

theorem Float.Theory.mulLtLeft ∀ (a c d: Nat) (h: a < c) (pos: 0 < d): d * a < d * c :=
  rewrite Nat.mulComm d a, Nat.mulComm d c then Float.Theory.mulLtRight a c d h pos

theorem Float.Theory.mulLeLeft ∀ (a c d: Nat) (h: a ≤ c): d * a ≤ d * c :=
  rewrite Nat.mulComm d a, Nat.mulComm d c then Nat.leMulRight a c d h

theorem Float.Theory.isEvenOfZero ∀ (n: Nat) (e: n - Nat.divFuel n n 2 * 2 = 0): Float.Theory.IsEven n :=
  rewrite e then byComputing

--| An even significand makes an even pattern.
theorem Float.Theory.evenShift ∀ (e q: Nat)
    (h: Float.Theory.IsEven q):
    Float.Theory.IsEven (e * 4503599627370496 + q) :=
  Float.Theory.isEvenOf (e * 4503599627370496 + q) (e * 2251799813685248 + Nat.divFuel q q 2) (arithmetic [h])

--| What `roundsUp` decides: down when below halfway, or at it with `q`
--| even; up when above, or at it with `q` odd.
theorem Float.Theory.locateDown ∀ (q rem b: Nat)
    (pos: 0 < b)
    (h: Float.Model.roundsUp q (Float.Model.locate rem b) = False):
    (rem + rem < b) ∨ ((rem + rem = b) ∧ (Float.Theory.IsEven q)) :=
  match c0: Nat.equal rem 0 with
    | True => Inl (arithmetic [c0, pos])
    | False =>
      match c1: Nat.equal (2 * rem) b with
        | True =>
          Inr
            (Both
              (arithmetic [c1])
              (Float.Theory.isEvenOfZero q (arithmetic [Nat.equalFalse (q - Nat.divFuel q q 2 * 2) 1 h])))
        | False =>
          match c2: Nat.leq (2 * rem) b with
            | True => Inl (arithmetic [c2, Nat.equalFalse (2 * rem) b c1])

theorem Float.Theory.locateUp ∀ (q rem b: Nat)
    (h: Float.Model.roundsUp q (Float.Model.locate rem b) = True):
    (b < rem + rem) ∨ ((rem + rem = b) ∧ (Float.Theory.IsEven (Succ q))) :=
  match c0: Nat.equal rem 0 with
    | False =>
      match c1: Nat.equal (2 * rem) b with
        | True =>
          Inr (Both (arithmetic [c1]) (Float.Theory.isEvenOf (Succ q) (Succ (Nat.divFuel q q 2)) (arithmetic [h])))
        | False =>
          match c2: Nat.leq (2 * rem) b with
            | False => Inl (arithmetic [c2])

--| `roundCore` rounds `2^e × (q + rem / b)` units, given the significand
--| range it assumes.
theorem Float.Theory.roundCoreAt ∀ (e top b q rem: Nat)
    (pos: 0 < b)
    (split: top = q * b + rem)
    (hr: rem < b)
    (hq: q < 9007199254740992)
    (lead: (e = 0) ∨ (4503599627370496 ≤ q)):
    Float.Theory.RoundsTo (Nat.pow 2 e * top) b (Float.Model.roundCore False e q (Float.Model.locate rem b)) :=
  let xpos: 0 < Nat.pow 2 e := Nat.powSuccPos 1 e
  let gl: Float.Theory.magUnits (e * 4503599627370496 + q) * b = Nat.pow 2 e * q * b :=
    Eq.cong (k => k * b) (Float.Theory.magUnitsGrid e q (arithmetic [hq]) lead)
  let gh: Float.Theory.magUnits (Succ (e * 4503599627370496 + q)) * b = Nat.pow 2 e * (q + 1) * b :=
    Eq.trans
      (Eq.cong
        (k => Float.Theory.magUnits k * b)
        (arithmetic: Succ (e * 4503599627370496 + q) = e * 4503599627370496 + (q + 1)))
      (Eq.cong
        (k => k * b)
        (Float.Theory.magUnitsGrid e
          (q + 1)
          (arithmetic [hq])
          (match lead with
            | Inl z => Inl z
            | Inr l => Inr (arithmetic [l]))))
  let te: Nat.pow 2 e * top = Nat.pow 2 e * q * b + Nat.pow 2 e * rem :=
    Eq.trans
      (Eq.cong (k => Nat.pow 2 e * k) split)
      (algebra: Nat.pow 2 e * (q * b + rem) = Nat.pow 2 e * q * b + Nat.pow 2 e * rem)
  let ue: Nat.pow 2 e * (q + 1) * b = Nat.pow 2 e * q * b + Nat.pow 2 e * b := algebra
  let dbl: Nat.pow 2 e * (rem + rem) = Nat.pow 2 e * rem + Nat.pow 2 e * rem := algebra
  let strict: Nat.pow 2 e * rem < Nat.pow 2 e * b := Float.Theory.mulLtLeft rem b (Nat.pow 2 e) hr xpos
  let low: Float.Theory.magUnits (e * 4503599627370496 + q) * b ≤ Nat.pow 2 e * top := arithmetic [gl, te]
  let high: Nat.pow 2 e * top < Float.Theory.magUnits (Succ (e * 4503599627370496 + q)) * b :=
    arithmetic [gh, te, ue, strict]
  match c: Float.Model.roundsUp q (Float.Model.locate rem b) with
    | False =>
      Float.Theory.roundsToNeighbour
        (Nat.pow 2 e * top)
        b
        (e * 4503599627370496 + q)
        (e * 4503599627370496 + q)
        pos
        low
        high
        (Inl
          (Both byComputing
            (match Float.Theory.locateDown q rem b pos c with
              | Inl lt =>
                let m: Nat.pow 2 e * (rem + rem) < Nat.pow 2 e * b :=
                  Float.Theory.mulLtLeft (rem + rem) b (Nat.pow 2 e) lt xpos
                Both (arithmetic [gl, gh, te, ue, dbl, m]) (tie =>
                  Void.impossible (arithmetic [gl, gh, te, ue, dbl, m, tie]))
              | Inr (Both eq ev) =>
                let m: Nat.pow 2 e * (rem + rem) = Nat.pow 2 e * b := Eq.cong (k => Nat.pow 2 e * k) eq
                Both (arithmetic [gl, gh, te, ue, dbl, m]) (tie => Float.Theory.evenShift e q ev))))
    | True =>
      Float.Theory.roundsToNeighbour
        (Nat.pow 2 e * top)
        b
        (e * 4503599627370496 + q)
        (e * 4503599627370496 + (q + 1))
        pos
        low
        high
        (Inr
          (Both
            (arithmetic: e * 4503599627370496 + (q + 1) = Succ (e * 4503599627370496 + q))
            (match Float.Theory.locateUp q rem b c with
              | Inl lt =>
                let m: Nat.pow 2 e * b < Nat.pow 2 e * (rem + rem) :=
                  Float.Theory.mulLtLeft b (rem + rem) (Nat.pow 2 e) lt xpos
                Both (arithmetic [gl, gh, te, ue, dbl, m]) (tie =>
                  Void.impossible (arithmetic [gl, gh, te, ue, dbl, m, tie]))
              | Inr (Both eq ev) =>
                let m: Nat.pow 2 e * (rem + rem) = Nat.pow 2 e * b := Eq.cong (k => Nat.pow 2 e * k) eq
                Both (arithmetic [gl, gh, te, ue, dbl, m]) (tie =>
                  J
                    (y w => Float.Theory.IsEven y)
                    (Float.Theory.evenShift e (Succ q) ev)
                    (arithmetic: e * 4503599627370496 + Succ q = Succ (e * 4503599627370496 + q))))))

-- The same value as another fraction

theorem Float.Theory.cancelLe ∀ (a b c: Nat) (pos: 0 < c) (h: a * c ≤ b * c): a ≤ b := match k: Nat.leq a b with
  | True => arithmetic [k]
  | False => Void.impossible (arithmetic [h, Float.Theory.mulLtRight b a c (arithmetic [k]) pos])

theorem Float.Theory.cancelLess ∀ (a b c: Nat) (h: a * c < b * c): a < b := match k: Nat.leq b a with
  | True => Void.impossible (arithmetic [h, Nat.leMulRight b a c (arithmetic [k])])
  | False => arithmetic [k]

theorem Float.Theory.absDiffMulLe ∀ (a b c: Nat) (k: a ≤ b): Nat.absDiff a b * c = Nat.absDiff (a * c) (b * c) :=
  rewrite Nat.absDiffOfLe a b k, Nat.absDiffOfLe (a * c) (b * c) (Nat.leMulRight a b c k) then
    arithmetic [
      (Eq.trans
        (Eq.cong (x => x * c) (arithmetic [k]: b = a + (b - a)))
        (algebra: (a + (b - a)) * c = a * c + (b - a) * c): b * c = a * c + (b - a) * c)
    ]

theorem Float.Theory.absDiffMul ∀ (a b c: Nat): Nat.absDiff a b * c = Nat.absDiff (a * c) (b * c) :=
  match k: Nat.leq a b with
    | True => Float.Theory.absDiffMulLe a b c (arithmetic [k])
    | False =>
      rewrite Nat.absDiffComm a b, Nat.absDiffComm (a * c) (b * c) then Float.Theory.absDiffMulLe b a c (arithmetic [k])

theorem Float.Theory.scaleLe ∀ (x t1 d1 t2 d2: Nat) (p1: 0 < d1) (e: t1 * d2 = t2 * d1) (h: d1 * x ≤ t1): d2 * x ≤ t2 :=
  Float.Theory.cancelLe
    (d2 * x)
    t2
    d1
    p1
    (arithmetic [Nat.leMulRight (d1 * x) t1 d2 h, e, (algebra: d1 * x * d2 = d2 * x * d1)])

theorem Float.Theory.scaleLess ∀ (x t1 d1 t2 d2: Nat)
    (p2: 0 < d2)
    (e: t1 * d2 = t2 * d1)
    (h: t1 < d1 * x):
    t2 < d2 * x :=
  Float.Theory.cancelLess t2
    (d2 * x)
    d1
    (arithmetic [Float.Theory.mulLtRight t1 (d1 * x) d2 h p2, e, (algebra: d1 * x * d2 = d2 * x * d1)])

theorem Float.Theory.distScale ∀ (u t1 d1 t2 d2: Nat)
    (e: t1 * d2 = t2 * d1):
    Nat.absDiff (u * d1) t1 * d2 = Nat.absDiff (u * d2) t2 * d1 :=
  rewrite Float.Theory.absDiffMul (u * d1) t1 d2,
      Float.Theory.absDiffMul (u * d2) t2 d1,
      e,
      (algebra: u * d1 * d2 = u * d2 * d1) then
    byComputing

theorem Float.Theory.leAcross ∀ (a b c d k1 k2: Nat)
    (p1: 0 < k1)
    (ea: a * k2 = c * k1)
    (eb: b * k2 = d * k1)
    (h: a ≤ b):
    c ≤ d :=
  Float.Theory.cancelLe c d k1 p1 (arithmetic [ea, eb, Nat.leMulRight a b k2 h])

theorem Float.Theory.eqAcross ∀ (a b c d k1 k2: Nat)
    (p2: 0 < k2)
    (ea: a * k2 = c * k1)
    (eb: b * k2 = d * k1)
    (h: c = d):
    a = b :=
  arithmetic [
    Float.Theory.cancelLe a b k2 p2 (arithmetic [ea, eb, Eq.cong (x => x * k1) h]),
    Float.Theory.cancelLe b a k2 p2 (arithmetic [ea, eb, Eq.cong (x => x * k1) h])
  ]

--| Rounding `t1 / d1` is rounding any equal fraction.
theorem Float.Theory.roundsToScale ∀ (t1 d1 t2 d2 r: Nat)
    (p1: 0 < d1)
    (p2: 0 < d2)
    (e: t1 * d2 = t2 * d1)
    (h: Float.Theory.RoundsTo t1 d1 r):
    Float.Theory.RoundsTo t2 d2 r :=
  {
    bounded = h.bounded,
    overflow = er => Float.Theory.scaleLe Float.Theory.overflowUnits t1 d1 t2 d2 p1 e (h.overflow er),
    inRange = lr => Float.Theory.scaleLess Float.Theory.overflowUnits t1 d1 t2 d2 p2 e (h.inRange lr),
    nearest = m hm hr =>
      Float.Theory.leAcross
        (Nat.absDiff (Float.Theory.magUnits r * d1) t1)
        (Nat.absDiff (Float.Theory.magUnits m * d1) t1)
        (Nat.absDiff (Float.Theory.magUnits r * d2) t2)
        (Nat.absDiff (Float.Theory.magUnits m * d2) t2)
        d1
        d2
        p1
        (Float.Theory.distScale (Float.Theory.magUnits r) t1 d1 t2 d2 e)
        (Float.Theory.distScale (Float.Theory.magUnits m) t1 d1 t2 d2 e)
        (h.nearest m hm hr),
    tiesEven = m hm hr ne eq =>
      h.tiesEven m hm hr ne
        (Float.Theory.eqAcross
          (Nat.absDiff (Float.Theory.magUnits r * d1) t1)
          (Nat.absDiff (Float.Theory.magUnits m * d1) t1)
          (Nat.absDiff (Float.Theory.magUnits r * d2) t2)
          (Nat.absDiff (Float.Theory.magUnits m * d2) t2)
          d1
          d2
          p2
          (Float.Theory.distScale (Float.Theory.magUnits r) t1 d1 t2 d2 e)
          (Float.Theory.distScale (Float.Theory.magUnits m) t1 d1 t2 d2 e)
          eq)
  }

-- Scaling by 2^k

--| The numerator of 2^k as a fraction `upPow k / downPow k` of whole numbers.
def Float.Theory.upPow: (shift: Int) → Nat
  | OfNat k => Nat.pow 2 k
  | NegSucc k => 1

--| The denominator of 2^k as a fraction `upPow k / downPow k` of whole numbers.
def Float.Theory.downPow: (shift: Int) → Nat
  | OfNat k => 1
  | NegSucc k => Nat.pow 2 (Succ k)

theorem Float.Theory.scaleUpPow ∀ (n: Nat) (k: Int): Float.Model.scaleUp n k = n * Float.Theory.upPow k := match k with
  | OfNat k => Eq.cong (x => n * x) (Float.Theory.pow2Pow k)
  | NegSucc k => (Nat.mulOne n).flipped

theorem Float.Theory.scaleDownPow ∀ (d: Nat) (k: Int): Float.Model.scaleDown d k = d * Float.Theory.downPow k :=
  match k with
    | OfNat k => (Nat.mulOne d).flipped
    | NegSucc k => Eq.cong (x => d * x) (Float.Theory.pow2Pow (Succ k))

theorem Float.Theory.upPowPos ∀ (k: Int): 0 < Float.Theory.upPow k := match k with
  | OfNat k => Nat.powSuccPos 1 k
  | NegSucc k => byComputing

theorem Float.Theory.downPowPos ∀ (k: Int): 0 < Float.Theory.downPow k := match k with
  | OfNat k => byComputing
  | NegSucc k => Nat.powSuccPos 1 (Succ k)

--| One step up doubles the fraction.
theorem Float.Theory.powStep ∀ (m: Int):
    Float.Theory.upPow m * Float.Theory.downPow (Int.add m (OfNat 1)) * 2
      = Float.Theory.upPow (Int.add m (OfNat 1)) * Float.Theory.downPow m :=
  match m with
    | OfNat a => algebra
    | NegSucc Zero => byComputing
    | NegSucc (Succ b) => algebra

theorem Float.Theory.powChain ∀ (p q r s u v w: Nat)
    (ih: p * s * r = u * v)
    (step: u * q * 2 = w * s):
    s * (p * q * (r * 2)) = s * (w * v) :=
  Eq.trans
    (algebra: s * (p * q * (r * 2)) = p * s * r * (q * 2))
    (Eq.trans
      (Eq.cong (x => x * (q * 2)) ih)
      (Eq.trans
        (algebra: u * v * (q * 2) = v * (u * q * 2))
        (Eq.trans (Eq.cong (x => v * x) step) (algebra: v * (w * s) = s * (w * v)))))

--| `j` steps up multiply it by 2^j.
theorem Float.Theory.powShift ∀ (k: Int) (j: Nat):
    Float.Theory.upPow k * Float.Theory.downPow (Int.add k (OfNat j)) * Nat.pow 2 j
      = Float.Theory.upPow (Int.add k (OfNat j)) * Float.Theory.downPow k :=
  match j with
    | Zero => rewrite Int.addZero k then Nat.mulOne (Float.Theory.upPow k * Float.Theory.downPow k)
    | Succ j =>
      rewrite (algebra: Int.add k (OfNat (Succ j)) = Int.add (Int.add k (OfNat j)) (OfNat 1)) then
        Nat.mulCancelLeft
          (Float.Theory.downPow (Int.add k (OfNat j)))
          (Float.Theory.downPowPos (Int.add k (OfNat j)))
          (Float.Theory.upPow k * Float.Theory.downPow (Int.add (Int.add k (OfNat j)) (OfNat 1)) * (Nat.pow 2 j * 2))
          (Float.Theory.upPow (Int.add (Int.add k (OfNat j)) (OfNat 1)) * Float.Theory.downPow k)
          (Float.Theory.powChain
            (Float.Theory.upPow k)
            (Float.Theory.downPow (Int.add (Int.add k (OfNat j)) (OfNat 1)))
            (Nat.pow 2 j)
            (Float.Theory.downPow (Int.add k (OfNat j)))
            (Float.Theory.upPow (Int.add k (OfNat j)))
            (Float.Theory.downPow k)
            (Float.Theory.upPow (Int.add (Int.add k (OfNat j)) (OfNat 1)))
            (Float.Theory.powShift k j)
            (Float.Theory.powStep (Int.add k (OfNat j))))

theorem Float.Theory.quotLess ∀ (q b t k: Nat) (low: q * b ≤ t) (h: t < b * k): q < k :=
  Float.Theory.cancelLess q k b (arithmetic [low, h, (algebra: b * k = k * b)])

theorem Float.Theory.quotAtLeast ∀ (q b t k: Nat) (high: t < Succ q * b) (h: b * k ≤ t): k ≤ q :=
  match c: Nat.leq k q with
    | True => arithmetic [c]
    | False =>
      Void.impossible (arithmetic [high, h, Nat.leMulRight (Succ q) k b (arithmetic [c]), (algebra: b * k = k * b)])
--| `roundMagnitude`'s last step, at exponent `e` and shift `sh`.
def Float.Theory.roundAt (n den e: Nat) (sh: Int): Nat :=
  let top: Nat := Float.Model.scaleUp n sh
  let bottom: Nat := Float.Model.scaleDown den sh
  let q: Nat := Nat.divFuel top top bottom
  Float.Model.roundCore False e q (Float.Model.locate (top - q * bottom) bottom)

-- Choosing the exponent

--| Cross-multiplied steps between fractions `nk / dk` at neighbouring
--| scales.
theorem Float.Theory.halveLow ∀ (nc dc nh dh: Nat)
    (pos: 0 < dc)
    (rel: nh * dc * 2 = nc * dh)
    (h: dc * 9007199254740992 ≤ nc):
    dh * 4503599627370496 ≤ nh :=
  Float.Theory.cancelLe
    (dh * 4503599627370496)
    nh
    (dc * 2)
    (arithmetic [pos])
    (arithmetic [
      (algebra: dh * 4503599627370496 * (dc * 2) = dc * 9007199254740992 * dh),
      Nat.leMulRight (dc * 9007199254740992) nc dh h,
      (Eq.trans (algebra: nh * (dc * 2) = nh * dc * 2) rel: nh * (dc * 2) = nc * dh)
    ])

theorem Float.Theory.halveHigh ∀ (nc dc nh dh: Nat)
    (pos: 0 < dh)
    (rel: nh * dc * 2 = nc * dh)
    (h: nc < dc * 18014398509481984):
    nh < dh * 9007199254740992 :=
  Float.Theory.cancelLess nh
    (dh * 9007199254740992)
    (dc * 2)
    (arithmetic [
      (algebra: dh * 9007199254740992 * (dc * 2) = dc * 18014398509481984 * dh),
      Float.Theory.mulLtRight nc (dc * 18014398509481984) dh h pos,
      (Eq.trans (algebra: nh * (dc * 2) = nh * dc * 2) rel: nh * (dc * 2) = nc * dh)
    ])

theorem Float.Theory.lowerHigh ∀ (na da nb db p: Nat)
    (pp: 0 < p)
    (pos: 0 < da)
    (rel: na * db * p = nb * da)
    (h: nb < db * 9007199254740992):
    na < da * 9007199254740992 :=
  Float.Theory.cancelLess na
    (da * 9007199254740992)
    db
    (arithmetic [
      Nat.leMulPos (na * db) p pp,
      rel,
      Float.Theory.mulLtRight nb (db * 9007199254740992) da h pos,
      (algebra: db * 9007199254740992 * da = da * 9007199254740992 * db)
    ])

--| At `c = bitLength den + 53 - bitLength n`, `n / den × 2^c` is between
--| 2^52 and 2^54.
theorem Float.Theory.firstLow ∀ (n den u v a dd: Nat)
    (pa: 0 < a)
    (pv: 0 < v)
    (rel: u * a = dd * 9007199254740992 * v)
    (ba: a ≤ n + n)
    (bd: den < dd):
    den * v * 4503599627370496 < n * u :=
  Float.Theory.cancelLess
    (den * v * 4503599627370496)
    (n * u)
    a
    (arithmetic [
      Float.Theory.mulLtRight
        (den * a)
        (dd * (n + n))
        (v * 4503599627370496)
        (arithmetic [Float.Theory.mulLtRight den dd a bd pa, Float.Theory.mulLeLeft a (n + n) dd ba])
        (arithmetic [pv]),
      (algebra: den * v * 4503599627370496 * a = den * a * (v * 4503599627370496)),
      (algebra: dd * (n + n) * (v * 4503599627370496) = n * (dd * 9007199254740992 * v)),
      (Eq.trans (algebra: n * u * a = n * (u * a)) (Eq.cong (x => n * x) rel): n * u * a
        = n * (dd * 9007199254740992 * v))
    ])

theorem Float.Theory.firstHigh ∀ (n den u v a dd: Nat)
    (pa: 0 < a)
    (pv: 0 < v)
    (pdd: 0 < dd)
    (rel: u * a = dd * 9007199254740992 * v)
    (bn: n < a)
    (bD: dd ≤ den + den):
    n * u < den * v * 18014398509481984 :=
  Float.Theory.cancelLess
    (n * u)
    (den * v * 18014398509481984)
    a
    (arithmetic [
      Float.Theory.mulLtRight
        (n * dd)
        (a * (den + den))
        (v * 9007199254740992)
        (arithmetic [
          Float.Theory.mulLtRight n a dd bn pdd,
          Float.Theory.mulLeLeft dd (den + den) a bD,
          (algebra: n * dd = n * dd),
          (algebra: a * dd = n * 0 + a * dd)
        ])
        (arithmetic [pv]),
      (algebra: den * v * 18014398509481984 * a = a * (den + den) * (v * 9007199254740992)),
      (algebra: n * dd * (v * 9007199254740992) = n * (dd * 9007199254740992 * v)),
      (Eq.trans (algebra: n * u * a = n * (u * a)) (Eq.cong (x => n * x) rel): n * u * a
        = n * (dd * 9007199254740992 * v))
    ])

theorem Float.Theory.subNatNatCancel ∀ (x a: Nat): Int.subNatNat (x + a) a = OfNat x :=
  rewrite (arithmetic: a - (x + a) = 0) then rewrite (arithmetic: x + a - a = x) then byComputing

--| `2^E × top / bottom` at `shift + E = s` is `n / den × 2^s`.
theorem Float.Theory.shiftCross ∀ (n den u v us vs x: Nat)
    (rel: u * vs * x = us * v):
    x * (n * u) * (den * vs) = n * us * (den * v) :=
  Eq.trans
    (algebra: x * (n * u) * (den * vs) = n * den * (u * vs * x))
    (Eq.trans (Eq.cong (y => n * den * y) rel) (algebra: n * den * (us * v) = n * us * (den * v)))

theorem Float.Theory.finishAt ∀ (n den: Nat) (s sh: Int) (e: Nat)
    (pn: 0 < n)
    (pd: 0 < den)
    (hs: Int.add sh (OfNat e) = s)
    (qhi: n * Float.Theory.upPow sh < den * Float.Theory.downPow sh * 9007199254740992)
    (lead: (e = 0) ∨ (den * Float.Theory.downPow sh * 4503599627370496 ≤ n * Float.Theory.upPow sh)):
    Float.Theory.RoundsTo (Float.Model.scaleUp n s) (Float.Model.scaleDown den s) (Float.Theory.roundAt n den e sh) :=
  let top: Nat := Float.Model.scaleUp n sh
  let bottom: Nat := Float.Model.scaleDown den sh
  let q: Nat := Nat.divFuel top top bottom
  let te: top = n * Float.Theory.upPow sh := Float.Theory.scaleUpPow n sh
  let be: bottom = den * Float.Theory.downPow sh := Float.Theory.scaleDownPow den sh
  let pb: 0 < bottom :=
    rewrite be then arithmetic [Nat.leMulPos den (Float.Theory.downPow sh) (Float.Theory.downPowPos sh), pd]
  let low: q * bottom ≤ top := Nat.divFuelLe top top bottom
  let high: top < Succ q * bottom := Nat.divFuelBound top top bottom (Nat.nonzeroOfPos bottom pb) (Nat.leRefl top)
  let rel: Float.Theory.upPow sh * Float.Theory.downPow s * Nat.pow 2 e
    = Float.Theory.upPow s * Float.Theory.downPow sh :=
    J
      (y w =>
        Float.Theory.upPow sh * Float.Theory.downPow y * Nat.pow 2 e = Float.Theory.upPow y * Float.Theory.downPow sh)
      (Float.Theory.powShift sh e)
      hs
  Float.Theory.roundsToScale
    (Nat.pow 2 e * top)
    bottom
    (Float.Model.scaleUp n s)
    (Float.Model.scaleDown den s)
    (Float.Model.roundCore False e q (Float.Model.locate (top - q * bottom) bottom))
    pb
    (rewrite Float.Theory.scaleDownPow den s then
      arithmetic [Nat.leMulPos den (Float.Theory.downPow s) (Float.Theory.downPowPos s), pd])
    (rewrite te, be, Float.Theory.scaleUpPow n s, Float.Theory.scaleDownPow den s then
      Float.Theory.shiftCross n den
        (Float.Theory.upPow sh)
        (Float.Theory.downPow sh)
        (Float.Theory.upPow s)
        (Float.Theory.downPow s)
        (Nat.pow 2 e)
        rel)
    (Float.Theory.roundCoreAt e top bottom q
      (top - q * bottom)
      pb
      (arithmetic [low])
      (arithmetic [low, high])
      (Float.Theory.quotLess q bottom top 9007199254740992 low (arithmetic [te, be, qhi]))
      (match lead with
        | Inl z => Inl z
        | Inr l => Inr (Float.Theory.quotAtLeast q bottom top 4503599627370496 high (arithmetic [l, te, be]))))

theorem Float.Theory.crossTwo ∀ (n den u v us vs x: Nat)
    (rel: u * vs * x = us * v):
    n * u * (den * vs) * x = n * us * (den * v) :=
  Eq.trans (algebra: n * u * (den * vs) * x = x * (n * u) * (den * vs)) (Float.Theory.shiftCross n den u v us vs x rel)

--| The exponent and shift for a scale `c'` at which `n / den` has 53 bits.
theorem Float.Theory.afterExponent ∀ (n den: Nat) (s c: Int)
    (pn: 0 < n)
    (pd: 0 < den)
    (lo: den * Float.Theory.downPow c * 4503599627370496 ≤ n * Float.Theory.upPow c)
    (hi: n * Float.Theory.upPow c < den * Float.Theory.downPow c * 9007199254740992):
    Float.Theory.RoundsTo
      (Float.Model.scaleUp n s)
      (Float.Model.scaleDown den s)
      (Float.Theory.roundAt n den (Int.toNat (Int.sub s c)) (Int.sub s (OfNat (Int.toNat (Int.sub s c))))) :=
  match hv: Int.sub s c with
    | OfNat e =>
      let shEq: Int.sub s (OfNat e) = c := algebra [hv]
      Float.Theory.finishAt n den s
        (Int.sub s (OfNat e))
        e
        pn
        pd
        (algebra: Int.add (Int.sub s (OfNat e)) (OfNat e) = s)
        (J (y w => n * Float.Theory.upPow y < den * Float.Theory.downPow y * 9007199254740992) hi shEq.flipped)
        (Inr (J (y w => den * Float.Theory.downPow y * 4503599627370496 ≤ n * Float.Theory.upPow y) lo shEq.flipped))
    | NegSucc j =>
      let cEq: Int.add (Int.sub s (OfNat 0)) (OfNat (Succ j)) = c := algebra [hv]
      let rel: Float.Theory.upPow (Int.sub s (OfNat 0)) * Float.Theory.downPow c * Nat.pow 2 (Succ j)
        = Float.Theory.upPow c * Float.Theory.downPow (Int.sub s (OfNat 0)) :=
        J
          (y w =>
            Float.Theory.upPow (Int.sub s (OfNat 0)) * Float.Theory.downPow y * Nat.pow 2 (Succ j)
              = Float.Theory.upPow y * Float.Theory.downPow (Int.sub s (OfNat 0)))
          (Float.Theory.powShift (Int.sub s (OfNat 0)) (Succ j))
          cEq
      Float.Theory.finishAt n den s
        (Int.sub s (OfNat 0))
        0
        pn
        pd
        (algebra: Int.add (Int.sub s (OfNat 0)) (OfNat 0) = s)
        (Float.Theory.lowerHigh
          (n * Float.Theory.upPow (Int.sub s (OfNat 0)))
          (den * Float.Theory.downPow (Int.sub s (OfNat 0)))
          (n * Float.Theory.upPow c)
          (den * Float.Theory.downPow c)
          (Nat.pow 2 (Succ j))
          (Nat.powSuccPos 1 (Succ j))
          (arithmetic [
            Nat.leMulPos den
              (Float.Theory.downPow (Int.sub s (OfNat 0)))
              (Float.Theory.downPowPos (Int.sub s (OfNat 0))),
            pd
          ])
          (Float.Theory.crossTwo n den
            (Float.Theory.upPow (Int.sub s (OfNat 0)))
            (Float.Theory.downPow (Int.sub s (OfNat 0)))
            (Float.Theory.upPow c)
            (Float.Theory.downPow c)
            (Nat.pow 2 (Succ j))
            rel)
          hi)
        (Inl byComputing)

--| `roundMagnitude` rounds `n / den × 2^s` units, for positive `n` and
--| `den`.
theorem Float.Theory.roundMagnitudeSpec ∀ (n den: Nat) (s: Int)
    (pn: 0 < n)
    (pd: 0 < den):
    Float.Theory.RoundsTo
      (Float.Model.scaleUp n s)
      (Float.Model.scaleDown den s)
      (Float.Model.roundMagnitude False n den s) :=
  let a: Nat := Float.Model.bitLength n
  let d: Nat := Float.Model.bitLength den
  let c: Int := Int.subNatNat (d + 53) a
  let bn: Float.Theory.IsBitLength n a := Float.Theory.bitLengthSpec n pn
  let bd: Float.Theory.IsBitLength den d := Float.Theory.bitLengthSpec den pd
  let cEq: Int.add c (OfNat a) = OfNat (d + 53) :=
    Eq.trans (Int.subNatNatAddOfNat a (d + 53) a) (Float.Theory.subNatNatCancel (d + 53) a)
  let shifted: Float.Theory.upPow c * 1 * Nat.pow 2 a = Nat.pow 2 (d + 53) * Float.Theory.downPow c :=
    J
      (y w =>
        Float.Theory.upPow c * Float.Theory.downPow y * Nat.pow 2 a = Float.Theory.upPow y * Float.Theory.downPow c)
      (Float.Theory.powShift c a)
      cEq
  let relc: Float.Theory.upPow c * Nat.pow 2 a = Nat.pow 2 d * 9007199254740992 * Float.Theory.downPow c :=
    Eq.trans
      (algebra: Float.Theory.upPow c * Nat.pow 2 a = Float.Theory.upPow c * 1 * Nat.pow 2 a)
      (Eq.trans shifted
        (Eq.trans
          (Eq.cong (x => x * Float.Theory.downPow c) (Nat.powAdd 2 d 53))
          (algebra: Nat.pow 2 d * Nat.pow 2 53 * Float.Theory.downPow c
            = Nat.pow 2 d * 9007199254740992 * Float.Theory.downPow c)))
  let lowc: den * Float.Theory.downPow c * 4503599627370496 < n * Float.Theory.upPow c :=
    Float.Theory.firstLow n den
      (Float.Theory.upPow c)
      (Float.Theory.downPow c)
      (Nat.pow 2 a)
      (Nat.pow 2 d)
      (Nat.powSuccPos 1 a)
      (Float.Theory.downPowPos c)
      relc
      bn.right
      bd.left
  let highc: n * Float.Theory.upPow c < den * Float.Theory.downPow c * 18014398509481984 :=
    Float.Theory.firstHigh n den
      (Float.Theory.upPow c)
      (Float.Theory.downPow c)
      (Nat.pow 2 a)
      (Nat.pow 2 d)
      (Nat.powSuccPos 1 a)
      (Float.Theory.downPowPos c)
      (Nat.powSuccPos 1 d)
      relc
      bn.left
      bd.right
  let wideEq: Float.Model.scaleDown den c * Float.Model.pow2 53 = den * Float.Theory.downPow c * 9007199254740992 :=
    Eq.trans
      (Eq.cong (x => x * Float.Model.pow2 53) (Float.Theory.scaleDownPow den c))
      (Eq.cong
        (x => den * Float.Theory.downPow c * x)
        (Float.Theory.pow2Pow 53: Float.Model.pow2 53 = 9007199254740992))
  let nEq: Float.Model.scaleUp n c = n * Float.Theory.upPow c := Float.Theory.scaleUpPow n c
  match w: Nat.leq (Float.Model.scaleDown den c * Float.Model.pow2 53) (Float.Model.scaleUp n c) with
    | True =>
      let c1: Int := Int.sub c (OfNat 1)
      let step: Float.Theory.upPow c1 * Float.Theory.downPow c * 2 = Float.Theory.upPow c * Float.Theory.downPow c1 :=
        J
          (y v => Float.Theory.upPow c1 * Float.Theory.downPow y * 2 = Float.Theory.upPow y * Float.Theory.downPow c1)
          (Float.Theory.powShift c1 1)
          (algebra: Int.add (Int.sub c (OfNat 1)) (OfNat 1) = c)
      let rel: n * Float.Theory.upPow c1 * (den * Float.Theory.downPow c) * 2
        = n * Float.Theory.upPow c * (den * Float.Theory.downPow c1) :=
        Float.Theory.crossTwo n den
          (Float.Theory.upPow c1)
          (Float.Theory.downPow c1)
          (Float.Theory.upPow c)
          (Float.Theory.downPow c)
          2
          step
      Float.Theory.afterExponent n den s c1 pn pd
        (Float.Theory.halveLow
          (n * Float.Theory.upPow c)
          (den * Float.Theory.downPow c)
          (n * Float.Theory.upPow c1)
          (den * Float.Theory.downPow c1)
          (arithmetic [Nat.leMulPos den (Float.Theory.downPow c) (Float.Theory.downPowPos c), pd])
          rel
          (arithmetic [w, wideEq, nEq]))
        (Float.Theory.halveHigh
          (n * Float.Theory.upPow c)
          (den * Float.Theory.downPow c)
          (n * Float.Theory.upPow c1)
          (den * Float.Theory.downPow c1)
          (arithmetic [Nat.leMulPos den (Float.Theory.downPow c1) (Float.Theory.downPowPos c1), pd])
          rel
          highc)
    | False => Float.Theory.afterExponent n den s c pn pd (arithmetic [lowc]) (arithmetic [w, wideEq, nEq])

-- Rounding is monotone

theorem Float.Theory.notEvenBoth ∀ (n: Nat) (a: Float.Theory.IsEven n) (b: Float.Theory.IsEven (Succ n)): Void :=
  arithmetic [a, Nat.divFuelLe n n 2, b, Nat.divFuelLe (Succ n) (Succ n) 2]

theorem Float.Theory.orderAbsurd ∀ (x t1 t2: Nat) (a: x ≤ t1) (b: t2 < x) (le: t1 ≤ t2): Void := arithmetic

--| Two roundings with the same denominator keep the order of the values.
theorem Float.Theory.roundsToMono ∀ (t1 t2 d r1 r2: Nat)
    (pd: 0 < d)
    (h1: Float.Theory.RoundsTo t1 d r1)
    (h2: Float.Theory.RoundsTo t2 d r2)
    (le: t1 ≤ t2):
    r1 ≤ r2 :=
  match c: Nat.leq r1 r2 with
    | True => arithmetic [c]
    | False =>
      Void.impossible
        (match f: Nat.leq 9218868437227405312 r1 with
          | True =>
            Float.Theory.orderAbsurd
              (d * Float.Theory.overflowUnits)
              t1
              t2
              (h1.overflow (arithmetic [f, h1.bounded]))
              (h2.inRange (arithmetic [c, h1.bounded]))
              le
          | False =>
            let lt1: r1 < 9218868437227405312 := arithmetic [f]
            let lt2: r2 < 9218868437227405312 := arithmetic [f, c]
            let ab: Float.Theory.magUnits r2 * d < Float.Theory.magUnits r1 * d :=
              Float.Theory.scaledLess r2 r1 d (arithmetic [c]) pd
            let n1 := h1.nearest r2 lt2 lt1
            let n2 := h2.nearest r1 lt1 lt2
            let da := Float.Theory.absDiffDef (Float.Theory.magUnits r2 * d) t1
            let db := Float.Theory.absDiffDef (Float.Theory.magUnits r1 * d) t1
            let da2 := Float.Theory.absDiffDef (Float.Theory.magUnits r2 * d) t2
            let db2 := Float.Theory.absDiffDef (Float.Theory.magUnits r1 * d) t2
            match g: Nat.equal (Succ r2) r1 with
              | True =>
                let e1: Succ r2 = r1 := g.read
                Float.Theory.notEvenBoth r2
                  (h2.tiesEven r1 lt1 lt2 (ne => arithmetic [ne, e1]) (arithmetic [n1, n2, da, db, da2, db2, ab, le]))
                  (J
                    (y w => Float.Theory.IsEven y)
                    (h1.tiesEven r2 lt2 lt1 (ne => arithmetic [ne, e1]) (arithmetic [n1, n2, da, db, da2, db2, ab, le]))
                    e1.flipped)
              | False =>
                let m: Nat := Succ r2
                let am: Float.Theory.magUnits r2 * d < Float.Theory.magUnits m * d :=
                  Float.Theory.scaledLess r2 m d (arithmetic) pd
                let mb: Float.Theory.magUnits m * d < Float.Theory.magUnits r1 * d :=
                  Float.Theory.scaledLess m r1 d (arithmetic [c, Nat.equalFalse (Succ r2) r1 g]) pd
                arithmetic [
                  n1,
                  n2,
                  da,
                  db,
                  da2,
                  db2,
                  ab,
                  le,
                  am,
                  mb,
                  h1.nearest m (arithmetic [c, Nat.equalFalse (Succ r2) r1 g, lt1]) lt1,
                  Float.Theory.absDiffDef (Float.Theory.magUnits m * d) t1
                ])

-- `roundRatio`

-- Its three cases: a zero numerator gives the zero with sign `z`, a
-- positive one the rounded magnitude, a negative one that with the sign
-- bit.

--| `roundRatio` of a zero numerator is the zero with sign `z`.
theorem Float.Theory.roundRatioZeroNum ∀ (den: Nat) (scale: Int) (z: Bool):
    Float.Model.roundRatio (OfNat 0) den scale z = Float.Model.zeroBits z :=
  byComputing

--| `roundRatio` of a positive numerator is the rounded magnitude.
theorem Float.Theory.roundRatioPos ∀ (k den: Nat) (scale: Int) (z: Bool):
    Float.Model.roundRatio (OfNat (Succ k)) den scale z
      = Float.Model.roundMagnitude False (Succ k) den (Int.add scale (OfNat 1074)) :=
  byComputing

--| `roundRatio` of a negative numerator is the rounded magnitude with the sign bit.
theorem Float.Theory.roundRatioNeg ∀ (k den: Nat) (scale: Int) (z: Bool):
    Float.Model.roundRatio (NegSucc k) den scale z
      = Float.Model.roundMagnitude False (Succ k) den (Int.add scale (OfNat 1074)) + 9223372036854775808 :=
  byComputing

theorem Float.Theory.scaleDownPos ∀ (den: Nat) (s: Int) (pd: 0 < den): 0 < Float.Model.scaleDown den s :=
  rewrite Float.Theory.scaleDownPow den s then
    arithmetic [Nat.leMulPos den (Float.Theory.downPow s) (Float.Theory.downPowPos s), pd]

theorem Float.Theory.magnitudeBound ∀ (n den: Nat) (s: Int)
    (pn: 0 < n)
    (pd: 0 < den):
    Float.Model.roundMagnitude False n den s ≤ 9218868437227405312 :=
  (Float.Theory.roundMagnitudeSpec n den s pn pd).bounded

--| A larger numerator rounds to a pattern at least as large.
theorem Float.Theory.magnitudeMono ∀ (n1 n2 den: Nat) (s: Int)
    (pn: 0 < n1)
    (pd: 0 < den)
    (h: n1 ≤ n2):
    Float.Model.roundMagnitude False n1 den s ≤ Float.Model.roundMagnitude False n2 den s :=
  Float.Theory.roundsToMono
    (Float.Model.scaleUp n1 s)
    (Float.Model.scaleUp n2 s)
    (Float.Model.scaleDown den s)
    (Float.Model.roundMagnitude False n1 den s)
    (Float.Model.roundMagnitude False n2 den s)
    (Float.Theory.scaleDownPos den s pd)
    (Float.Theory.roundMagnitudeSpec n1 den s pn pd)
    (Float.Theory.roundMagnitudeSpec n2 den s (arithmetic [pn, h]) pd)
    (rewrite Float.Theory.scaleUpPow n1 s, Float.Theory.scaleUpPow n2 s then
      Nat.leMulRight n1 n2 (Float.Theory.upPow s) h)

theorem Float.Theory.roundRatioValid ∀ (den: Nat) (scale: Int) (z: Bool)
    (pd: 0 < den) (num: Int):
    Float.isValid (Float.Model.roundRatio num den scale z) = True :=
  match num with
    | OfNat Zero =>
      match z with
        | True => Float.validHigh 9223372036854775808 byComputing byComputing
        | False => Float.validLow 0 byComputing
    | OfNat (Succ k) =>
      Float.validLow
        (Float.Model.roundMagnitude False (Succ k) den (Int.add scale (OfNat 1074)))
        (Float.Theory.magnitudeBound (Succ k) den (Int.add scale (OfNat 1074)) byComputing pd)
    | NegSucc k =>
      Float.validHigh
        (Float.Model.roundMagnitude False (Succ k) den (Int.add scale (OfNat 1074)) + 9223372036854775808)
        (arithmetic)
        (arithmetic [Float.Theory.magnitudeBound (Succ k) den (Int.add scale (OfNat 1074)) byComputing pd])

--| Keys in the total order.
theorem Float.Theory.keyLow ∀ (m: Nat)
    (h: m ≤ 9218868437227405312):
    Float.keyOf m (Nat.leq 9223372036854775808 m) = OfNat m :=
  rewrite (arithmetic [h]: Nat.leq 9223372036854775808 m = False) then byComputing

theorem Float.Theory.keyHigh ∀ (m: Nat):
    Float.keyOf (m + 9223372036854775808) (Nat.leq 9223372036854775808 (m + 9223372036854775808)) = NegSucc m :=
  byComputing

theorem Float.Theory.leqVia ∀ (a b c d: Int) (ea: a = c) (eb: b = d) (h: Int.leq c d = True): Int.leq a b = True :=
  rewrite ea, eb then h

--| The key of a rounding.
def Float.Theory.roundKey (num: Int) (den: Nat) (scale: Int) (z: Bool): Int :=
  Float.keyOf
    (Float.Model.roundRatio num den scale z)
    (Nat.leq 9223372036854775808 (Float.Model.roundRatio num den scale z))

theorem Float.Theory.roundKeyPos ∀ (k den: Nat) (scale: Int) (z: Bool)
    (pd: 0 < den):
    Float.Theory.roundKey (OfNat (Succ k)) den scale z
      = OfNat (Float.Model.roundMagnitude False (Succ k) den (Int.add scale (OfNat 1074))) :=
  Float.Theory.keyLow
    (Float.Model.roundMagnitude False (Succ k) den (Int.add scale (OfNat 1074)))
    (Float.Theory.magnitudeBound (Succ k) den (Int.add scale (OfNat 1074)) byComputing pd)

theorem Float.Theory.roundKeyNeg ∀ (k den: Nat) (scale: Int) (z: Bool):
    Float.Theory.roundKey (NegSucc k) den scale z
      = NegSucc (Float.Model.roundMagnitude False (Succ k) den (Int.add scale (OfNat 1074))) :=
  Float.Theory.keyHigh (Float.Model.roundMagnitude False (Succ k) den (Int.add scale (OfNat 1074)))

--| A zero numerator's key is -1 or 0, below every positive one's and above
--| every negative one's.
theorem Float.Theory.roundKeyZeroLe ∀ (den: Nat) (scale: Int) (z: Bool) (m: Nat):
    Int.leq (Float.Theory.roundKey (OfNat 0) den scale z) (OfNat m) = True :=
  match z with
    | True => byComputing
    | False => byComputing

theorem Float.Theory.roundKeyZeroGe ∀ (den: Nat) (scale: Int) (z: Bool) (m: Nat):
    Int.leq (NegSucc m) (Float.Theory.roundKey (OfNat 0) den scale z) = True :=
  match z with
    | True => byComputing
    | False => byComputing

--| A smaller numerator rounds to a double no greater, whatever the zero signs.
theorem Float.Theory.roundKeyMono ∀ (den: Nat) (scale: Int) (z1 z2: Bool)
    (pd: 0 < den) (num1 num2: Int)
    (lt: Int.less num1 num2 = True):
    Int.leq (Float.Theory.roundKey num1 den scale z1) (Float.Theory.roundKey num2 den scale z2) = True :=
  match num1, num2 with
    | OfNat Zero, OfNat (Succ k2) =>
      Float.Theory.leqVia
        (Float.Theory.roundKey (OfNat 0) den scale z1)
        (Float.Theory.roundKey (OfNat (Succ k2)) den scale z2)
        (Float.Theory.roundKey (OfNat 0) den scale z1)
        (OfNat (Float.Model.roundMagnitude False (Succ k2) den (Int.add scale (OfNat 1074))))
        byComputing
        (Float.Theory.roundKeyPos k2 den scale z2 pd)
        (Float.Theory.roundKeyZeroLe den scale z1
          (Float.Model.roundMagnitude False (Succ k2) den (Int.add scale (OfNat 1074))))
    | OfNat (Succ k1), OfNat (Succ k2) =>
      Float.Theory.leqVia
        (Float.Theory.roundKey (OfNat (Succ k1)) den scale z1)
        (Float.Theory.roundKey (OfNat (Succ k2)) den scale z2)
        (OfNat (Float.Model.roundMagnitude False (Succ k1) den (Int.add scale (OfNat 1074))))
        (OfNat (Float.Model.roundMagnitude False (Succ k2) den (Int.add scale (OfNat 1074))))
        (Float.Theory.roundKeyPos k1 den scale z1 pd)
        (Float.Theory.roundKeyPos k2 den scale z2 pd)
        (Float.Theory.magnitudeMono
          (Succ k1)
          (Succ k2)
          den
          (Int.add scale (OfNat 1074))
          byComputing
          pd
          (arithmetic [lt]))
    | NegSucc k1, OfNat Zero =>
      Float.Theory.leqVia
        (Float.Theory.roundKey (NegSucc k1) den scale z1)
        (Float.Theory.roundKey (OfNat 0) den scale z2)
        (NegSucc (Float.Model.roundMagnitude False (Succ k1) den (Int.add scale (OfNat 1074))))
        (Float.Theory.roundKey (OfNat 0) den scale z2)
        (Float.Theory.roundKeyNeg k1 den scale z1)
        byComputing
        (Float.Theory.roundKeyZeroGe den scale z2
          (Float.Model.roundMagnitude False (Succ k1) den (Int.add scale (OfNat 1074))))
    | NegSucc k1, OfNat (Succ k2) =>
      Float.Theory.leqVia
        (Float.Theory.roundKey (NegSucc k1) den scale z1)
        (Float.Theory.roundKey (OfNat (Succ k2)) den scale z2)
        (NegSucc (Float.Model.roundMagnitude False (Succ k1) den (Int.add scale (OfNat 1074))))
        (OfNat (Float.Model.roundMagnitude False (Succ k2) den (Int.add scale (OfNat 1074))))
        (Float.Theory.roundKeyNeg k1 den scale z1)
        (Float.Theory.roundKeyPos k2 den scale z2 pd)
        byComputing
    | NegSucc k1, NegSucc k2 =>
      Float.Theory.leqVia
        (Float.Theory.roundKey (NegSucc k1) den scale z1)
        (Float.Theory.roundKey (NegSucc k2) den scale z2)
        (NegSucc (Float.Model.roundMagnitude False (Succ k1) den (Int.add scale (OfNat 1074))))
        (NegSucc (Float.Model.roundMagnitude False (Succ k2) den (Int.add scale (OfNat 1074))))
        (Float.Theory.roundKeyNeg k1 den scale z1)
        (Float.Theory.roundKeyNeg k2 den scale z2)
        (Float.Theory.magnitudeMono
          (Succ k2)
          (Succ k1)
          den
          (Int.add scale (OfNat 1074))
          byComputing
          pd
          (arithmetic [lt]))

-- Rounding a double's own value gives the double

theorem Float.Theory.largestUnder: Float.Theory.magUnits 9218868437227405311 < Float.Theory.overflowUnits := byComputing

theorem Float.Theory.capAbsurd ∀ (o u um: Nat) (a: 1 * o ≤ u * 1) (hu: u ≤ um) (hm: um < o): Void := arithmetic

theorem Float.Theory.roundRatioOfPos ∀ (den: Nat) (scale: Int) (z: Bool) (x: Nat)
    (p: 0 < x):
    Float.Model.roundRatio (OfNat x) den scale z
      = Float.Model.roundMagnitude False x den (Int.add scale (OfNat 1074)) :=
  match x with | Succ k => byComputing

theorem Float.Theory.roundRatioOfNeg ∀ (den: Nat) (scale: Int) (z: Bool) (x: Nat)
    (p: 0 < x):
    Float.Model.roundRatio (Int.neg (OfNat x)) den scale z
      = Float.Model.roundMagnitude False x den (Int.add scale (OfNat 1074)) + 9223372036854775808 :=
  match x with | Succ k => byComputing

theorem Float.Theory.zeroOrPos ∀ (m: Nat): (m = 0) ∨ (0 < m) := match m with
  | Zero => Inl byComputing
  | Succ k => Inr byComputing

--| Rounding a finite pattern's own units gives that pattern.
theorem Float.Theory.roundsToExact ∀ (m r: Nat)
    (hm: m < 9218868437227405312)
    (spec: Float.Theory.RoundsTo (Float.Theory.magUnits m * 1) 1 r):
    r = m :=
  match c: Nat.leq 9218868437227405312 r with
    | True =>
      Void.impossible
        (Float.Theory.capAbsurd Float.Theory.overflowUnits
          (Float.Theory.magUnits m)
          (Float.Theory.magUnits 9218868437227405311)
          (spec.overflow (arithmetic [c, spec.bounded]))
          (Float.Theory.magUnitsLe m 9218868437227405311 (arithmetic [hm]))
          Float.Theory.largestUnder)
    | False =>
      Float.Theory.magUnitsInjective r m
        (arithmetic [
          spec.nearest m hm (arithmetic [c]),
          Float.Theory.absDiffDef (Float.Theory.magUnits r * 1) (Float.Theory.magUnits m * 1),
          Float.Theory.absDiffDef (Float.Theory.magUnits m * 1) (Float.Theory.magUnits m * 1)
        ])

theorem Float.Theory.magnitudeExact ∀ (m: Nat)
    (pm: 0 < m)
    (hm: m < 9218868437227405312):
    Float.Model.roundMagnitude False (Float.Theory.magUnits m) 1 (OfNat 0) = m :=
  Float.Theory.roundsToExact m
    (Float.Model.roundMagnitude False (Float.Theory.magUnits m) 1 (OfNat 0))
    hm
    (Float.Theory.roundMagnitudeSpec
      (Float.Theory.magUnits m)
      1
      (OfNat 0)
      (Float.Theory.magUnitsLess 0 m pm)
      byComputing)

theorem Float.Theory.unitsRoundPos ∀ (x: Nat)
    (p: 0 < x):
    Float.Model.roundRatio (Int.signed False x) 1 (-1074) False = Float.Model.roundMagnitude False x 1 (OfNat 0) :=
  match x with | Succ k => byComputing

theorem Float.Theory.unitsRoundNeg ∀ (x: Nat)
    (p: 0 < x):
    Float.Model.roundRatio (Int.signed True x) 1 (-1074) True
      = Float.Model.roundMagnitude False x 1 (OfNat 0) + 9223372036854775808 :=
  match x with | Succ k => byComputing

theorem Float.Theory.unitsRoundNonneg ∀ (m: Nat)
    (hm: m < 9218868437227405312):
    Float.Model.roundRatio (Int.signed False (Float.Theory.magUnits m)) 1 (-1074) False = m :=
  match m with
    | Zero => byComputing
    | Succ k =>
      Eq.trans
        (Float.Theory.unitsRoundPos (Float.Theory.magUnits (Succ k)) (Float.Theory.magUnitsLess 0 (Succ k) byComputing))
        (Float.Theory.magnitudeExact (Succ k) byComputing hm)

theorem Float.Theory.unitsRoundNonpos ∀ (m: Nat)
    (hm: m < 9218868437227405312):
    Float.Model.roundRatio (Int.signed True (Float.Theory.magUnits m)) 1 (-1074) True = m + 9223372036854775808 :=
  match m with
    | Zero => byComputing
    | Succ k =>
      Eq.trans
        (Float.Theory.unitsRoundNeg (Float.Theory.magUnits (Succ k)) (Float.Theory.magUnitsLess 0 (Succ k) byComputing))
        (Eq.cong (x => x + 9223372036854775808) (Float.Theory.magnitudeExact (Succ k) byComputing hm))
theorem Float.Theory.unitsRound ∀ (bits m: Nat)
    (hm: m < 9218868437227405312) (sb: Bool)
    (hb: bits = (if sb then m + 9223372036854775808 else m)):
    Float.Model.roundRatio (Int.signed sb (Float.Theory.magUnits m)) 1 (-1074) sb = bits :=
  match sb with
    | False => Eq.trans (Float.Theory.unitsRoundNonneg m hm) hb.flipped
    | True => Eq.trans (Float.Theory.unitsRoundNonpos m hm) hb.flipped

theorem Float.Theory.splitBits ∀ (bits: Nat):
    bits
      = (if Float.Model.signBit bits then Float.Model.magnitude bits + 9223372036854775808
         else Float.Model.magnitude bits) :=
  match c: Nat.leq 9223372036854775808 bits with
    | True => arithmetic [c]
    | False => byComputing

--| A finite pattern: its magnitude is below infinity's.
def Float.Theory.FiniteBits (bits: Nat): Prop := Float.Model.magnitude bits < 9218868437227405312

theorem Float.Theory.roundRatioUnitsBits ∀ (bits: Nat)
    (fin: Float.Theory.FiniteBits bits):
    Float.Model.roundRatio (Float.Model.units bits) 1 (-1074) (Float.Model.signBit bits) = bits :=
  Float.Theory.unitsRound bits (Float.Model.magnitude bits) fin (Float.Model.signBit bits) (Float.Theory.splitBits bits)

-- Addition on bit patterns

theorem Float.Theory.boolCases ∀ (b: Bool): (b = True) ∨ (b = False) := match b with
  | True => Inl byComputing
  | False => Inr byComputing

theorem Float.Theory.andFalseRight ∀ (b: Bool): (b ∧ False) = False := match b with
  | True => byComputing
  | False => byComputing

theorem Float.Theory.andTrueRight ∀ (b: Bool): (b ∧ True) = b := match b with
  | True => byComputing
  | False => byComputing

theorem Float.Theory.andSwap ∀ (a b: Bool): (a ∧ b) = (b ∧ a) := match a, b with
  | True, True => byComputing
  | True, False => byComputing
  | False, True => byComputing
  | False, False => byComputing

theorem Float.Theory.ifTrue ∀ (c: Bool) (x y: Nat) (h: c = True): (if c then x else y) = x := rewrite h then byComputing

theorem Float.Theory.ifFalse ∀ (c: Bool) (x y: Nat) (h: c = False): (if c then x else y) = y :=
  rewrite h then byComputing

-- `addBits`'s branches past the NaN check: an infinite first argument,
-- and two finite ones.

--| `addBits` of an infinite first argument: the NaN for infinities of opposite signs, else the infinity.
def Float.Theory.addInf (a b: Nat): Nat :=
  if Float.Model.isInfinite b ∧ ¬(Nat.equal a b) then 9221120237041090560 else a

--| The double nearest `n` units of 2^-1074, with sign `z` if it is zero.
def Float.Theory.finWith (n: Int) (z: Bool): Nat := Float.Model.roundScaled n (-1074) z

--| `addBits` of two finite doubles: the exact sum of their units, rounded.
def Float.Theory.addFin (a b: Nat): Nat :=
  Float.Theory.finWith
    (Int.add (Float.Model.units a) (Float.Model.units b))
    (Float.Model.signBit a ∧ Float.Model.signBit b)

theorem Float.Theory.finWithCong ∀ (n1 n2: Int) (z1 z2: Bool)
    (en: n1 = n2)
    (ez: z1 = z2):
    Float.Theory.finWith n1 z1 = Float.Theory.finWith n2 z2 :=
  rewrite en, ez then byComputing

--| `addBits` past the NaN check: an infinity if either is one, otherwise the rounded sum.
def Float.Theory.addRest (a b: Nat): Nat :=
  if Float.Model.isInfinite a then Float.Theory.addInf a b
  else if Float.Model.isInfinite b then b
  else Float.Theory.addFin a b

theorem Float.Theory.addBitsNaN ∀ (a b: Nat)
    (h: (Float.Model.isNaN a ∨ Float.Model.isNaN b) = True):
    Float.Model.addBits a b = 9221120237041090560 :=
  Float.Theory.ifTrue (Float.Model.isNaN a ∨ Float.Model.isNaN b) 9221120237041090560 (Float.Theory.addRest a b) h

theorem Float.Theory.addBitsRest ∀ (a b: Nat)
    (h: (Float.Model.isNaN a ∨ Float.Model.isNaN b) = False):
    Float.Model.addBits a b = Float.Theory.addRest a b :=
  Float.Theory.ifFalse (Float.Model.isNaN a ∨ Float.Model.isNaN b) 9221120237041090560 (Float.Theory.addRest a b) h

theorem Float.Theory.addRestInfA ∀ (a b: Nat)
    (h: Float.Model.isInfinite a = True):
    Float.Theory.addRest a b = Float.Theory.addInf a b :=
  Float.Theory.ifTrue
    (Float.Model.isInfinite a)
    (Float.Theory.addInf a b)
    (if Float.Model.isInfinite b then b else Float.Theory.addFin a b)
    h

theorem Float.Theory.addRestInfB ∀ (a b: Nat)
    (ha: Float.Model.isInfinite a = False)
    (hb: Float.Model.isInfinite b = True):
    Float.Theory.addRest a b = b :=
  Eq.trans
    (Float.Theory.ifFalse
      (Float.Model.isInfinite a)
      (Float.Theory.addInf a b)
      (if Float.Model.isInfinite b then b else Float.Theory.addFin a b)
      ha)
    (Float.Theory.ifTrue (Float.Model.isInfinite b) b (Float.Theory.addFin a b) hb)

theorem Float.Theory.addRestFin ∀ (a b: Nat)
    (ha: Float.Model.isInfinite a = False)
    (hb: Float.Model.isInfinite b = False):
    Float.Theory.addRest a b = Float.Theory.addFin a b :=
  Eq.trans
    (Float.Theory.ifFalse
      (Float.Model.isInfinite a)
      (Float.Theory.addInf a b)
      (if Float.Model.isInfinite b then b else Float.Theory.addFin a b)
      ha)
    (Float.Theory.ifFalse (Float.Model.isInfinite b) b (Float.Theory.addFin a b) hb)

theorem Float.Theory.orFalse ∀ (x y: Bool) (hx: x = False) (hy: y = False): (x ∨ y) = False :=
  rewrite hx, hy then byComputing

--| A valid pattern that is neither the NaN nor infinite is finite.
theorem Float.Theory.finiteOf ∀ (a: Nat)
    (v: Float.isValid a = True)
    (na: Float.Model.isNaN a = False)
    (ia: Float.Model.isInfinite a = False):
    Float.Theory.FiniteBits a :=
  match Float.Theory.boolCases (Nat.leq 9223372036854775808 a) with
    | Inl c =>
      arithmetic [
        Float.highBound a v (arithmetic [c]),
        c,
        (rewrite c then byComputing: Float.Model.magnitude a = a - 9223372036854775808),
        Nat.equalFalse (Float.Model.magnitude a) 9218868437227405312 ia
      ]
    | Inr c =>
      arithmetic [
        Float.lowBound a v na c,
        c,
        (rewrite c then byComputing: Float.Model.magnitude a = a),
        Nat.equalFalse (Float.Model.magnitude a) 9218868437227405312 ia
      ]

--| `addFin` is `addBits` with neither argument the NaN nor infinite.
theorem Float.Theory.addFiniteBits ∀ (a b: Nat)
    (na: Float.Model.isNaN a = False)
    (nb: Float.Model.isNaN b = False)
    (ia: Float.Model.isInfinite a = False)
    (ib: Float.Model.isInfinite b = False):
    Float.Model.addBits a b
      = Float.Model.roundRatio
        (Int.add (Float.Model.units a) (Float.Model.units b))
        1
        (-1074)
        (Float.Model.signBit a ∧ Float.Model.signBit b) :=
  Eq.trans
    (Float.Theory.addBitsRest a b (Float.Theory.orFalse (Float.Model.isNaN a) (Float.Model.isNaN b) na nb))
    (Float.Theory.addRestFin a b ia ib)

theorem Float.Theory.addFinComm ∀ (a b: Nat): Float.Theory.addFin a b = Float.Theory.addFin b a :=
  Float.Theory.finWithCong
    (Int.add (Float.Model.units a) (Float.Model.units b))
    (Int.add (Float.Model.units b) (Float.Model.units a))
    (Float.Model.signBit a ∧ Float.Model.signBit b)
    (Float.Model.signBit b ∧ Float.Model.signBit a)
    (Int.addComm (Float.Model.units a) (Float.Model.units b))
    (Float.Theory.andSwap (Float.Model.signBit a) (Float.Model.signBit b))

theorem Float.Theory.addInfComm ∀ (a b: Nat)
    (ia: Float.Model.isInfinite a = True)
    (ib: Float.Model.isInfinite b = True):
    Float.Theory.addInf a b = Float.Theory.addInf b a :=
  match Float.Theory.boolCases (Nat.equal a b) with
    | Inl e =>
      let ab: a = b := e.read
      rewrite ab then byComputing
    | Inr e =>
      Eq.trans
        (rewrite ib, e then byComputing: Float.Theory.addInf a b = 9221120237041090560)
        (Eq.flipped
          (rewrite ia, Eq.trans (Nat.equalComm b a) e then byComputing: Float.Theory.addInf b a = 9221120237041090560))

--| A case split that leaves the goal as it is, for goals that are costly to
--| search.
theorem Float.Theory.orCase ∀ [p q goal: Prop] (h: p ∨ q) (l: p → goal) (r: q → goal): goal := match h with
  | Inl a => l a
  | Inr b => r b

theorem Float.Theory.addRestComm ∀ (a b: Nat): Float.Theory.addRest a b = Float.Theory.addRest b a :=
  Float.Theory.orCase
    (Float.Theory.boolCases (Float.Model.isInfinite a))
    (ia =>
      Float.Theory.orCase
        (Float.Theory.boolCases (Float.Model.isInfinite b))
        (ib =>
          Eq.trans
            (Float.Theory.addRestInfA a b ia)
            (Eq.trans (Float.Theory.addInfComm a b ia ib) (Float.Theory.addRestInfA b a ib).flipped))
        (ib =>
          Eq.trans
            (Float.Theory.addRestInfA a b ia)
            (Eq.trans
              (rewrite ib then byComputing: Float.Theory.addInf a b = a)
              (Eq.flipped (Float.Theory.addRestInfB b a ib ia)))))
    (ia =>
      Float.Theory.orCase
        (Float.Theory.boolCases (Float.Model.isInfinite b))
        (ib =>
          Eq.trans
            (Float.Theory.addRestInfB a b ia ib)
            (Eq.trans
              (Eq.flipped (rewrite ia then byComputing: Float.Theory.addInf b a = b))
              (Float.Theory.addRestInfA b a ib).flipped))
        (ib =>
          Eq.trans
            (Float.Theory.addRestFin a b ia ib)
            (Eq.trans (Float.Theory.addFinComm a b) (Eq.flipped (Float.Theory.addRestFin b a ib ia)))))

theorem Float.Theory.addBitsComm ∀ (a b: Nat): Float.Model.addBits a b = Float.Model.addBits b a :=
  Float.Theory.orCase
    (Float.Theory.boolCases (Float.Model.isNaN a ∨ Float.Model.isNaN b))
    (n =>
      Eq.trans
        (Float.Theory.addBitsNaN a b n)
        (Eq.flipped
          (Float.Theory.addBitsNaN b a (Eq.trans (Bool.orComm (Float.Model.isNaN b) (Float.Model.isNaN a)) n))))
    (n =>
      Eq.trans
        (Float.Theory.addBitsRest a b n)
        (Eq.trans
          (Float.Theory.addRestComm a b)
          (Eq.flipped
            (Float.Theory.addBitsRest b a (Eq.trans (Bool.orComm (Float.Model.isNaN b) (Float.Model.isNaN a)) n)))))

-- Order keys of patterns

--| The order key of a bit pattern (`Float.orderKey`).
def Float.Theory.key (n: Nat): Int := Float.keyOf n (Nat.leq 9223372036854775808 n)

theorem Float.Theory.keyTo ∀ (a r s: Nat)
    (e: r = s)
    (h: Int.leq (Float.Theory.key a) (Float.Theory.key s) = True):
    Int.leq (Float.Theory.key a) (Float.Theory.key r) = True :=
  J (y w => Int.leq (Float.Theory.key a) (Float.Theory.key y) = True) h e.flipped

theorem Float.Theory.validTo ∀ (r s: Nat) (e: r = s) (h: Float.isValid s = True): Float.isValid r = True :=
  J (y w => Float.isValid y = True) h e.flipped

theorem Float.Theory.keyRefl ∀ (x: Int): Int.leq x x = True := match x with
  | OfNat n => Nat.leRefl n
  | NegSucc n => Nat.leRefl n

theorem Float.Theory.keySet ∀ (a: Nat)
    (c: Nat.leq 9223372036854775808 a = True):
    Float.Theory.key a = NegSucc (a - 9223372036854775808) :=
  rewrite c then byComputing

theorem Float.Theory.keyClear ∀ (a: Nat) (c: Nat.leq 9223372036854775808 a = False): Float.Theory.key a = OfNat a :=
  rewrite c then byComputing

--| Every valid pattern's key is at most the NaN's.
theorem Float.Theory.keyLeNaN ∀ (a: Nat)
    (v: Float.isValid a = True):
    Int.leq (Float.Theory.key a) (Float.Theory.key 9221120237041090560) = True :=
  Float.Theory.orCase
    (Float.Theory.boolCases (Nat.leq 9223372036854775808 a))
    (c =>
      Float.Theory.leqVia
        (Float.Theory.key a)
        (Float.Theory.key 9221120237041090560)
        (NegSucc (a - 9223372036854775808))
        (OfNat 9221120237041090560)
        (Float.Theory.keySet a c)
        byComputing
        byComputing)
    (c =>
      Float.Theory.leqVia
        (Float.Theory.key a)
        (Float.Theory.key 9221120237041090560)
        (OfNat a)
        (OfNat 9221120237041090560)
        (Float.Theory.keyClear a c)
        byComputing
        (Float.Theory.orCase
          (Float.Theory.boolCases (Nat.equal a 9221120237041090560))
          (e => (arithmetic [e]: Nat.leq a 9221120237041090560 = True))
          (e => (arithmetic [Float.lowBound a v e c]: Nat.leq a 9221120237041090560 = True))))

--| A finite pattern's key is below +infinity's.
theorem Float.Theory.keyLeInf ∀ (a: Nat)
    (fin: Float.Theory.FiniteBits a):
    Int.leq (Float.Theory.key a) (OfNat 9218868437227405312) = True :=
  Float.Theory.orCase
    (Float.Theory.boolCases (Nat.leq 9223372036854775808 a))
    (c =>
      Float.Theory.leqVia
        (Float.Theory.key a)
        (OfNat 9218868437227405312)
        (NegSucc (a - 9223372036854775808))
        (OfNat 9218868437227405312)
        (Float.Theory.keySet a c)
        byComputing
        byComputing)
    (c =>
      Float.Theory.leqVia
        (Float.Theory.key a)
        (OfNat 9218868437227405312)
        (OfNat a)
        (OfNat 9218868437227405312)
        (Float.Theory.keyClear a c)
        byComputing
        (arithmetic [fin, (rewrite c then byComputing: Float.Model.magnitude a = a)]: Nat.leq a 9218868437227405312
          = True))

--| The keys of the two zeros' patterns are at most `0.0`'s.
theorem Float.Theory.zeroLeZeroBits ∀ (a: Nat)
    (h: (a = 0) ∨ (a = 9223372036854775808)):
    Int.leq (Float.Theory.key a) (OfNat 0) = True :=
  match h with
    | Inl e => J (y w => Int.leq (Float.Theory.key y) (OfNat 0) = True) byComputing e.flipped
    | Inr e => J (y w => Int.leq (Float.Theory.key y) (OfNat 0) = True) byComputing e.flipped

-- Units and rounding, on patterns

theorem Float.Theory.signedZero ∀ (s: Bool) (x: Nat) (h: Int.signed s x = OfNat 0): x = 0 := match s, x with
  | False, x => Int.ofNatInjective x 0 h
  | True, Zero => byComputing

--| A pattern with no units is a zero.
theorem Float.Theory.unitsZeroIsZeroBits ∀ (a: Nat)
    (h: Float.Model.units a = OfNat 0):
    (a = 0) ∨ (a = 9223372036854775808) :=
  let m0: Float.Model.magnitude a = 0 :=
    Float.Theory.magUnitsInjective
      (Float.Model.magnitude a)
      0
      (Float.Theory.signedZero (Float.Model.signBit a) (Float.Theory.magUnits (Float.Model.magnitude a)) h)
  Float.Theory.orCase
    (Float.Theory.boolCases (Float.Model.signBit a))
    (s =>
      Inr
        (arithmetic [
          m0,
          (J
            (y w => a = (if y then Float.Model.magnitude a + 9223372036854775808 else Float.Model.magnitude a))
            (Float.Theory.splitBits a)
            s: a = Float.Model.magnitude a + 9223372036854775808)
        ]))
    (s =>
      Inl
        (arithmetic [
          m0,
          (J
            (y w => a = (if y then Float.Model.magnitude a + 9223372036854775808 else Float.Model.magnitude a))
            (Float.Theory.splitBits a)
            s: a = Float.Model.magnitude a)
        ]))

--| The two zeros' patterns have no units.
theorem Float.Theory.unitsZeroBits ∀ (a: Nat) (h: (a = 0) ∨ (a = 9223372036854775808)): Float.Model.units a = OfNat 0 :=
  match h with
    | Inl e => J (y w => Float.Model.units y = OfNat 0) byComputing e.flipped
    | Inr e => J (y w => Float.Model.units y = OfNat 0) byComputing e.flipped

--| The zero sign matters only for a zero
--| numerator.
theorem Float.Theory.roundRatioSignIrrelevant ∀ (den: Nat) (scale: Int) (z1 z2: Bool) (num: Int)
    (ne: num ≠ OfNat 0):
    Float.Model.roundRatio num den scale z1 = Float.Model.roundRatio num den scale z2 :=
  match num with
    | OfNat Zero => (ne byComputing).impossible
    | OfNat (Succ k) => byComputing
    | NegSucc k => byComputing

theorem Float.Theory.intZeroCases ∀ (x: Int): (x = OfNat 0) ∨ (x ≠ OfNat 0) := match x with
  | OfNat Zero => Inl byComputing
  | OfNat (Succ k) => Inr (h => Bool.falseNotTrue (Eq.cong (y => Nat.equal (Int.toNat y) 0) h))
  | NegSucc k => Inr (Int.negSuccNotOfNat k 0)

theorem Float.Theory.intLessAddPos ∀ (k: Nat) (pk: 0 < k) (x: Int): Int.less x (Int.add x (OfNat k)) = True :=
  match x with
    | OfNat n => (arithmetic [pk]: Nat.leq (Succ n) (n + k) = True)
    | NegSucc n =>
      match h: Succ n - k with
        | Zero => byComputing
        | Succ j => (arithmetic [h, pk]: Nat.leq (Succ j) n = True)

theorem Float.Theory.orLeftFalse ∀ (x y: Bool) (h: (x ∨ y) = False): x = False := match x with | False => byComputing

theorem Float.Theory.orRightFalse ∀ (x y: Bool) (h: (x ∨ y) = False): y = False := match y with
  | True => cases
  | False => byComputing

--| The result of `addBits` is a valid pattern.
theorem Float.Theory.addBitsValid ∀ (a b: Nat)
    (va: Float.isValid a = True)
    (vb: Float.isValid b = True):
    Float.isValid (Float.Model.addBits a b) = True :=
  Float.Theory.orCase
    (Float.Theory.boolCases (Float.Model.isNaN a ∨ Float.Model.isNaN b))
    (n =>
      Float.Theory.validTo (Float.Model.addBits a b) 9221120237041090560 (Float.Theory.addBitsNaN a b n) byComputing)
    (n =>
      Float.Theory.validTo
        (Float.Model.addBits a b)
        (Float.Theory.addRest a b)
        (Float.Theory.addBitsRest a b n)
        (Float.Theory.orCase
          (Float.Theory.boolCases (Float.Model.isInfinite a))
          (ia =>
            Float.Theory.validTo
              (Float.Theory.addRest a b)
              (Float.Theory.addInf a b)
              (Float.Theory.addRestInfA a b ia)
              (Float.Theory.orCase
                (Float.Theory.boolCases (Float.Model.isInfinite b ∧ ¬(Nat.equal a b)))
                (c =>
                  Float.Theory.validTo
                    (Float.Theory.addInf a b)
                    9221120237041090560
                    (Float.Theory.ifTrue (Float.Model.isInfinite b ∧ ¬(Nat.equal a b)) 9221120237041090560 a c)
                    byComputing)
                (c =>
                  Float.Theory.validTo
                    (Float.Theory.addInf a b)
                    a
                    (Float.Theory.ifFalse (Float.Model.isInfinite b ∧ ¬(Nat.equal a b)) 9221120237041090560 a c)
                    va)))
          (ia =>
            Float.Theory.orCase
              (Float.Theory.boolCases (Float.Model.isInfinite b))
              (ib => Float.Theory.validTo (Float.Theory.addRest a b) b (Float.Theory.addRestInfB a b ia ib) vb)
              (ib =>
                Float.Theory.validTo
                  (Float.Theory.addRest a b)
                  (Float.Theory.addFin a b)
                  (Float.Theory.addRestFin a b ia ib)
                  (Float.Theory.roundRatioValid 1
                    (-1074)
                    (Float.Model.signBit a ∧ Float.Model.signBit b)
                    byComputing
                    (Int.add (Float.Model.units a) (Float.Model.units b)))))))

--| The trigger law on patterns: adding a pattern with the sign bit clear
--| never moves down the total order.
theorem Float.Theory.addFinMono ∀ (a b: Nat)
    (fa: Float.Theory.FiniteBits a)
    (sb: Nat.leq 9223372036854775808 b = False):
    Int.leq (Float.Theory.key a) (Float.Theory.key (Float.Theory.addFin a b)) = True :=
  let ub: Float.Model.units b = OfNat (Float.Theory.magUnits b) := rewrite sb then byComputing
  let sum: Float.Theory.addFin a b
    = Float.Theory.finWith
      (Int.add (Float.Model.units a) (OfNat (Float.Theory.magUnits b)))
      (Float.Model.signBit a ∧ False) :=
    Float.Theory.finWithCong
      (Int.add (Float.Model.units a) (Float.Model.units b))
      (Int.add (Float.Model.units a) (OfNat (Float.Theory.magUnits b)))
      (Float.Model.signBit a ∧ Float.Model.signBit b)
      (Float.Model.signBit a ∧ False)
      (Eq.cong (k => Int.add (Float.Model.units a) k) ub)
      (Eq.cong (z => Float.Model.signBit a ∧ z) sb)
  let self: Float.Theory.roundKey (Float.Model.units a) 1 (-1074) (Float.Model.signBit a) = Float.Theory.key a :=
    Eq.cong Float.Theory.key (Float.Theory.roundRatioUnitsBits a fa)
  Float.Theory.keyTo a
    (Float.Theory.addFin a b)
    (Float.Theory.finWith
      (Int.add (Float.Model.units a) (OfNat (Float.Theory.magUnits b)))
      (Float.Model.signBit a ∧ False))
    sum
    (Float.Theory.orCase
      (Float.Theory.zeroOrPos (Float.Theory.magUnits b))
      (k0 =>
        let zero: Float.Theory.finWith
          (Int.add (Float.Model.units a) (OfNat (Float.Theory.magUnits b)))
          (Float.Model.signBit a ∧ False)
          = Float.Theory.finWith (Float.Model.units a) False :=
          Float.Theory.finWithCong
            (Int.add (Float.Model.units a) (OfNat (Float.Theory.magUnits b)))
            (Float.Model.units a)
            (Float.Model.signBit a ∧ False)
            False
            (Eq.trans (Eq.cong (k => Int.add (Float.Model.units a) (OfNat k)) k0) (Int.addZero (Float.Model.units a)))
            (Float.Theory.andFalseRight (Float.Model.signBit a))
        Float.Theory.keyTo a
          (Float.Theory.finWith
            (Int.add (Float.Model.units a) (OfNat (Float.Theory.magUnits b)))
            (Float.Model.signBit a ∧ False))
          (Float.Theory.finWith (Float.Model.units a) False)
          zero
          (Float.Theory.orCase
            (Float.Theory.intZeroCases (Float.Model.units a))
            (u0 =>
              Float.Theory.leqVia
                (Float.Theory.key a)
                (Float.Theory.key (Float.Theory.finWith (Float.Model.units a) False))
                (Float.Theory.key a)
                (OfNat 0)
                byComputing
                (Eq.cong (n => Float.Theory.key (Float.Theory.finWith n False)) u0)
                (Float.Theory.zeroLeZeroBits a (Float.Theory.unitsZeroIsZeroBits a u0)))
            (un =>
              Float.Theory.leqVia
                (Float.Theory.key a)
                (Float.Theory.key (Float.Theory.finWith (Float.Model.units a) False))
                (Float.Theory.key a)
                (Float.Theory.key a)
                byComputing
                (Eq.trans
                  (Eq.cong Float.Theory.key
                    (Float.Theory.roundRatioSignIrrelevant 1
                      (-1074)
                      False
                      (Float.Model.signBit a)
                      (Float.Model.units a)
                      un))
                  self)
                (Float.Theory.keyRefl (Float.Theory.key a)))))
      (pk =>
        Float.Theory.leqVia
          (Float.Theory.key a)
          (Float.Theory.key
            (Float.Theory.finWith
              (Int.add (Float.Model.units a) (OfNat (Float.Theory.magUnits b)))
              (Float.Model.signBit a ∧ False)))
          (Float.Theory.roundKey (Float.Model.units a) 1 (-1074) (Float.Model.signBit a))
          (Float.Theory.roundKey
            (Int.add (Float.Model.units a) (OfNat (Float.Theory.magUnits b)))
            1
            (-1074)
            (Float.Model.signBit a ∧ False))
          self.flipped
          byComputing
          (Float.Theory.roundKeyMono 1
            (-1074)
            (Float.Model.signBit a)
            (Float.Model.signBit a ∧ False)
            byComputing
            (Float.Model.units a)
            (Int.add (Float.Model.units a) (OfNat (Float.Theory.magUnits b)))
            (Float.Theory.intLessAddPos (Float.Theory.magUnits b) pk (Float.Model.units a)))))

theorem Float.Theory.addBitsMono ∀ (a b: Nat)
    (va: Float.isValid a = True)
    (vb: Float.isValid b = True)
    (sb: Nat.leq 9223372036854775808 b = False):
    Int.leq (Float.Theory.key a) (Float.Theory.key (Float.Model.addBits a b)) = True :=
  Float.Theory.orCase
    (Float.Theory.boolCases (Float.Model.isNaN a ∨ Float.Model.isNaN b))
    (n =>
      Float.Theory.keyTo a
        (Float.Model.addBits a b)
        9221120237041090560
        (Float.Theory.addBitsNaN a b n)
        (Float.Theory.keyLeNaN a va))
    (n =>
      Float.Theory.keyTo a
        (Float.Model.addBits a b)
        (Float.Theory.addRest a b)
        (Float.Theory.addBitsRest a b n)
        (Float.Theory.orCase
          (Float.Theory.boolCases (Float.Model.isInfinite a))
          (ia =>
            Float.Theory.keyTo a
              (Float.Theory.addRest a b)
              (Float.Theory.addInf a b)
              (Float.Theory.addRestInfA a b ia)
              (Float.Theory.orCase
                (Float.Theory.boolCases (Float.Model.isInfinite b ∧ ¬(Nat.equal a b)))
                (c =>
                  Float.Theory.keyTo a
                    (Float.Theory.addInf a b)
                    9221120237041090560
                    (Float.Theory.ifTrue (Float.Model.isInfinite b ∧ ¬(Nat.equal a b)) 9221120237041090560 a c)
                    (Float.Theory.keyLeNaN a va))
                (c =>
                  Float.Theory.keyTo a
                    (Float.Theory.addInf a b)
                    a
                    (Float.Theory.ifFalse (Float.Model.isInfinite b ∧ ¬(Nat.equal a b)) 9221120237041090560 a c)
                    (Float.Theory.keyRefl (Float.Theory.key a)))))
          (ia =>
            let fa: Float.Theory.FiniteBits a :=
              Float.Theory.finiteOf a va (Float.Theory.orLeftFalse (Float.Model.isNaN a) (Float.Model.isNaN b) n) ia
            Float.Theory.orCase
              (Float.Theory.boolCases (Float.Model.isInfinite b))
              (ib =>
                let binf: b = 9218868437227405312 :=
                  Nat.equalSound b 9218868437227405312
                    (J (y w => Nat.equal (if y then b - 9223372036854775808 else b) 9218868437227405312 = True) ib sb)
                Float.Theory.keyTo a
                  (Float.Theory.addRest a b)
                  9218868437227405312
                  (Eq.trans (Float.Theory.addRestInfB a b ia ib) binf)
                  (Float.Theory.keyLeInf a fa))
              (ib =>
                Float.Theory.keyTo a
                  (Float.Theory.addRest a b)
                  (Float.Theory.addFin a b)
                  (Float.Theory.addRestFin a b ia ib)
                  (Float.Theory.addFinMono a b fa sb)))))

theorem Float.Theory.addNegZeroBits ∀ (a: Nat)
    (va: Float.isValid a = True):
    Float.Model.addBits a 9223372036854775808 = a :=
  Float.Theory.orCase
    (Float.Theory.boolCases (Float.Model.isNaN a))
    (n => Eq.trans (Float.Theory.addBitsNaN a 9223372036854775808 (rewrite n then byComputing)) n.read.flipped)
    (n =>
      Eq.trans
        (Float.Theory.addBitsRest a 9223372036854775808
          (Float.Theory.orFalse (Float.Model.isNaN a) False n byComputing))
        (Float.Theory.orCase
          (Float.Theory.boolCases (Float.Model.isInfinite a))
          (ia => Eq.trans (Float.Theory.addRestInfA a 9223372036854775808 ia) byComputing)
          (ia =>
            Eq.trans
              (Float.Theory.addRestFin a 9223372036854775808 ia byComputing)
              (Eq.trans
                (Float.Theory.finWithCong
                  (Int.add (Float.Model.units a) (OfNat 0))
                  (Float.Model.units a)
                  (Float.Model.signBit a ∧ True)
                  (Float.Model.signBit a)
                  (Int.addZero (Float.Model.units a))
                  (Float.Theory.andTrueRight (Float.Model.signBit a)))
                (Float.Theory.roundRatioUnitsBits a (Float.Theory.finiteOf a va n ia))))))

--| Reading a valid pattern back.
theorem Float.Theory.ofBitsFromBits ∀ (b: Nat) (c: Bool)
    (h: Float.isValid b = c)
    (e: c = True):
    (Float.ofBitsFrom b c h).bits = b :=
  match c with | True => byComputing

theorem Float.Theory.ofBitsBits ∀ (b: Nat) (v: Float.isValid b = True): (Float.ofBits b).bits = b :=
  Float.Theory.ofBitsFromBits b (Float.isValid b) byComputing v

theorem Float.Theory.signClear ∀ (b: Nat)
    (h: Int.leq (OfNat 0) (Float.Theory.key b) = True):
    Nat.leq 9223372036854775808 b = False :=
  Float.Theory.orCase (Float.Theory.boolCases (Nat.leq 9223372036854775808 b)) (c => cases) (c => c)

-- Units and rounding, on doubles

theorem Float.Theory.finiteBits ∀ (x: Float) (fin: Float.isFinite x = True): Float.Theory.FiniteBits x.bits :=
  let g: Nat.leq 9218868437227405312 (Float.Model.magnitude x.bits) = False := fin.read
  arithmetic [g]

theorem Float.Theory.finiteNotNaN ∀ (a: Nat) (fin: Float.Theory.FiniteBits a): Float.Model.isNaN a = False :=
  Bool.falseOfNotTrue (Float.Model.isNaN a) (h => Bool.falseNotTrue (J (y w => Float.Theory.FiniteBits y) fin h.read))

theorem Float.Theory.finiteNotInfinite ∀ (a: Nat) (fin: Float.Theory.FiniteBits a): Float.Model.isInfinite a = False :=
  Bool.falseOfNotTrue (Float.Model.isInfinite a) (h => arithmetic [fin, h])

--| The patterns of a zero.
theorem Float.Theory.zeroBits ∀ (x: Float) (h: Float.isZero x = True): (x.bits = 0) ∨ (x.bits = 9223372036854775808) :=
  Float.Theory.orCase (Float.Theory.boolCases (Nat.equal x.bits 0)) (e => Inl e.read) (e =>
    Inr (Nat.equalSound x.bits 9223372036854775808 (J (y w => (y ∨ Nat.equal x.bits 9223372036854775808) = True) h e)))

theorem Float.Theory.zeroOfBits ∀ (x: Float)
    (h: (x.bits = 0) ∨ (x.bits = 9223372036854775808)):
    Float.isZero x = True :=
  match h with
    | Inl e => J (y w => (Nat.equal y 0 ∨ Nat.equal y 9223372036854775808) = True) byComputing e.flipped
    | Inr e => J (y w => (Nat.equal y 0 ∨ Nat.equal y 9223372036854775808) = True) byComputing e.flipped

--| A zero has no units.
theorem Float.Theory.unitsZero ∀ (x: Float) (h: Float.isZero x = True): Float.Theory.units x = OfNat 0 :=
  Float.Theory.unitsZeroBits x.bits (Float.Theory.zeroBits x h)

test "Float.Theory.unitsZero" :=
  Float.Theory.units 0.0 == OfNat 0
    ∧ Float.Theory.units (-0.0) == OfNat 0
    ∧ Float.Theory.units 5e-324 == OfNat 1
    ∧ Float.Theory.units (-5e-324) == NegSucc 0

--| A double with no units is a zero.
theorem Float.Theory.unitsZeroIsZero ∀ (x: Float) (h: Float.Theory.units x = OfNat 0): Float.isZero x = True :=
  Float.Theory.zeroOfBits x (Float.Theory.unitsZeroIsZeroBits x.bits h)

test "Float.Theory.unitsZeroIsZero" :=
  Float.isZero (-0.0) ∧ ¬(Float.Theory.units 5e-324 == OfNat 0) ∧ ¬(Float.Theory.units (-5e-324) == OfNat 0)

--| A double above `0.0` has positive units.
theorem Float.Theory.unitsPositive ∀ (x: Float) (h: 0.0 < x): Int.less (OfNat 0) (Float.Theory.units x) = True :=
  Float.Theory.orCase (Float.Theory.boolCases (Nat.leq 9223372036854775808 x.bits)) (c => cases) (c =>
    let pos: Nat.leq 1 x.bits = True := J (y w => Int.less (OfNat 0) (Float.keyOf x.bits y) = True) h c
    let u: Float.Theory.units x = OfNat (Float.Theory.magUnits x.bits) := rewrite c then byComputing
    Float.Theory.orCase
      (Float.Theory.zeroOrPos (Float.Theory.magUnits x.bits))
      (k0 => Void.impossible (arithmetic [pos, Float.Theory.magUnitsInjective x.bits 0 k0]))
      (pk => rewrite u then (arithmetic [pk]: Nat.leq 1 (Float.Theory.magUnits x.bits) = True)))

test "Float.Theory.unitsPositive" :=
  Float.Theory.units 5e-324 == OfNat 1
    ∧ Float.Theory.units 1.0 == OfNat (Float.Model.pow2 1074)
    ∧ Float.Theory.units 1.7976931348623157e308 == OfNat (Float.Model.pow2 2045 * 9007199254740991)

--| Rounding a finite double's units, with its own sign for a zero, gives it
--| back.
theorem Float.Theory.roundRatioUnits ∀ (x: Float)
    (fin: Float.isFinite x = True):
    Float.ofBits (Float.Model.roundRatio (Float.Theory.units x) 1 (-1074) (Float.Model.signBit x.bits)) = x :=
  Float.bitsExt
    (Float.ofBits (Float.Model.roundRatio (Float.Theory.units x) 1 (-1074) (Float.Model.signBit x.bits)))
    x
    (Eq.trans
      (Float.Theory.ofBitsBits
        (Float.Model.roundRatio (Float.Theory.units x) 1 (-1074) (Float.Model.signBit x.bits))
        (Float.Theory.roundRatioValid 1 (-1074) (Float.Model.signBit x.bits) byComputing (Float.Theory.units x)))
      (Float.Theory.roundRatioUnitsBits x.bits (Float.Theory.finiteBits x fin)))

test "Float.Theory.roundRatioUnits" :=
  Float.ofBits (Float.Model.roundRatio (OfNat 0) 1 (-1074) True) == -0.0
    ∧ Float.ofBits (Float.Model.roundRatio (OfNat 1) 1 (-1074) False) == 5e-324
    ∧ Float.ofBits (Float.Model.roundRatio (Float.Theory.units 0.1) 1 (-1074) False) == 0.1
    ∧ Float.ofBits (Float.Model.roundRatio (Float.Theory.units (-1.7976931348623157e308)) 1 (-1074) True)
      == -1.7976931348623157e308

test "Float.Theory.roundRatioSignIrrelevant" :=
  Float.Model.roundRatio (OfNat 3) 2 (-1074) True == Float.Model.roundRatio (OfNat 3) 2 (-1074) False
    ∧ Float.Model.roundRatio (NegSucc 0) 1 (-1074) False == Float.Model.roundRatio (NegSucc 0) 1 (-1074) True
    ∧ ¬(Float.Model.roundRatio (OfNat 0) 1 (-1074) True == Float.Model.roundRatio (OfNat 0) 1 (-1074) False)

theorem Float.Theory.roundRatioZero ∀ (den: Nat) (scale: Int):
    Float.ofBits (Float.Model.roundRatio (OfNat 0) den scale False) = 0.0 :=
  Float.bitsExt (Float.ofBits (Float.Model.roundRatio (OfNat 0) den scale False)) 0.0 byComputing

test "Float.Theory.roundRatioZero" :=
  Float.ofBits (Float.Model.roundRatio (OfNat 0) 7 (-1074) False) == 0.0
    ∧ Float.ofBits (Float.Model.roundRatio (OfNat 0) 7 (-1074) True) == -0.0

--| Rounding is strictly monotone in the numerator, for any zero signs.
theorem Float.Theory.roundRatioStrictMono ∀ (den: Nat) (scale: Int) (z1 z2: Bool)
    (pd: 0 < den) (num1 num2: Int)
    (lt: Int.less num1 num2 = True):
    Float.ofBits (Float.Model.roundRatio num1 den scale z1)
      <= Float.ofBits (Float.Model.roundRatio num2 den scale z2) :=
  Float.Theory.leqVia
    (Float.orderKey (Float.ofBits (Float.Model.roundRatio num1 den scale z1)))
    (Float.orderKey (Float.ofBits (Float.Model.roundRatio num2 den scale z2)))
    (Float.Theory.roundKey num1 den scale z1)
    (Float.Theory.roundKey num2 den scale z2)
    (Eq.cong Float.Theory.key
      (Float.Theory.ofBitsBits
        (Float.Model.roundRatio num1 den scale z1)
        (Float.Theory.roundRatioValid den scale z1 pd num1)))
    (Eq.cong Float.Theory.key
      (Float.Theory.ofBitsBits
        (Float.Model.roundRatio num2 den scale z2)
        (Float.Theory.roundRatioValid den scale z2 pd num2)))
    (Float.Theory.roundKeyMono den scale z1 z2 pd num1 num2 lt)

--| The non-strict form is false: equal numerators of `0` differ by the sign.
test "Float.Theory.roundRatioStrictMono" :=
  Float.ofBits (Float.Model.roundRatio (NegSucc 0) 1 (-1074) False)
    <= Float.ofBits (Float.Model.roundRatio (OfNat 0) 1 (-1074) True)
    ∧ Float.ofBits (Float.Model.roundRatio (OfNat 0) 1 (-1074) True)
      <= Float.ofBits (Float.Model.roundRatio (OfNat 1) 3 (-1074) True)
    ∧ Float.ofBits (Float.Model.roundRatio (OfNat 1) 3 (-1074) False)
      <= Float.ofBits (Float.Model.roundRatio (OfNat 2) 3 (-1074) False)
    ∧ ¬(Float.ofBits (Float.Model.roundRatio (OfNat 0) 1 (-1074) False)
      <= Float.ofBits (Float.Model.roundRatio (OfNat 0) 1 (-1074) True))

--| The sum of two finite doubles: their units' sum, rounded, with `-0.0` only
--| when both are negative.
theorem Float.Theory.addFinite ∀ (x y: Float)
    (fx: Float.isFinite x = True)
    (fy: Float.isFinite y = True):
    x + y
      = Float.ofBits
        (Float.Model.roundRatio
          (Int.add (Float.Theory.units x) (Float.Theory.units y))
          1
          (-1074)
          (Float.Model.signBit x.bits ∧ Float.Model.signBit y.bits)) :=
  match x, y with
    | { bits = a, valid = p }, { bits = b, valid = q } =>
      let fa: Float.Theory.FiniteBits a := Float.Theory.finiteBits { bits = a, valid = p } fx
      let fb: Float.Theory.FiniteBits b := Float.Theory.finiteBits { bits = b, valid = q } fy
      Eq.cong Float.ofBits
        (Float.Theory.addFiniteBits a b
          (Float.Theory.finiteNotNaN a fa)
          (Float.Theory.finiteNotNaN b fb)
          (Float.Theory.finiteNotInfinite a fa)
          (Float.Theory.finiteNotInfinite b fb))

test "Float.Theory.addFinite" :=
  (-0.0) + 0.0 == Float.ofBits (Float.Model.roundRatio (OfNat 0) 1 (-1074) False)
    ∧ (-0.0) + (-0.0) == Float.ofBits (Float.Model.roundRatio (OfNat 0) 1 (-1074) True)
    ∧ 1.7976931348623157e308 + 1.7976931348623157e308 == Float.infinity
    ∧ 5e-324 + 5e-324 == Float.ofBits 2

--| A zero is at most `0.0`.
theorem Float.Theory.zeroLeZero ∀ (x: Float) (h: Float.isZero x = True): x <= 0.0 :=
  Float.Theory.zeroLeZeroBits x.bits (Float.Theory.zeroBits x h)

test "Float.Theory.zeroLeZero" := -0.0 <= 0.0 <= 0.0 ∧ ¬(0.0 <= -0.0) ∧ ¬(5e-324 <= 0.0)

-- The laws

--| Adding a non-negative double never moves down the total order, for every
--| `s` and `d`, the NaN and infinities included.
theorem Float.addMonotoneRight ∀ (s d: Float) (h: 0.0 <= d): s <= s + d := match s, d with
  | { bits = a, valid = p }, { bits = b, valid = q } =>
    J
      (y w => Int.leq (Float.Theory.key a) (Float.Theory.key y) = True)
      (Float.Theory.addBitsMono a b p q (Float.Theory.signClear b h))
      (Eq.flipped (Float.Theory.ofBitsBits (Float.Model.addBits a b) (Float.Theory.addBitsValid a b p q)))

test "Float.addMonotoneRight" :=
  1.5 <= 1.5 + 0.0
    ∧ -0.0 <= -0.0 + 0.0
    ∧ 0.0 <= 0.0 + 0.0
    ∧ 1.0 <= 1.0 + 5e-324
    ∧ 5e-324 <= 5e-324 + 5e-324
    ∧ -5e-324 <= -5e-324 + 5e-324
    ∧ 1.7976931348623157e308 <= 1.7976931348623157e308 + 1.7976931348623157e308
    ∧ -Float.infinity <= -Float.infinity + Float.infinity
    ∧ Float.infinity <= Float.infinity + 1.0
    ∧ Float.nan <= Float.nan + 1.0
    ∧ 1.0 <= 1.0 + Float.nan
    ∧ -1.0 <= -1.0 + Float.nan
    ∧ -2.0 <= -2.0 + Float.infinity

--| `x <= y → x + z <= y + z` is false: `-infinity <= 0.0`, but with `z =
--| +infinity` the left side is the NaN, above `+infinity`.
test "adding to both sides of `<=` is not monotone" :=
  -Float.infinity <= 0.0 ∧ ¬(-Float.infinity + Float.infinity <= 0.0 + Float.infinity)

--| `0.0 <= d → s - d <= s` is false at `d = NaN`.
test "subtracting a non-negative double can go up" := 0.0 <= Float.nan ∧ ¬(1.0 - Float.nan <= 1.0)

theorem Float.addComm ∀ (x y: Float): x + y = y + x := match x, y with
  | { bits = a, valid = p }, { bits = b, valid = q } => Eq.cong Float.ofBits (Float.Theory.addBitsComm a b)

test "Float.addComm" :=
  0.1 + 0.2 == 0.2 + 0.1
    ∧ (-0.0) + 0.0 == 0.0 + (-0.0)
    ∧ (-0.0) + (-0.0) == (-0.0) + (-0.0)
    ∧ Float.infinity + (-Float.infinity) == (-Float.infinity) + Float.infinity
    ∧ Float.nan + 1.0 == 1.0 + Float.nan
    ∧ 1.7976931348623157e308 + 1e308 == 1e308 + 1.7976931348623157e308
    ∧ 5e-324 + 1.0 == 1.0 + 5e-324

theorem Float.subAddNeg ∀ (x y: Float): x - y = x + (-y) := byComputing

test "Float.subAddNeg" :=
  1.0 - 0.0 == 1.0 + (-0.0)
    ∧ 0.0 - 0.0 == 0.0 + (-0.0)
    ∧ Float.infinity - Float.infinity == Float.infinity + (-Float.infinity)
    ∧ 1.0 - Float.nan == 1.0 + (-Float.nan)
    ∧ 5e-324 - 5e-324 == 5e-324 + (-5e-324)

--| `x + (-0.0)` is `x`, zeros included.
theorem Float.addNegZero ∀ (x: Float): x + (-0.0) = x := match x with
  | { bits = a, valid = p } =>
    Float.bitsExt
      (Float.ofBits (Float.Model.addBits a 9223372036854775808))
      { bits = a, valid = p }
      (Eq.trans
        (Float.Theory.ofBitsBits
          (Float.Model.addBits a 9223372036854775808)
          (Float.Theory.addBitsValid a 9223372036854775808 p byComputing))
        (Float.Theory.addNegZeroBits a p))

test "Float.addNegZero" :=
  0.0 + (-0.0) == 0.0
    ∧ (-0.0) + (-0.0) == -0.0
    ∧ 1.5 + (-0.0) == 1.5
    ∧ 5e-324 + (-0.0) == 5e-324
    ∧ Float.infinity + (-0.0) == Float.infinity
    ∧ (-Float.infinity) + (-0.0) == -Float.infinity
    ∧ (Float.nan + (-0.0)).bits == Float.nan.bits

--| `x + 0.0 = x` is false at `x = -0.0`.
test "adding 0.0 is not the identity" := ¬((-0.0) + 0.0 == -0.0)

--| `-(x + y) = (-x) + (-y)` is false at `x = 0.0`, `y = -0.0`.
test "negation does not distribute over addition" := ¬(-(0.0 + (-0.0)) == (-0.0) + 0.0)
