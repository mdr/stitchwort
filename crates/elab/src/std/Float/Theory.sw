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
      | True => rewrite z.read
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
  | Zero | Succ _ => byComputing

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
  rewrite d, (arithmetic: e * 4503599627370496 + f - e * 4503599627370496 = f), Float.Theory.pow2Pow (e - 1)

--| A normal pattern, exponent field `e + 1`.
theorem Float.Theory.magUnitsFieldNext ∀ (e f: Nat)
    (h: f < 4503599627370496):
    Float.Theory.magUnits (e * 4503599627370496 + 4503599627370496 + f) = Nat.pow 2 e * (f + 4503599627370496) :=
  calc Float.Theory.magUnits (e * 4503599627370496 + f + 4503599627370496)
    _ = Float.Theory.magUnits (e * 4503599627370496 + f + 4503599627370496) :=
      Eq.cong Float.Theory.magUnits
        (arithmetic: e * 4503599627370496 + 4503599627370496 + f = (e + 1) * 4503599627370496 + f)
    _ = Nat.pow 2 e * (f + 4503599627370496) := Float.Theory.magUnitsField (e + 1) f h
    _ = Nat.pow 2 e * (f + 4503599627370496) := byComputing

--| A subnormal's units are its bits.
theorem Float.Theory.magUnitsLow ∀ (q: Nat) (h: q < 4503599627370496): Float.Theory.magUnits q = q :=
  Float.Theory.magUnitsField 0 q h

--| `e × 2^52 + q`, for a significand `q` with its leading bit, is
--| `2^e × q` units.
theorem Float.Theory.magUnitsNormal ∀ (e q: Nat)
    (lo: 4503599627370496 ≤ q)
    (hi: q < 9007199254740992):
    Float.Theory.magUnits (e * 4503599627370496 + q) = Nat.pow 2 e * q :=
  calc Float.Theory.magUnits (e * 4503599627370496 + q)
    _ = Float.Theory.magUnits (e * 4503599627370496 + (q - 4503599627370496) + 4503599627370496) :=
      Eq.cong Float.Theory.magUnits
        (arithmetic: e * 4503599627370496 + q = e * 4503599627370496 + 4503599627370496 + (q - 4503599627370496))
    _ = Nat.pow 2 e * (q - 4503599627370496 + 4503599627370496) :=
      Float.Theory.magUnitsFieldNext e (q - 4503599627370496) arithmetic
    _ = Nat.pow 2 e * q := Eq.cong (t => Nat.pow 2 e * t) (arithmetic: q - 4503599627370496 + 4503599627370496 = q)

--| The first pattern of exponent field `e + 1`, and of `e + 2`.
theorem Float.Theory.magUnitsWholeAt ∀ (e z: Nat)
    (hz: z = 0):
    Float.Theory.magUnits (e * 4503599627370496 + 4503599627370496 + z) = Nat.pow 2 e * 4503599627370496 :=
  calc Float.Theory.magUnits (e * 4503599627370496 + z + 4503599627370496)
    _ = Nat.pow 2 e * (z + 4503599627370496) := Float.Theory.magUnitsFieldNext e z (arithmetic: z < 4503599627370496)
    _ = z * Nat.pow 2 e + (Nat.pow 2 e * 4503599627370496) :=
      (algebra: Nat.pow 2 e * (z + 4503599627370496) = z * Nat.pow 2 e + Nat.pow 2 e * 4503599627370496)
    _ = Nat.pow 2 e * 4503599627370496 := Eq.cong (t => t * Nat.pow 2 e + Nat.pow 2 e * 4503599627370496) hz

theorem Float.Theory.magUnitsWhole ∀ (e: Nat):
    Float.Theory.magUnits (e * 4503599627370496 + 4503599627370496) = Nat.pow 2 e * 4503599627370496 :=
  Eq.trans
    (Eq.cong Float.Theory.magUnits
      (arithmetic: e * 4503599627370496 + 4503599627370496 = e * 4503599627370496 + 4503599627370496 + 0))
    (Float.Theory.magUnitsWholeAt e 0 byComputing)

theorem Float.Theory.magUnitsCarry ∀ (e: Nat):
    Float.Theory.magUnits (e * 4503599627370496 + 9007199254740992) = Nat.pow 2 e * 9007199254740992 :=
  calc Float.Theory.magUnits (e * 4503599627370496 + 9007199254740992)
    _ = Float.Theory.magUnits (e * 4503599627370496 + 9007199254740992) :=
      Eq.cong Float.Theory.magUnits
        (arithmetic: e * 4503599627370496 + 9007199254740992 = (e + 1) * 4503599627370496 + 4503599627370496)
    _ = Nat.pow 2 e * 2 * 4503599627370496 := Float.Theory.magUnitsWhole (e + 1)
    _ = Nat.pow 2 e * 2 * 4503599627370496 := Eq.cong (t => Nat.pow 2 t * 4503599627370496) (Nat.addOne e)
    _ = Nat.pow 2 e * 9007199254740992 := (algebra: Nat.pow 2 e * 2 * 4503599627370496 = Nat.pow 2 e * 9007199254740992)

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
  rewrite d, (arithmetic [e]: n - h * 2 = 0)

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
  calc Float.Theory.magUnits 9218868437227405311 * b + Float.Theory.magUnits 9218868437227405312 * b
    _ = (Float.Theory.magUnits 9218868437227405311 + Float.Theory.magUnits 9218868437227405312) * b :=
      Eq.flipped
        (Nat.mulDistribRight (Float.Theory.magUnits 9218868437227405311) (Float.Theory.magUnits 9218868437227405312) b)
    _ = (Float.Theory.overflowUnits + Float.Theory.overflowUnits) * b :=
      Eq.cong
        (k => k * b)
        (byComputing: Float.Theory.magUnits 9218868437227405311 + Float.Theory.magUnits 9218868437227405312
          = Float.Theory.overflowUnits + Float.Theory.overflowUnits)
    _ = Float.Theory.overflowUnits * b + Float.Theory.overflowUnits * b :=
      Nat.mulDistribRight Float.Theory.overflowUnits Float.Theory.overflowUnits b
    _ = b * Float.Theory.overflowUnits + b * Float.Theory.overflowUnits :=
      Eq.cong (k => k + k) (Nat.mulComm Float.Theory.overflowUnits b)

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

theorem Float.Theory.isEvenOfZero ∀ (n: Nat) (e: n - Nat.divFuel n n 2 * 2 = 0): Float.Theory.IsEven n := rewrite e

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
      (algebra: u * d1 * d2 = u * d2 * d1)

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
  calc s * (p * q * (r * 2))
    _ = p * s * r * (q * 2) := (algebra: s * (p * q * (r * 2)) = p * s * r * (q * 2))
    _ = u * v * (q * 2) := Eq.cong (x => x * (q * 2)) ih
    _ = v * (u * q * 2) := (algebra: u * v * (q * 2) = v * (u * q * 2))
    _ = v * (w * s) := Eq.cong (x => v * x) step
    _ = s * (w * v) := (algebra: v * (w * s) = s * (w * v))

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
  rewrite (arithmetic: a - (x + a) = 0), (arithmetic: x + a - a = x)

--| `2^E × top / bottom` at `shift + E = s` is `n / den × 2^s`.
theorem Float.Theory.shiftCross ∀ (n den u v us vs x: Nat)
    (rel: u * vs * x = us * v):
    x * (n * u) * (den * vs) = n * us * (den * v) :=
  calc x * (n * u) * (den * vs)
    _ = n * den * (u * vs * x) := (algebra: x * (n * u) * (den * vs) = n * den * (u * vs * x))
    _ = n * den * (us * v) := Eq.cong (y => n * den * y) rel
    _ = n * us * (den * v) := (algebra: n * den * (us * v) = n * us * (den * v))

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
    calc Float.Theory.upPow c * Nat.pow 2 a
      _ = Float.Theory.upPow c * 1 * Nat.pow 2 a :=
        (algebra: Float.Theory.upPow c * Nat.pow 2 a = Float.Theory.upPow c * 1 * Nat.pow 2 a)
      _ = Nat.pow 2 (d + 53) * Float.Theory.downPow c := shifted
      _ = Nat.pow 2 d * Nat.pow 2 53 * Float.Theory.downPow c :=
        Eq.cong (x => x * Float.Theory.downPow c) (Nat.powAdd 2 d 53)
      _ = Nat.pow 2 d * 9007199254740992 * Float.Theory.downPow c :=
        (algebra: Nat.pow 2 d * Nat.pow 2 53 * Float.Theory.downPow c
          = Nat.pow 2 d * 9007199254740992 * Float.Theory.downPow c)
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
  rewrite (arithmetic [h]: Nat.leq 9223372036854775808 m = False)

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
  match z with | True | False => byComputing

theorem Float.Theory.roundKeyZeroGe ∀ (den: Nat) (scale: Int) (z: Bool) (m: Nat):
    Int.leq (NegSucc m) (Float.Theory.roundKey (OfNat 0) den scale z) = True :=
  match z with | True | False => byComputing

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

theorem Float.Theory.ifTrue ∀ (c: Bool) (x y: Nat) (h: c = True): (if c then x else y) = x := rewrite h

theorem Float.Theory.ifFalse ∀ (c: Bool) (x y: Nat) (h: c = False): (if c then x else y) = y := rewrite h

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
  rewrite en, ez

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
        (rewrite c: Float.Model.magnitude a = a - 9223372036854775808),
        Nat.equalFalse (Float.Model.magnitude a) 9218868437227405312 ia
      ]
    | Inr c =>
      arithmetic [
        Float.lowBound a v na c,
        c,
        (rewrite c: Float.Model.magnitude a = a),
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
      rewrite ab
    | Inr e =>
      Eq.trans
        (rewrite ib, e: Float.Theory.addInf a b = 9221120237041090560)
        (Eq.flipped (rewrite ia, Eq.trans (Nat.equalComm b a) e: Float.Theory.addInf b a = 9221120237041090560))

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
          calc Float.Theory.addRest a b
            _ = Float.Theory.addInf a b := Float.Theory.addRestInfA a b ia
            _ = Float.Theory.addInf b a := Float.Theory.addInfComm a b ia ib
            _ = Float.Theory.addRest b a := (Float.Theory.addRestInfA b a ib).flipped)
        (ib =>
          calc Float.Theory.addRest a b
            _ = Float.Theory.addInf a b := Float.Theory.addRestInfA a b ia
            _ = a := (rewrite ib: Float.Theory.addInf a b = a)
            _ = Float.Theory.addRest b a := Eq.flipped (Float.Theory.addRestInfB b a ib ia)))
    (ia =>
      Float.Theory.orCase
        (Float.Theory.boolCases (Float.Model.isInfinite b))
        (ib =>
          calc Float.Theory.addRest a b
            _ = b := Float.Theory.addRestInfB a b ia ib
            _ = Float.Theory.addInf b a := Eq.flipped (rewrite ia: Float.Theory.addInf b a = b)
            _ = Float.Theory.addRest b a := (Float.Theory.addRestInfA b a ib).flipped)
        (ib =>
          calc Float.Theory.addRest a b
            _ = Float.Theory.addFin a b := Float.Theory.addRestFin a b ia ib
            _ = Float.Theory.addFin b a := Float.Theory.addFinComm a b
            _ = Float.Theory.addRest b a := Eq.flipped (Float.Theory.addRestFin b a ib ia)))

theorem Float.Theory.addBitsComm ∀ (a b: Nat): Float.Model.addBits a b = Float.Model.addBits b a :=
  Float.Theory.orCase
    (Float.Theory.boolCases (Float.Model.isNaN a ∨ Float.Model.isNaN b))
    (n =>
      Eq.trans
        (Float.Theory.addBitsNaN a b n)
        (Eq.flipped
          (Float.Theory.addBitsNaN b a (Eq.trans (Bool.orComm (Float.Model.isNaN b) (Float.Model.isNaN a)) n))))
    (n =>
      calc Float.Model.addBits a b
        _ = Float.Theory.addRest a b := Float.Theory.addBitsRest a b n
        _ = Float.Theory.addRest b a := Float.Theory.addRestComm a b
        _ = Float.Model.addBits b a :=
          Eq.flipped
            (Float.Theory.addBitsRest b a (Eq.trans (Bool.orComm (Float.Model.isNaN b) (Float.Model.isNaN a)) n)))

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

theorem Float.Theory.keyRefl ∀ (x: Int): Int.leq x x = True := match x with | OfNat n | NegSucc n => Nat.leRefl n

theorem Float.Theory.keySet ∀ (a: Nat)
    (c: Nat.leq 9223372036854775808 a = True):
    Float.Theory.key a = NegSucc (a - 9223372036854775808) :=
  rewrite c

theorem Float.Theory.keyClear ∀ (a: Nat) (c: Nat.leq 9223372036854775808 a = False): Float.Theory.key a = OfNat a :=
  rewrite c

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
        (arithmetic [fin, (rewrite c: Float.Model.magnitude a = a)]: Nat.leq a 9218868437227405312 = True))

--| The keys of the two zeros' patterns are at most `0.0`'s.
theorem Float.Theory.zeroLeZeroBits ∀ (a: Nat)
    (h: (a = 0) ∨ (a = 9223372036854775808)):
    Int.leq (Float.Theory.key a) (OfNat 0) = True :=
  match h with | Inl e | Inr e => J (y w => Int.leq (Float.Theory.key y) (OfNat 0) = True) byComputing e.flipped

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
  match h with | Inl e | Inr e => J (y w => Float.Model.units y = OfNat 0) byComputing e.flipped

--| The zero sign matters only for a zero
--| numerator.
theorem Float.Theory.roundRatioSignIrrelevant ∀ (den: Nat) (scale: Int) (z1 z2: Bool) (num: Int)
    (ne: num ≠ OfNat 0):
    Float.Model.roundRatio num den scale z1 = Float.Model.roundRatio num den scale z2 :=
  match num with
    | OfNat Zero => (ne byComputing).impossible
    | OfNat (Succ _) | NegSucc _ => byComputing

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
  let ub: Float.Model.units b = OfNat (Float.Theory.magUnits b) := rewrite sb
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
    (n => Eq.trans (Float.Theory.addBitsNaN a 9223372036854775808 (rewrite n)) n.read.flipped)
    (n =>
      Eq.trans
        (Float.Theory.addBitsRest a 9223372036854775808
          (Float.Theory.orFalse (Float.Model.isNaN a) False n byComputing))
        (Float.Theory.orCase
          (Float.Theory.boolCases (Float.Model.isInfinite a))
          (ia => Eq.trans (Float.Theory.addRestInfA a 9223372036854775808 ia) byComputing)
          (ia =>
            calc Float.Theory.addRest a 9223372036854775808
              _ = Float.Theory.addFin a 9223372036854775808 :=
                Float.Theory.addRestFin a 9223372036854775808 ia byComputing
              _ = Float.Theory.finWith (Float.Model.units a) (Float.Model.signBit a) :=
                Float.Theory.finWithCong
                  (Int.add (Float.Model.units a) (OfNat 0))
                  (Float.Model.units a)
                  (Float.Model.signBit a ∧ True)
                  (Float.Model.signBit a)
                  (Int.addZero (Float.Model.units a))
                  (Float.Theory.andTrueRight (Float.Model.signBit a))
              _ = a := Float.Theory.roundRatioUnitsBits a (Float.Theory.finiteOf a va n ia))))

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
    | Inl e | Inr e => J (y w => (Nat.equal y 0 ∨ Nat.equal y 9223372036854775808) = True) byComputing e.flipped

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
    let u: Float.Theory.units x = OfNat (Float.Theory.magUnits x.bits) := rewrite c
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

-- Multiplication and the conversions

--| Two roundings of the same value give the same pattern.
theorem Float.Theory.roundsToUnique ∀ (t d r1 r2: Nat)
    (pd: 0 < d)
    (h1: Float.Theory.RoundsTo t d r1)
    (h2: Float.Theory.RoundsTo t d r2):
    r1 = r2 :=
  arithmetic [
    Float.Theory.roundsToMono t t d r1 r2 pd h1 h2 (Nat.leRefl t),
    Float.Theory.roundsToMono t t d r2 r1 pd h2 h1 (Nat.leRefl t)
  ]

--| Equal values round to the same magnitude, however they are written.
theorem Float.Theory.magnitudeCross ∀ (n1 d1 n2 d2: Nat) (s1 s2: Int)
    (pn1: 0 < n1)
    (pd1: 0 < d1)
    (pn2: 0 < n2)
    (pd2: 0 < d2)
    (e: Float.Model.scaleUp n1 s1 * Float.Model.scaleDown d2 s2
      = Float.Model.scaleUp n2 s2 * Float.Model.scaleDown d1 s1):
    Float.Model.roundMagnitude False n1 d1 s1 = Float.Model.roundMagnitude False n2 d2 s2 :=
  Float.Theory.roundsToUnique
    (Float.Model.scaleUp n2 s2)
    (Float.Model.scaleDown d2 s2)
    (Float.Model.roundMagnitude False n1 d1 s1)
    (Float.Model.roundMagnitude False n2 d2 s2)
    (Float.Theory.scaleDownPos d2 s2 pd2)
    (Float.Theory.roundsToScale
      (Float.Model.scaleUp n1 s1)
      (Float.Model.scaleDown d1 s1)
      (Float.Model.scaleUp n2 s2)
      (Float.Model.scaleDown d2 s2)
      (Float.Model.roundMagnitude False n1 d1 s1)
      (Float.Theory.scaleDownPos d1 s1 pd1)
      (Float.Theory.scaleDownPos d2 s2 pd2)
      e
      (Float.Theory.roundMagnitudeSpec n1 d1 s1 pn1 pd1))
    (Float.Theory.roundMagnitudeSpec n2 d2 s2 pn2 pd2)

--| Equal nonzero values of the same sign round to the same double.
theorem Float.Theory.roundRatioCross ∀ (sb: Bool) (n1 n2: Nat) (s1 s2: Int) (z1 z2: Bool)
    (pn1: 0 < n1)
    (pn2: 0 < n2)
    (e: Float.Model.scaleUp n1 (Int.add s1 (OfNat 1074)) * Float.Model.scaleDown 1 (Int.add s2 (OfNat 1074))
      = Float.Model.scaleUp n2 (Int.add s2 (OfNat 1074)) * Float.Model.scaleDown 1 (Int.add s1 (OfNat 1074))):
    Float.Model.roundRatio (Int.signed sb n1) 1 s1 z1 = Float.Model.roundRatio (Int.signed sb n2) 1 s2 z2 :=
  let m: Float.Model.roundMagnitude False n1 1 (Int.add s1 (OfNat 1074))
    = Float.Model.roundMagnitude False n2 1 (Int.add s2 (OfNat 1074)) :=
    Float.Theory.magnitudeCross n1 1 n2 1
      (Int.add s1 (OfNat 1074))
      (Int.add s2 (OfNat 1074))
      pn1
      byComputing
      pn2
      byComputing
      e
  match sb with
    | False =>
      calc Float.Model.roundRatio (OfNat n1) 1 s1 z1
        _ = Float.Model.roundMagnitude False n1 1 (Int.add s1 (OfNat 1074)) :=
          Float.Theory.roundRatioOfPos 1 s1 z1 n1 pn1
        _ = Float.Model.roundMagnitude False n2 1 (Int.add s2 (OfNat 1074)) := m
        _ = Float.Model.roundRatio (OfNat n2) 1 s2 z2 := (Float.Theory.roundRatioOfPos 1 s2 z2 n2 pn2).flipped
    | True =>
      calc Float.Model.roundRatio (Int.neg (OfNat n1)) 1 s1 z1
        _ = Float.Model.roundMagnitude False n1 1 (Int.add s1 (OfNat 1074)) + 9223372036854775808 :=
          Float.Theory.roundRatioOfNeg 1 s1 z1 n1 pn1
        _ = Float.Model.roundMagnitude False n2 1 (Int.add s2 (OfNat 1074)) + 9223372036854775808 :=
          Eq.cong (x => x + 9223372036854775808) m
        _ = Float.Model.roundRatio (Int.neg (OfNat n2)) 1 s2 z2 := (Float.Theory.roundRatioOfNeg 1 s2 z2 n2 pn2).flipped

theorem Float.Theory.mulPos ∀ (k p: Nat) (pk: 0 < k) (pp: 0 < p): 0 < k * p := arithmetic [pk, Nat.leMulPos k p pp]

--| `k × 2^1074` units of 2^-2148 are `k` units of 2^-1074.
theorem Float.Theory.roundRatioShift ∀ (sb: Bool) (k: Nat) (z: Bool):
    Float.Model.roundRatio (Int.signed sb (k * Float.Model.pow2 1074)) 1 (-2148) z
      = Float.Model.roundRatio (Int.signed sb k) 1 (-1074) z :=
  Float.Theory.orCase
    (Float.Theory.zeroOrPos k)
    (k0 =>
      rewrite k0 then
        match sb with
          | False => byComputing
          | True => byComputing)
    (pk =>
      Float.Theory.roundRatioCross sb
        (k * Float.Model.pow2 1074)
        k
        (-2148)
        (-1074)
        z
        z
        (Float.Theory.mulPos k (Float.Model.pow2 1074) pk byComputing)
        pk
        (Eq.trans
          (Nat.mulOne (k * Float.Model.pow2 1074))
          (Eq.cong (t => t * Float.Model.pow2 1074) (Nat.mulOne k)).flipped))

--| `mulBits` with neither argument the NaN nor infinite: the units' product, rounded.
theorem Float.Theory.mulFiniteBits ∀ (a b: Nat)
    (na: Float.Model.isNaN a = False)
    (nb: Float.Model.isNaN b = False)
    (ia: Float.Model.isInfinite a = False)
    (ib: Float.Model.isInfinite b = False):
    Float.Model.mulBits a b
      = Float.Model.roundRatio
        (Int.mul (Float.Model.units a) (Float.Model.units b))
        1
        (-2148)
        (Bool.xor (Float.Model.signBit a) (Float.Model.signBit b)) :=
  let fin: Nat :=
    Float.Model.roundScaled
      (Int.mul (Float.Model.units a) (Float.Model.units b))
      (-2148)
      (Bool.xor (Float.Model.signBit a) (Float.Model.signBit b))
  let inf: Nat :=
    if Float.Model.isZero a ∨ Float.Model.isZero b then 9221120237041090560
    else Float.Model.infinityBits (Bool.xor (Float.Model.signBit a) (Float.Model.signBit b))
  Eq.trans
    (Float.Theory.ifFalse
      (Float.Model.isNaN a ∨ Float.Model.isNaN b)
      9221120237041090560
      (if Float.Model.isInfinite a ∨ Float.Model.isInfinite b then inf else fin)
      (Float.Theory.orFalse (Float.Model.isNaN a) (Float.Model.isNaN b) na nb))
    (Float.Theory.ifFalse
      (Float.Model.isInfinite a ∨ Float.Model.isInfinite b)
      inf
      fin
      (Float.Theory.orFalse (Float.Model.isInfinite a) (Float.Model.isInfinite b) ia ib))

--| An infinite pattern is the infinity of its sign.
theorem Float.Theory.infinityOfBits ∀ (a: Nat)
    (ia: Float.Model.isInfinite a = True):
    Float.Model.infinityBits (Float.Model.signBit a) = a :=
  let mag: Float.Model.magnitude a = 9218868437227405312 :=
    Nat.equalSound (Float.Model.magnitude a) 9218868437227405312 ia
  match c: Nat.leq 9223372036854775808 a with
    | True => arithmetic [c, mag, (rewrite c: Float.Model.magnitude a = a - 9223372036854775808)]
    | False => arithmetic [c, mag, (rewrite c: Float.Model.magnitude a = a)]

--| Multiplying a valid pattern by 1.0's gives it back.
theorem Float.Theory.mulOneBits ∀ (a: Nat)
    (va: Float.isValid a = True):
    Float.Model.mulBits a 4607182418800017408 = a :=
  Float.Theory.orCase
    (Float.Theory.boolCases (Float.Model.isNaN a))
    (n =>
      Eq.trans
        (Float.Theory.ifTrue
          (Float.Model.isNaN a ∨ Float.Model.isNaN 4607182418800017408)
          9221120237041090560
          (if Float.Model.isInfinite a ∨ Float.Model.isInfinite 4607182418800017408 then
             (if Float.Model.isZero a ∨ Float.Model.isZero 4607182418800017408 then 9221120237041090560
              else Float.Model.infinityBits (Bool.xor (Float.Model.signBit a) False))
           else
             Float.Model.roundScaled
               (Int.mul (Float.Model.units a) (Float.Model.units 4607182418800017408))
               (-2148)
               (Bool.xor (Float.Model.signBit a) False))
          (rewrite n))
        n.read.flipped)
    (n =>
      Float.Theory.orCase
        (Float.Theory.boolCases (Float.Model.isInfinite a))
        (ia =>
          let mag: Float.Model.magnitude a = 9218868437227405312 :=
            Nat.equalSound (Float.Model.magnitude a) 9218868437227405312 ia
          let rest: Nat :=
            if Float.Model.isInfinite a ∨ Float.Model.isInfinite 4607182418800017408 then
              (if Float.Model.isZero a ∨ Float.Model.isZero 4607182418800017408 then 9221120237041090560
               else Float.Model.infinityBits (Bool.xor (Float.Model.signBit a) False))
            else
              Float.Model.roundScaled
                (Int.mul (Float.Model.units a) (Float.Model.units 4607182418800017408))
                (-2148)
                (Bool.xor (Float.Model.signBit a) False)
          let special: Nat :=
            if Float.Model.isZero a ∨ Float.Model.isZero 4607182418800017408 then 9221120237041090560
            else Float.Model.infinityBits (Bool.xor (Float.Model.signBit a) False)
          calc Float.Model.mulBits a 4607182418800017408
            _ = rest :=
              Float.Theory.ifFalse
                (Float.Model.isNaN a ∨ Float.Model.isNaN 4607182418800017408)
                9221120237041090560
                rest
                (Float.Theory.orFalse (Float.Model.isNaN a) False n byComputing)
            _ = special :=
              Float.Theory.ifTrue
                (Float.Model.isInfinite a ∨ Float.Model.isInfinite 4607182418800017408)
                special
                (Float.Model.roundScaled
                  (Int.mul (Float.Model.units a) (Float.Model.units 4607182418800017408))
                  (-2148)
                  (Bool.xor (Float.Model.signBit a) False))
                (rewrite ia)
            _ = Float.Model.infinityBits (Bool.xor (Float.Model.signBit a) False) :=
              Float.Theory.ifFalse
                (Float.Model.isZero a ∨ Float.Model.isZero 4607182418800017408)
                9221120237041090560
                (Float.Model.infinityBits (Bool.xor (Float.Model.signBit a) False))
                (rewrite mag)
            _ = Float.Model.infinityBits (Float.Model.signBit a) :=
              Eq.cong Float.Model.infinityBits (Float.Theory.xorFalse (Float.Model.signBit a))
            _ = a := Float.Theory.infinityOfBits a ia)
        (ia =>
          let sb: Bool := Float.Model.signBit a
          let k: Nat := Float.Theory.magUnits (Float.Model.magnitude a)
          calc Float.Model.mulBits a 4607182418800017408
            _ = Float.Model.roundRatio
                (Int.mul (Float.Model.units a) (Float.Model.units 4607182418800017408))
                1
                (-2148)
                (Bool.xor sb False) := Float.Theory.mulFiniteBits a 4607182418800017408 n byComputing ia byComputing
            _ = Float.Model.roundRatio
                (Int.signed (Bool.xor sb False) (k * Float.Model.pow2 1074))
                1
                (-2148)
                (Bool.xor sb False) :=
              Eq.cong
                (t => Float.Model.roundRatio t 1 (-2148) (Bool.xor sb False))
                (Int.signedMulLeft sb k (OfNat (Float.Model.pow2 1074)))
            _ = Float.Model.roundRatio (Int.signed sb (k * Float.Model.pow2 1074)) 1 (-2148) sb :=
              Eq.cong
                (s => Float.Model.roundRatio (Int.signed s (k * Float.Model.pow2 1074)) 1 (-2148) s)
                (Float.Theory.xorFalse sb)
            _ = Float.Model.roundRatio (Int.signed sb k) 1 (-1074) sb := Float.Theory.roundRatioShift sb k sb
            _ = a := Float.Theory.roundRatioUnitsBits a (Float.Theory.finiteOf a va n ia)))

--| `x * 1.0` is `x`, zeros, infinities and the NaN included.
theorem Float.mulOneRight ∀ (x: Float): x * 1.0 = x := match x with
  | { bits = a, valid = p } =>
    Float.bitsExt
      (Float.ofBits (Float.Model.mulBits a 4607182418800017408))
      { bits = a, valid = p }
      (Eq.trans
        (Float.Theory.ofBitsBits
          (Float.Model.mulBits a 4607182418800017408)
          (Float.Theory.validTo (Float.Model.mulBits a 4607182418800017408) a (Float.Theory.mulOneBits a p) p))
        (Float.Theory.mulOneBits a p))

test "Float.mulOneRight" :=
  0.1 * 1.0 == 0.1
    ∧ (-0.0) * 1.0 == -0.0
    ∧ 0.0 * 1.0 == 0.0
    ∧ 5e-324 * 1.0 == 5e-324
    ∧ (-1.7976931348623157e308) * 1.0 == -1.7976931348623157e308
    ∧ Float.infinity * 1.0 == Float.infinity
    ∧ (-Float.infinity) * 1.0 == -Float.infinity
    ∧ (Float.nan * 1.0).bits == Float.nan.bits

--| `ofNat n` is `ofInt n`.
theorem Float.ofNatOfInt ∀ (n: Nat): Float.ofNat n = Float.ofInt (OfNat n) := byComputing

--| A larger integer never converts to a smaller double.
theorem Float.ofIntMonotone ∀ (i j: Int) (h: Int.leq i j = True): Float.ofInt i <= Float.ofInt j :=
  match lt: Int.less i j with
    | True => Float.Theory.roundRatioStrictMono 1 (OfNat 0) False False byComputing i j lt
    | False =>
      let e: i = j := arithmetic [h, lt]
      rewrite e then Float.Theory.keyRefl (Float.orderKey (Float.ofInt j))

test "Float.ofIntMonotone" :=
  Float.ofInt (-9007199254740995) <= Float.ofInt (-9007199254740994)
    ∧ Float.ofInt 9007199254740992 <= Float.ofInt 9007199254740993
    ∧ Float.ofInt 0 <= Float.ofInt 1
    ∧ Float.ofNat (Nat.pow 2 1024 - Nat.pow 2 970 - 1) <= Float.ofNat (Nat.pow 2 1024)

-- Whole numbers up to 2^53 are doubles

--| How far a whole number's significand is shifted up: `53 - bitLength n`.
def Float.Theory.wholeShift (n: Nat): Nat := 53 - Float.Model.bitLength n

--| The pattern of the whole number `n`, for `0 < n ≤ 2^53`: the significand
--| `n × 2^j`, at exponent field `1075 - j`, for `j` its `wholeShift`.
def Float.Theory.wholeBits (n: Nat): Nat :=
  (1074 - Float.Theory.wholeShift n) * 4503599627370496 + n * Nat.pow 2 (Float.Theory.wholeShift n)

theorem Float.Theory.wholeSignificand ∀ (n: Nat)
    (pn: 0 < n)
    (h: n ≤ 9007199254740992):
    (4503599627370496 ≤ n * Nat.pow 2 (Float.Theory.wholeShift n))
      ∧ (n * Nat.pow 2 (Float.Theory.wholeShift n) ≤ 9007199254740992) :=
  let b: Nat := Float.Model.bitLength n
  let bs: Float.Theory.IsBitLength n b := Float.Theory.bitLengthSpec n pn
  let j: Nat := 53 - b
  match c: Nat.leq b 53 with
    | True =>
      let total: Nat.pow 2 b * Nat.pow 2 j = 9007199254740992 :=
        Eq.trans (Nat.powAdd 2 b j).flipped (Eq.cong (Nat.pow 2) (arithmetic [c]: b + j = 53))
      let upper: n * Nat.pow 2 j < Nat.pow 2 b * Nat.pow 2 j :=
        Float.Theory.mulLtRight n (Nat.pow 2 b) (Nat.pow 2 j) bs.left (Nat.powSuccPos 1 j)
      let lower: Nat.pow 2 b * Nat.pow 2 j ≤ (n + n) * Nat.pow 2 j :=
        Nat.leMulRight (Nat.pow 2 b) (n + n) (Nat.pow 2 j) bs.right
      let double: (n + n) * Nat.pow 2 j = n * Nat.pow 2 j + n * Nat.pow 2 j := algebra
      Both (arithmetic [total, upper, lower, double]) (arithmetic [total, upper])
    | False =>
      let big: Nat.pow 2 54 ≤ Nat.pow 2 b := Nat.powMono 1 54 b (arithmetic [c])
      let top: n = 9007199254740992 := arithmetic [big, bs.right, h]
      let j0: j = 0 := arithmetic [c]
      rewrite j0, top then Both byComputing byComputing

--| The units of a whole number's pattern: `n × 2^1074`.
theorem Float.Theory.wholeUnits ∀ (n: Nat)
    (pn: 0 < n)
    (h: n ≤ 9007199254740992):
    Float.Theory.magUnits (Float.Theory.wholeBits n) = n * Nat.pow 2 1074 :=
  let j: Nat := Float.Theory.wholeShift n
  let sig: (4503599627370496 ≤ n * Nat.pow 2 j) ∧ (n * Nat.pow 2 j ≤ 9007199254740992) :=
    Float.Theory.wholeSignificand n pn h
  calc Float.Theory.magUnits ((1074 - j) * 4503599627370496 + n * Nat.pow 2 j)
    _ = Nat.pow 2 (1074 - j) * (n * Nat.pow 2 j) :=
      Float.Theory.magUnitsGrid (1074 - j) (n * Nat.pow 2 j) sig.right (Inr sig.left)
    _ = n * (Nat.pow 2 (1074 - j) * Nat.pow 2 j) := algebra
    _ = n * Nat.pow 2 (1074 - j + j) := Eq.cong (t => n * t) (Nat.powAdd 2 (1074 - j) j).flipped
    _ = n * Nat.pow 2 1074 := Eq.cong (t => n * Nat.pow 2 t) (arithmetic: 1074 - j + j = 1074)

theorem Float.Theory.wholeFinite ∀ (n: Nat)
    (pn: 0 < n)
    (h: n ≤ 9007199254740992):
    Float.Theory.wholeBits n < 9218868437227405312 :=
  arithmetic [(Float.Theory.wholeSignificand n pn h).right]

--| A whole number up to 2^53 converts exactly: to its own pattern.
theorem Float.Theory.ofIntBitsWhole ∀ (n: Nat)
    (pn: 0 < n)
    (h: n ≤ 9007199254740992):
    Float.Model.ofIntBits (OfNat n) = Float.Theory.wholeBits n :=
  let m: Nat := Float.Theory.wholeBits n
  let r: Nat := Float.Model.roundMagnitude False n 1 (OfNat 1074)
  let units: Float.Theory.magUnits m = n * Nat.pow 2 1074 := Float.Theory.wholeUnits n pn h
  let spec: Float.Theory.RoundsTo (n * Nat.pow 2 1074) 1 r :=
    Float.Theory.roundMagnitudeSpec n 1 (OfNat 1074) pn byComputing
  calc Float.Model.ofIntBits (OfNat n)
    _ = r := Float.Theory.roundRatioOfPos 1 (OfNat 0) False n pn
    _ = m :=
      Float.Theory.roundsToExact m r
        (Float.Theory.wholeFinite n pn h)
        (Float.Theory.roundsToScale
          (n * Nat.pow 2 1074)
          1
          (Float.Theory.magUnits m * 1)
          1
          r
          byComputing
          byComputing
          (calc n * Nat.pow 2 1074 * 1
            _ = n * Nat.pow 2 1074 := Nat.mulOne (n * Nat.pow 2 1074)
            _ = Float.Theory.magUnits m := units.flipped
            _ = Float.Theory.magUnits m * 1 * 1 := (algebra: Float.Theory.magUnits m = Float.Theory.magUnits m * 1 * 1))
          spec)

theorem Float.Theory.wholeSignClear ∀ (n: Nat)
    (pn: 0 < n)
    (h: n ≤ 9007199254740992):
    Nat.leq 9223372036854775808 (Float.Theory.wholeBits n) = False :=
  match c: Nat.leq 9223372036854775808 (Float.Theory.wholeBits n) with
    | True => Void.impossible (arithmetic [c, Float.Theory.wholeFinite n pn h])
    | False => byComputing

--| The conversion of a whole number up to 2^53: finite, positive or `+0.0`,
--| and exactly `n` in units.
theorem Float.Theory.ofIntBitsSmall ∀ (n: Nat)
    (h: n ≤ 9007199254740992):
    (Float.Theory.FiniteBits (Float.Model.ofIntBits (OfNat n))
      ∧ (Float.Model.signBit (Float.Model.ofIntBits (OfNat n)) = False))
      ∧ (Float.Model.units (Float.Model.ofIntBits (OfNat n)) = OfNat (n * Nat.pow 2 1074)) :=
  Float.Theory.orCase
    (Float.Theory.zeroOrPos n)
    (n0 =>
      let fin: Float.Theory.FiniteBits (Float.Model.ofIntBits (OfNat 0)) := byComputing
      let sign: (Float.Theory.FiniteBits (Float.Model.ofIntBits (OfNat 0))
        ∧ (Float.Model.signBit (Float.Model.ofIntBits (OfNat 0)) = False)) :=
        Both fin byComputing
      J
        (y w =>
          (Float.Theory.FiniteBits (Float.Model.ofIntBits (OfNat y))
            ∧ (Float.Model.signBit (Float.Model.ofIntBits (OfNat y)) = False))
            ∧ (Float.Model.units (Float.Model.ofIntBits (OfNat y)) = OfNat (y * Nat.pow 2 1074)))
        (Both sign byComputing)
        n0.flipped)
    (pn =>
      let c: Nat.leq 9223372036854775808 (Float.Theory.wholeBits n) = False := Float.Theory.wholeSignClear n pn h
      let mag: Float.Model.magnitude (Float.Theory.wholeBits n) = Float.Theory.wholeBits n := rewrite c
      rewrite Float.Theory.ofIntBitsWhole n pn h then
        Both
          (Both (arithmetic [mag, Float.Theory.wholeFinite n pn h]) c)
          (calc Float.Model.units (Float.Theory.wholeBits n)
            _ = Int.signed False (Float.Theory.magUnits (Float.Theory.wholeBits n)) := rewrite c
            _ = OfNat (n * Nat.pow 2 1074) := Eq.cong OfNat (Float.Theory.wholeUnits n pn h)))

--| `ofNat n` has `n × 2^1074` units, so is exactly `n`, for every `n` up to
--| 2^53.
theorem Float.ofNatExact ∀ (n: Nat)
    (h: n ≤ 9007199254740992):
    Float.Theory.units (Float.ofNat n) = OfNat (n * Nat.pow 2 1074) :=
  rewrite Float.Theory.ofBitsBits
        (Float.Model.ofIntBits (OfNat n))
        (Float.Theory.roundRatioValid 1 (OfNat 0) False byComputing (OfNat n)) then
    (Float.Theory.ofIntBitsSmall n h).right

test "Float.ofNatExact" :=
  Float.Theory.units (Float.ofNat 0) == OfNat 0
    ∧ Float.Theory.units (Float.ofNat 3) == OfNat (3 * Nat.pow 2 1074)
    ∧ Float.Theory.units (Float.ofNat 9007199254740992) == OfNat (9007199254740992 * Nat.pow 2 1074)
    ∧ ¬(Float.Theory.units (Float.ofNat 9007199254740993) == OfNat (9007199254740993 * Nat.pow 2 1074))

--| `x * y` on any two doubles, known or not: their bits' product.
theorem Float.Theory.mulOfBits ∀ (x y: Float): x * y = Float.ofBits (Float.Model.mulBits x.bits y.bits) :=
  match x, y with | { bits = a, valid = p }, { bits = b, valid = q } => byComputing

theorem Float.Theory.pairEq ∀ (i j: Int) (x y: Bool) (e: i = j) (f: x = y): (i, x) = (j, y) := rewrite e, f

theorem Float.Theory.wholeProduct ∀ (a b p: Nat): a * p * (b * p) * 1 = a * b * p * p := algebra

--| The product of two whole doubles' units is the product of the numbers, scaled.
theorem Float.Theory.mulWholeCross ∀ (a b: Nat):
    Float.Model.roundRatio (OfNat (a * Nat.pow 2 1074 * (b * Nat.pow 2 1074))) 1 (-2148) False
      = Float.Model.roundRatio (OfNat (a * b)) 1 0 False :=
  Float.Theory.orCase (Float.Theory.zeroOrPos a) (a0 => rewrite a0) (pa =>
    Float.Theory.orCase
      (Float.Theory.zeroOrPos b)
      (b0 =>
        rewrite b0 then
          calc Float.Model.roundRatio (OfNat (a * Nat.pow 2 1074 * 0)) 1 (-2148) False
            _ = Float.Model.roundRatio (OfNat 0) 1 (-2148) False :=
              Eq.cong (t => Float.Model.roundRatio (OfNat t) 1 (-2148) False) (Nat.mulZero (a * Nat.pow 2 1074))
            _ = Float.Model.roundRatio (OfNat 0) 1 0 False := byComputing
            _ = Float.Model.roundRatio (OfNat (a * 0)) 1 0 False :=
              Eq.cong (t => Float.Model.roundRatio (OfNat t) 1 0 False) (Nat.mulZero a).flipped)
      (pb =>
        Float.Theory.roundRatioCross False
          (a * Nat.pow 2 1074 * (b * Nat.pow 2 1074))
          (a * b)
          (-2148)
          0
          False
          False
          (Float.Theory.mulPos
            (a * Nat.pow 2 1074)
            (b * Nat.pow 2 1074)
            (Float.Theory.mulPos a (Nat.pow 2 1074) pa byComputing)
            (Float.Theory.mulPos b (Nat.pow 2 1074) pb byComputing))
          (Float.Theory.mulPos a b pa pb)
          (Float.Theory.wholeProduct a b (Nat.pow 2 1074))))

--| Whole numbers up to 2^53 multiply as numbers, then round once: `ofNat a *
--| ofNat b` is `ofNat (a * b)`, so `ofNat a * 10.0` is `ofNat (a * 10)`.
theorem Float.ofNatMul ∀ (a b: Nat)
    (ha: a ≤ 9007199254740992)
    (hb: b ≤ 9007199254740992):
    Float.ofNat a * Float.ofNat b = Float.ofNat (a * b) :=
  let ba: Nat := Float.Model.ofIntBits (OfNat a)
  let bb: Nat := Float.Model.ofIntBits (OfNat b)
  let sa: (Float.Theory.FiniteBits ba ∧ (Float.Model.signBit ba = False))
    ∧ (Float.Model.units ba = OfNat (a * Nat.pow 2 1074)) :=
    Float.Theory.ofIntBitsSmall a ha
  let sb: (Float.Theory.FiniteBits bb ∧ (Float.Model.signBit bb = False))
    ∧ (Float.Model.units bb = OfNat (b * Nat.pow 2 1074)) :=
    Float.Theory.ofIntBitsSmall b hb
  calc Float.ofNat a * Float.ofNat b
    _ = Float.ofBits (Float.Model.mulBits (Float.ofNat a).bits (Float.ofNat b).bits) :=
      Float.Theory.mulOfBits (Float.ofNat a) (Float.ofNat b)
    _ = Float.ofBits (Float.Model.mulBits ba (Float.ofNat b).bits) :=
      Eq.cong
        (t => Float.ofBits (Float.Model.mulBits t (Float.ofNat b).bits))
        (Float.Theory.ofBitsBits ba (Float.Theory.roundRatioValid 1 (OfNat 0) False byComputing (OfNat a)))
    _ = Float.ofBits (Float.Model.mulBits ba bb) :=
      Eq.cong
        (t => Float.ofBits (Float.Model.mulBits ba t))
        (Float.Theory.ofBitsBits bb (Float.Theory.roundRatioValid 1 (OfNat 0) False byComputing (OfNat b)))
    _ = Float.ofBits
        (Float.Model.roundRatio
          (Int.mul (Float.Model.units ba) (Float.Model.units bb))
          1
          (-2148)
          (Bool.xor (Float.Model.signBit ba) (Float.Model.signBit bb))) :=
      Eq.cong Float.ofBits
        (Float.Theory.mulFiniteBits ba bb
          (Float.Theory.finiteNotNaN ba sa.left.left)
          (Float.Theory.finiteNotNaN bb sb.left.left)
          (Float.Theory.finiteNotInfinite ba sa.left.left)
          (Float.Theory.finiteNotInfinite bb sb.left.left))
    _ = Float.ofBits
        (Float.Model.roundRatio
          (Int.mul (OfNat (a * Nat.pow 2 1074)) (Float.Model.units bb))
          1
          (-2148)
          (Bool.xor False (Float.Model.signBit bb))) :=
      Eq.cong
        (t =>
          Float.ofBits
            (Float.Model.roundRatio
              (Int.mul t.fst (Float.Model.units bb))
              1
              (-2148)
              (Bool.xor t.snd (Float.Model.signBit bb))))
        (Float.Theory.pairEq
          (Float.Model.units ba)
          (OfNat (a * Nat.pow 2 1074))
          (Float.Model.signBit ba)
          False
          sa.right
          sa.left.right)
    _ = Float.ofBits (Float.Model.roundRatio (OfNat (a * Nat.pow 2 1074 * (b * Nat.pow 2 1074))) 1 (-2148) False) :=
      Eq.cong
        (t =>
          Float.ofBits
            (Float.Model.roundRatio (Int.mul (OfNat (a * Nat.pow 2 1074)) t.fst) 1 (-2148) (Bool.xor False t.snd)))
        (Float.Theory.pairEq
          (Float.Model.units bb)
          (OfNat (b * Nat.pow 2 1074))
          (Float.Model.signBit bb)
          False
          sb.right
          sb.left.right)
    _ = Float.ofNat (a * b) := Eq.cong Float.ofBits (Float.Theory.mulWholeCross a b)

test "Float.ofNatMul" :=
  Float.ofNat 3 * Float.ofNat 7 == Float.ofNat 21
    ∧ Float.ofNat 0 * Float.ofNat 5 == 0.0
    ∧ Float.ofNat 123456789 * 10.0 == Float.ofNat 1234567890
    ∧ Float.ofNat 9007199254740991 * 10.0 == Float.ofNat 90071992547409910
    ∧ Float.ofNat 9007199254740992 * Float.ofNat 9007199254740992 == Float.ofNat (Nat.pow 2 106)

-- Division and the conversions' order

--| A larger number never converts to a smaller double.
theorem Float.ofNatMonotone ∀ (m n: Nat) (h: m ≤ n): Float.ofNat m <= Float.ofNat n :=
  Float.ofIntMonotone (OfNat m) (OfNat n) (arithmetic [h])

--| A whole number up to 2^53 converts to a finite double.
theorem Float.ofNatFinite ∀ (n: Nat) (h: n ≤ 9007199254740992): Float.isFinite (Float.ofNat n) = True :=
  let fin: Float.Theory.FiniteBits (Float.Model.ofIntBits (OfNat n)) := (Float.Theory.ofIntBitsSmall n h).left.left
  rewrite Float.Theory.ofBitsBits
        (Float.Model.ofIntBits (OfNat n))
        (Float.Theory.roundRatioValid 1 (OfNat 0) False byComputing (OfNat n)) then
    (arithmetic [fin]: ¬(Nat.leq 9218868437227405312 (Float.clearSignBits (Float.Model.ofIntBits (OfNat n)))) = True)

test "Float.ofNatMonotone" :=
  Float.ofNat 0 <= Float.ofNat 1
    ∧ Float.ofNat 9007199254740992 <= Float.ofNat 9007199254740993
    ∧ Float.ofNat 4294967295 <= Float.ofNat 4294967296

test "Float.ofNatFinite" := Float.isFinite (Float.ofNat 9007199254740992) ∧ Float.isFinite (Float.ofNat 0)

--| Zero numerators' keys are ordered by their signs.
theorem Float.Theory.zeroKeyLe ∀ (den: Nat) (scale: Int) (z1 z2: Bool)
    (zs: z1 = False → z2 = False):
    Int.leq (Float.Theory.roundKey (OfNat 0) den scale z1) (Float.Theory.roundKey (OfNat 0) den scale z2) = True :=
  match z1, z2 with
    | True, True | False => byComputing
    | False, True => Void.impossible (Bool.falseNotTrue (zs byComputing).flipped)
    | False, False => byComputing

--| A smaller numerator rounds to a double no greater, if a zero numerator's
--| sign is no greater either.
theorem Float.Theory.roundKeyMonoLe ∀ (den: Nat) (scale: Int) (z1 z2: Bool)
    (pd: 0 < den) (num1 num2: Int)
    (le: Int.leq num1 num2 = True)
    (zs: z1 = False → z2 = False):
    Int.leq (Float.Theory.roundKey num1 den scale z1) (Float.Theory.roundKey num2 den scale z2) = True :=
  Float.Theory.orCase
    (Float.Theory.boolCases (Int.less num1 num2))
    (lt => Float.Theory.roundKeyMono den scale z1 z2 pd num1 num2 lt)
    (lt =>
      let e: num1 = num2 := arithmetic [le, lt]
      rewrite e then
        Float.Theory.orCase
          [goal := Int.leq (Float.Theory.roundKey num2 den scale z1) (Float.Theory.roundKey num2 den scale z2) = True]
          (Float.Theory.intZeroCases num2)
          (n0 => rewrite n0 then Float.Theory.zeroKeyLe den scale z1 z2 zs)
          (ne =>
            J
              (y w =>
                Int.leq (Float.Theory.roundKey num2 den scale z1) (Float.keyOf y (Nat.leq 9223372036854775808 y))
                  = True)
              (Float.Theory.keyRefl (Float.Theory.roundKey num2 den scale z1))
              (Float.Theory.roundRatioSignIrrelevant den scale z1 z2 num2 ne)))

--| The total order on finite patterns is the order of their units.
theorem Float.Theory.unitsMonoKey ∀ (a c: Nat)
    (h: Int.leq (Float.Theory.key a) (Float.Theory.key c) = True):
    Int.leq (Float.Model.units a) (Float.Model.units c) = True :=
  rewrite Float.Theory.unitsMag a, Float.Theory.unitsMag c then
    match sa: Nat.leq 9223372036854775808 a, sc: Nat.leq 9223372036854775808 c with
      | False, False =>
        let ka: Float.Theory.key a = OfNat a := Float.Theory.keyClear a sa
        let kc: Float.Theory.key c = OfNat c := Float.Theory.keyClear c sc
        let le: a ≤ c := arithmetic [h, ka, kc]
        (arithmetic [Float.Theory.magUnitsLe a c le]: Int.leq
          (OfNat (Float.Theory.magUnits a))
          (OfNat (Float.Theory.magUnits c))
          = True)
      | True, False => arithmetic
      | True, True =>
        (arithmetic [Float.Theory.magUnitsLe (c - 9223372036854775808) (a - 9223372036854775808) h]: Int.leq
          (Int.neg (OfNat (Float.Theory.magUnits (a - 9223372036854775808))))
          (Int.neg (OfNat (Float.Theory.magUnits (c - 9223372036854775808))))
          = True)

--| `divBits` with neither argument the NaN nor infinite and a nonzero
--| divisor: the units' quotient, rounded.
theorem Float.Theory.divFiniteBits ∀ (a b: Nat)
    (na: Float.Model.isNaN a = False)
    (nb: Float.Model.isNaN b = False)
    (ia: Float.Model.isInfinite a = False)
    (ib: Float.Model.isInfinite b = False)
    (zb: Float.Model.isZero b = False):
    Float.Model.divBits a b
      = Float.Model.roundRatio
        (if Float.Model.signBit b then Int.neg (Float.Model.units a) else Float.Model.units a)
        (Int.natAbs (Float.Model.units b))
        (OfNat 0)
        (Bool.xor (Float.Model.signBit a) (Float.Model.signBit b)) :=
  let sign: Bool := Bool.xor (Float.Model.signBit a) (Float.Model.signBit b)
  let fin: Nat :=
    Float.Model.roundRatio
      (if Float.Model.signBit b then Int.neg (Float.Model.units a) else Float.Model.units a)
      (Int.natAbs (Float.Model.units b))
      (OfNat 0)
      sign
  let byZero: Nat := if Float.Model.isZero a then 9221120237041090560 else Float.Model.infinityBits sign
  let atInfinity: Nat := if Float.Model.isInfinite b then 9221120237041090560 else Float.Model.infinityBits sign
  let finiteA: Nat :=
    if Float.Model.isInfinite b then Float.Model.zeroBits sign
    else if Float.Model.isZero b then byZero
    else fin
  calc Float.Model.divBits a b
    _ = (if Float.Model.isInfinite a then atInfinity else finiteA) :=
      Float.Theory.ifFalse
        (Float.Model.isNaN a ∨ Float.Model.isNaN b)
        9221120237041090560
        (if Float.Model.isInfinite a then atInfinity else finiteA)
        (Float.Theory.orFalse (Float.Model.isNaN a) (Float.Model.isNaN b) na nb)
    _ = finiteA := Float.Theory.ifFalse (Float.Model.isInfinite a) atInfinity finiteA ia
    _ = (if Float.Model.isZero b then byZero else fin) :=
      Float.Theory.ifFalse
        (Float.Model.isInfinite b)
        (Float.Model.zeroBits sign)
        (if Float.Model.isZero b then byZero else fin)
        ib
    _ = fin := Float.Theory.ifFalse (Float.Model.isZero b) byZero fin zb

--| A sign that is clear stays clear up the total order.
theorem Float.Theory.signClearUp ∀ (a c: Nat)
    (h: Int.leq (Float.Theory.key a) (Float.Theory.key c) = True)
    (sa: Nat.leq 9223372036854775808 a = False):
    Nat.leq 9223372036854775808 c = False :=
  match sc: Nat.leq 9223372036854775808 c with
    | False => byComputing
    | True => Void.impossible (arithmetic [h, Float.Theory.keyClear a sa, Float.Theory.keySet c sc])

--| `x / y` on any two doubles, known or not: their bits' quotient.
theorem Float.Theory.divOfBits ∀ (x y: Float): x / y = Float.ofBits (Float.Model.divBits x.bits y.bits) :=
  match x, y with | { bits = a, valid = p }, { bits = b, valid = q } => byComputing

theorem Float.Theory.natAbsPos ∀ (i: Int) (h: Int.less (OfNat 0) i = True): 0 < Int.natAbs i := match i with
  | OfNat n => arithmetic [h]

theorem Float.Theory.positiveDivisor ∀ (s z: Bool) (u: Int) (den: Nat)
    (h: s = False):
    Float.Model.roundRatio (if s then Int.neg u else u) den (OfNat 0) (Bool.xor z s)
      = Float.Model.roundRatio u den (OfNat 0) z :=
  rewrite h, Float.Theory.xorFalse z

--| Dividing by a positive finite double: the units' quotient, rounded,
--| with the dividend's sign for a zero.
theorem Float.Theory.divPosBits ∀ (a b: Nat)
    (fa: Float.Theory.FiniteBits a)
    (fb: Float.Theory.FiniteBits b)
    (sb: Nat.leq 9223372036854775808 b = False)
    (zb: Float.Model.isZero b = False):
    Float.Model.divBits a b
      = Float.Model.roundRatio
        (Float.Model.units a)
        (Int.natAbs (Float.Model.units b))
        (OfNat 0)
        (Float.Model.signBit a) :=
  calc Float.Model.divBits a b
    _ = Float.Model.roundRatio
        (if Float.Model.signBit b then Int.neg (Float.Model.units a) else Float.Model.units a)
        (Int.natAbs (Float.Model.units b))
        (OfNat 0)
        (Bool.xor (Float.Model.signBit a) (Float.Model.signBit b)) :=
      Float.Theory.divFiniteBits a b
        (Float.Theory.finiteNotNaN a fa)
        (Float.Theory.finiteNotNaN b fb)
        (Float.Theory.finiteNotInfinite a fa)
        (Float.Theory.finiteNotInfinite b fb)
        zb
    _ = Float.Model.roundRatio
        (Float.Model.units a)
        (Int.natAbs (Float.Model.units b))
        (OfNat 0)
        (Float.Model.signBit a) :=
      Float.Theory.positiveDivisor
        (Float.Model.signBit b)
        (Float.Model.signBit a)
        (Float.Model.units a)
        (Int.natAbs (Float.Model.units b))
        sb

--| A NaN or infinite dividend over a positive finite double is itself.
theorem Float.Theory.divSpecialBits ∀ (a b: Nat)
    (va: Float.isValid a = True)
    (special: Nat.leq 9218868437227405312 (Float.Model.magnitude a) = True)
    (fb: Float.Theory.FiniteBits b)
    (sb: Nat.leq 9223372036854775808 b = False):
    Float.Model.divBits a b = a :=
  let sign: Bool := Bool.xor (Float.Model.signBit a) (Float.Model.signBit b)
  let atInfinity: Nat := if Float.Model.isInfinite b then 9221120237041090560 else Float.Model.infinityBits sign
  let finiteA: Nat :=
    if Float.Model.isInfinite b then Float.Model.zeroBits sign
    else if Float.Model.isZero b then
      (if Float.Model.isZero a then 9221120237041090560 else Float.Model.infinityBits sign)
    else
      Float.Model.roundRatio
        (if Float.Model.signBit b then Int.neg (Float.Model.units a) else Float.Model.units a)
        (Int.natAbs (Float.Model.units b))
        (OfNat 0)
        sign
  Float.Theory.orCase
    (Float.Theory.boolCases (Float.Model.isNaN a))
    (n =>
      Eq.trans
        (Float.Theory.ifTrue
          (Float.Model.isNaN a ∨ Float.Model.isNaN b)
          9221120237041090560
          (if Float.Model.isInfinite a then atInfinity else finiteA)
          (rewrite n))
        (Nat.equalSound a 9221120237041090560 n).flipped)
    (n =>
      let ia: Float.Model.isInfinite a = True := match c: Nat.leq 9223372036854775808 a with
        | True =>
          (arithmetic [Float.highBound a va (arithmetic [c]), special]: Nat.equal
            (a - 9223372036854775808)
            9218868437227405312
            = True)
        | False => (arithmetic [Float.lowBound a va n c, special]: Nat.equal a 9218868437227405312 = True)
      calc Float.Model.divBits a b
        _ = (if Float.Model.isInfinite a then atInfinity else finiteA) :=
          Float.Theory.ifFalse
            (Float.Model.isNaN a ∨ Float.Model.isNaN b)
            9221120237041090560
            (if Float.Model.isInfinite a then atInfinity else finiteA)
            (Float.Theory.orFalse (Float.Model.isNaN a) (Float.Model.isNaN b) n (Float.Theory.finiteNotNaN b fb))
        _ = atInfinity := Float.Theory.ifTrue (Float.Model.isInfinite a) atInfinity finiteA ia
        _ = Float.Model.infinityBits sign :=
          Float.Theory.ifFalse
            (Float.Model.isInfinite b)
            9221120237041090560
            (Float.Model.infinityBits sign)
            (Float.Theory.finiteNotInfinite b fb)
        _ = Float.Model.infinityBits (Float.Model.signBit a) :=
          Eq.cong Float.Model.infinityBits
            (rewrite sb, Float.Theory.xorFalse (Float.Model.signBit a): sign = Float.Model.signBit a)
        _ = a := Float.Theory.infinityOfBits a ia)

--| A rounding's key is at most +infinity's.
theorem Float.Theory.roundKeyLeInf ∀ (den: Nat) (scale: Int) (z: Bool)
    (pd: 0 < den) (num: Int):
    Int.leq (Float.Theory.roundKey num den scale z) (OfNat 9218868437227405312) = True :=
  match num with
    | OfNat Zero => Float.Theory.roundKeyZeroLe den scale z 9218868437227405312
    | OfNat (Succ k) =>
      rewrite Float.Theory.roundKeyPos k den scale z pd then
        (arithmetic [Float.Theory.magnitudeBound (Succ k) den (Int.add scale (OfNat 1074)) byComputing pd]: Int.leq
          (OfNat (Float.Model.roundMagnitude False (Succ k) den (Int.add scale (OfNat 1074))))
          (OfNat 9218868437227405312)
          = True)
    | NegSucc k => rewrite Float.Theory.roundKeyNeg k den scale z

--| -infinity's key is the least of every valid pattern's.
theorem Float.Theory.keyAboveNegInf ∀ (r: Nat)
    (v: Float.isValid r = True):
    Int.leq (NegSucc 9218868437227405312) (Float.Theory.key r) = True :=
  match c: Nat.leq 9223372036854775808 r with
    | True => arithmetic [Float.highBound r v (arithmetic [c])]
    | False => byComputing

--| A NaN or infinite pattern above a finite one is +infinity or the NaN.
theorem Float.Theory.specialAbove ∀ (a c: Nat)
    (fa: Float.Theory.FiniteBits a)
    (vc: Float.isValid c = True)
    (special: Nat.leq 9218868437227405312 (Float.Model.magnitude c) = True)
    (h: Int.leq (Float.Theory.key a) (Float.Theory.key c) = True):
    Int.leq (OfNat 9218868437227405312) (Float.Theory.key c) = True :=
  match sc: Nat.leq 9223372036854775808 c with
    | False => arithmetic [special]
    | True =>
      let kc: Float.Theory.key c = NegSucc (c - 9223372036854775808) := Float.Theory.keySet c sc
      let top: c ≤ 18442240474082181120 := Float.highBound c vc (arithmetic [sc])
      match sa: Nat.leq 9223372036854775808 a with
        | True => Void.impossible (arithmetic [h, kc, Float.Theory.keySet a sa, top, special, fa])

--| A NaN or infinite pattern below a finite one is -infinity.
theorem Float.Theory.specialBelow ∀ (a c: Nat)
    (va: Float.isValid a = True)
    (special: Nat.leq 9218868437227405312 (Float.Model.magnitude a) = True)
    (fc: Float.Theory.FiniteBits c)
    (h: Int.leq (Float.Theory.key a) (Float.Theory.key c) = True):
    Int.leq (Float.Theory.key a) (NegSucc 9218868437227405312) = True :=
  match sa: Nat.leq 9223372036854775808 a with
    | True => arithmetic [special]
    | False =>
      let ka: Float.Theory.key a = OfNat a := Float.Theory.keyClear a sa
      match sc: Nat.leq 9223372036854775808 c with
        | False => Void.impossible (arithmetic [h, ka, Float.Theory.keyClear c sc, special, fc])

theorem Float.Theory.leqTrans ∀ (a b c: Int) (x: Int.leq a b = True) (y: Int.leq b c = True): Int.leq a c = True :=
  arithmetic [x, y]

--| A positive double's sign bit is clear.
theorem Float.Theory.positiveSignClear ∀ (d: Float) (pos: 0.0 < d): Nat.leq 9223372036854775808 d.bits = False :=
  Float.Theory.signClearUp 0 d.bits (arithmetic [pos]) byComputing

--| A positive double isn't a zero.
theorem Float.Theory.positiveNotZero ∀ (d: Float) (pos: 0.0 < d): Float.Model.isZero d.bits = False :=
  let sb: Nat.leq 9223372036854775808 d.bits = False := Float.Theory.positiveSignClear d pos
  let kb: Float.Theory.key d.bits = OfNat d.bits := Float.Theory.keyClear d.bits sb
  let mb: Float.Model.magnitude d.bits = d.bits := rewrite sb
  (arithmetic [pos, kb, mb]: Nat.equal (Float.Model.magnitude d.bits) 0 = False)

--| The bits of `x / d` for finite `x` and positive finite `d`: the units' quotient, rounded.
theorem Float.Theory.quotientBits ∀ (x d: Float)
    (pos: 0.0 < d)
    (fd: Float.isFinite d = True)
    (fx: Float.isFinite x = True):
    (x / d).bits
      = Float.Model.roundRatio
        (Float.Model.units x.bits)
        (Int.natAbs (Float.Model.units d.bits))
        (OfNat 0)
        (Float.Model.signBit x.bits) :=
  let a: Nat := x.bits
  let b: Nat := d.bits
  let den: Nat := Int.natAbs (Float.Model.units b)
  let r: Nat := Float.Model.roundRatio (Float.Model.units a) den (OfNat 0) (Float.Model.signBit a)
  let e: Float.Model.divBits a b = r :=
    Float.Theory.divPosBits a b
      (Float.Theory.finiteBits x fx)
      (Float.Theory.finiteBits d fd)
      (Float.Theory.positiveSignClear d pos)
      (Float.Theory.positiveNotZero d pos)
  let pd: 0 < den := Float.Theory.natAbsPos (Float.Model.units b) (Float.Theory.unitsPositive d pos)
  calc (x / d).bits
    _ = (Float.ofBits (Float.Model.divBits a b)).bits := Eq.cong (q => q.bits) (Float.Theory.divOfBits x d)
    _ = Float.Model.divBits a b :=
      Float.Theory.ofBitsBits
        (Float.Model.divBits a b)
        (Float.Theory.validTo
          (Float.Model.divBits a b)
          r
          e
          (Float.Theory.roundRatioValid den (OfNat 0) (Float.Model.signBit a) pd (Float.Model.units a)))
    _ = r := e

--| The key of a finite double over a positive finite one: its units'
--| quotient's, rounded.
theorem Float.Theory.quotientKeyFinite ∀ (x d: Float)
    (pos: 0.0 < d)
    (fd: Float.isFinite d = True)
    (fx: Float.isFinite x = True):
    Float.orderKey (x / d)
      = Float.Theory.roundKey
        (Float.Model.units x.bits)
        (Int.natAbs (Float.Model.units d.bits))
        (OfNat 0)
        (Float.Model.signBit x.bits) :=
  Eq.cong Float.Theory.key (Float.Theory.quotientBits x d pos fd fx)

--| A NaN or infinite double over a positive finite one is itself.
theorem Float.Theory.quotientSpecial ∀ (x d: Float)
    (pos: 0.0 < d)
    (fd: Float.isFinite d = True)
    (special: Nat.leq 9218868437227405312 (Float.Model.magnitude x.bits) = True):
    (x / d).bits = x.bits :=
  let e: Float.Model.divBits x.bits d.bits = x.bits :=
    Float.Theory.divSpecialBits x.bits d.bits x.valid special
      (Float.Theory.finiteBits d fd)
      (Float.Theory.positiveSignClear d pos)
  calc (x / d).bits
    _ = (Float.ofBits (Float.Model.divBits x.bits d.bits)).bits := Eq.cong (q => q.bits) (Float.Theory.divOfBits x d)
    _ = Float.Model.divBits x.bits d.bits :=
      Float.Theory.ofBitsBits
        (Float.Model.divBits x.bits d.bits)
        (Float.Theory.validTo (Float.Model.divBits x.bits d.bits) x.bits e x.valid)
    _ = x.bits := e

theorem Float.Theory.specialOf ∀ (x: Float)
    (nf: Float.isFinite x = False):
    Nat.leq 9218868437227405312 (Float.Model.magnitude x.bits) = True :=
  match c: Nat.leq 9218868437227405312 (Float.Model.magnitude x.bits) with | True => byComputing

--| Dividing by a positive finite double never moves down the total order:
--| `x <= y → x / d <= y / d`, for every `x` and `y`, the NaN and the
--| infinities included (each is its own quotient).
-- Finite operands: their units are in order, so their quotients are
-- (`Float.Theory.roundKeyMonoLe`); a NaN or infinite one is its own quotient, and the
-- finite ones' quotients lie between -infinity and +infinity.
theorem Float.divMonotone ∀ (x y d: Float) (pos: 0.0 < d) (fd: Float.isFinite d = True) (h: x <= y): x / d <= y / d :=
  let den: Nat := Int.natAbs (Float.Model.units d.bits)
  let pd: 0 < den := Float.Theory.natAbsPos (Float.Model.units d.bits) (Float.Theory.unitsPositive d pos)
  let roundKey: Float → Int := x =>
    Float.Theory.roundKey (Float.Model.units x.bits) den (OfNat 0) (Float.Model.signBit x.bits)
  Float.Theory.orCase
    [goal := x / d <= y / d]
    (Float.Theory.boolCases (Float.isFinite x))
    (fx =>
      Float.Theory.orCase
        [goal := x / d <= y / d]
        (Float.Theory.boolCases (Float.isFinite y))
        (fy =>
          Float.Theory.leqVia
            (Float.orderKey (x / d))
            (Float.orderKey (y / d))
            (roundKey x)
            (roundKey y)
            (Float.Theory.quotientKeyFinite x d pos fd fx)
            (Float.Theory.quotientKeyFinite y d pos fd fy)
            (Float.Theory.roundKeyMonoLe den
              (OfNat 0)
              (Float.Model.signBit x.bits)
              (Float.Model.signBit y.bits)
              pd
              (Float.Model.units x.bits)
              (Float.Model.units y.bits)
              (Float.Theory.unitsMonoKey x.bits y.bits h)
              (Float.Theory.signClearUp x.bits y.bits h)))
        (fy =>
          let above: Int.leq (OfNat 9218868437227405312) (Float.Theory.key y.bits) = True :=
            Float.Theory.specialAbove x.bits y.bits
              (Float.Theory.finiteBits x fx)
              y.valid
              (Float.Theory.specialOf y fy)
              h
          let low: Int.leq (roundKey x) (OfNat 9218868437227405312) = True :=
            Float.Theory.roundKeyLeInf den (OfNat 0) (Float.Model.signBit x.bits) pd (Float.Model.units x.bits)
          Float.Theory.leqVia
            (Float.orderKey (x / d))
            (Float.orderKey (y / d))
            (roundKey x)
            (Float.Theory.key y.bits)
            (Float.Theory.quotientKeyFinite x d pos fd fx)
            (Eq.cong Float.Theory.key (Float.Theory.quotientSpecial y d pos fd (Float.Theory.specialOf y fy)))
            (Float.Theory.leqTrans (roundKey x) (OfNat 9218868437227405312) (Float.Theory.key y.bits) low above)))
    (fx =>
      Float.Theory.orCase
        [goal := x / d <= y / d]
        (Float.Theory.boolCases (Float.isFinite y))
        (fy =>
          let below: Int.leq (Float.Theory.key x.bits) (NegSucc 9218868437227405312) = True :=
            Float.Theory.specialBelow x.bits y.bits x.valid
              (Float.Theory.specialOf x fx)
              (Float.Theory.finiteBits y fy)
              h
          let least: Int.leq (NegSucc 9218868437227405312) (Float.Theory.key (y / d).bits) = True :=
            Float.Theory.keyAboveNegInf (y / d).bits (y / d).valid
          Float.Theory.leqVia
            (Float.orderKey (x / d))
            (Float.orderKey (y / d))
            (Float.Theory.key x.bits)
            (Float.Theory.key (y / d).bits)
            (Eq.cong Float.Theory.key (Float.Theory.quotientSpecial x d pos fd (Float.Theory.specialOf x fx)))
            byComputing
            (Float.Theory.leqTrans
              (Float.Theory.key x.bits)
              (NegSucc 9218868437227405312)
              (Float.Theory.key (y / d).bits)
              below
              least))
        (fy =>
          Float.Theory.leqVia
            (Float.orderKey (x / d))
            (Float.orderKey (y / d))
            (Float.Theory.key x.bits)
            (Float.Theory.key y.bits)
            (Eq.cong Float.Theory.key (Float.Theory.quotientSpecial x d pos fd (Float.Theory.specialOf x fx)))
            (Eq.cong Float.Theory.key (Float.Theory.quotientSpecial y d pos fd (Float.Theory.specialOf y fy)))
            h))

test "Float.divMonotone" :=
  1.0 / 3.0 <= 2.0 / 3.0
    ∧ -0.0 / 2.0 <= 0.0 / 2.0
    ∧ -5e-324 / 3.0 <= 5e-324 / 3.0
    ∧ 1.7976931348623157e308 / 0.5 <= Float.infinity / 0.5
    ∧ -Float.infinity / 5e-324 <= -1.0 / 5e-324
    ∧ 1.0 / 5e-324 <= Float.nan / 5e-324
    ∧ Float.ofNat 4294967295 / 4294967296.0 < 1.0

--| `0.0 < d → x <= y → x / d <= y / d` is false at `d = +infinity`:
--| `-infinity <= -1.0`, but `-infinity / infinity` is the NaN, above
--| `-1.0 / infinity`, which is `-0.0`.
test "division by infinity is not monotone" :=
  -Float.infinity <= -1.0 ∧ ¬(-Float.infinity / Float.infinity <= -1.0 / Float.infinity)

-- Rounding to whole numbers

--| `floorDiv` of a whole multiple of `p`, plus less than `p`, positive part.
theorem Float.Theory.floorDivPos ∀ (k h p: Nat) (hp: h < p): Float.Model.floorDiv False (k * p + h) p = OfNat k :=
  Eq.cong OfNat (Nat.divUnique (k * p + h) p k h hp byComputing)

theorem Float.Theory.succMul ∀ (k p: Nat): Succ k * p = p + k * p := byComputing

--| `floorDiv` of `-m` where `m + h = (k + 1) × p` and `h < p`: `-(k + 1)`.
theorem Float.Theory.floorDivNeg ∀ (k h p m: Nat)
    (hp: h < p)
    (e: m + h = Succ k * p):
    Float.Model.floorDiv True m p = NegSucc k :=
  match z: Nat.equal h 0 with
    | True =>
      let h0: h = 0 := Nat.equalSound h 0 z
      let q: m / p = Succ k :=
        Nat.divUnique m p (Succ k) 0 (arithmetic [hp, h0]) (arithmetic [e, h0, Float.Theory.succMul k p])
      let ex: Nat.equal (Succ k * p) m = True :=
        J
          (y w => Nat.equal (Succ k * p) y = True)
          (Nat.equalRefl (Succ k * p))
          (arithmetic [e, h0, Float.Theory.succMul k p]: Succ k * p = m)
      rewrite q, ex
    | False =>
      let hz: h ≠ 0 := Nat.equalFalse h 0 z
      let q: m / p = k :=
        Nat.divUnique m p k (p - h) (arithmetic [hp, hz]) (arithmetic [e, hp, Float.Theory.succMul k p])
      rewrite q then
        match c: Nat.equal (k * p) m with
          | True => Void.impossible (arithmetic [e, hp, hz, Float.Theory.succMul k p, Nat.equalSound (k * p) m c])
          | False => byComputing

theorem Float.Theory.negSuccMul ∀ (k p: Nat): Int.mul (NegSucc k) (OfNat p) = Int.neg (OfNat (Succ k * p)) := algebra

--| `floorDiv` finds `n` again in `n × p + h`, for `h < p`.
theorem Float.Theory.floorDivWhole ∀ (n: Int) (h p: Nat)
    (hp: h < p):
    Float.Model.floorDiv
      (Int.isNeg (Int.add (Int.mul n (OfNat p)) (OfNat h)))
      (Int.natAbs (Int.add (Int.mul n (OfNat p)) (OfNat h)))
      p
      = n :=
  match n with
    | OfNat k => Float.Theory.floorDivPos k h p hp
    | NegSucc k =>
      match c: Int.add (Int.mul (NegSucc k) (OfNat p)) (OfNat h) with
        | OfNat j => Void.impossible (arithmetic [c, hp, Float.Theory.negSuccMul k p, Float.Theory.succMul k p])
        | NegSucc j =>
          Float.Theory.floorDivNeg k h p
            (Succ j)
            hp
            (arithmetic [c, hp, Float.Theory.negSuccMul k p, Float.Theory.succMul k p])

theorem Float.Theory.negMul ∀ (q p: Nat): Int.mul (Int.neg (OfNat q)) (OfNat p) = Int.neg (OfNat (q * p)) := algebra

--| `floorDiv` is at most the quotient: `floorDiv s m p × p ≤ ±m`.
theorem Float.Theory.floorDivLe ∀ (s: Bool) (m p: Nat)
    (pp: 0 < p):
    Int.leq (Int.mul (Float.Model.floorDiv s m p) (OfNat p)) (Int.signed s m) = True :=
  let q: Nat := Nat.divFuel m m p
  let low: q * p ≤ m := Nat.divFuelLe m m p
  let high: m < Succ q * p := Nat.divFuelBound m m p (arithmetic [pp]) (Nat.leRefl m)
  match s with
    | False => arithmetic [low]
    | True =>
      match e: Nat.equal (q * p) m with
        | True => arithmetic [Nat.equalSound (q * p) m e, Float.Theory.negMul q p]
        | False => arithmetic [high, (byComputing: Int.mul (NegSucc q) (OfNat p) = Int.neg (OfNat (Succ q * p)))]

theorem Float.Theory.negIntMul ∀ (i: Int) (p: Nat): Int.mul (Int.neg i) (OfNat p) = Int.neg (Int.mul i (OfNat p)) :=
  algebra

--| `-floorDiv (¬s) m p`, the ceiling, is at least the quotient.
theorem Float.Theory.ceilDivGe ∀ (s: Bool) (m p: Nat)
    (pp: 0 < p):
    Int.leq (Int.signed s m) (Int.mul (Int.neg (Float.Model.floorDiv (¬s) m p)) (OfNat p)) = True :=
  let h: Int.leq (Int.mul (Float.Model.floorDiv (¬s) m p) (OfNat p)) (Int.signed (¬s) m) = True :=
    Float.Theory.floorDivLe (¬s) m p pp
  let n: Int.mul (Int.neg (Float.Model.floorDiv (¬s) m p)) (OfNat p)
    = Int.neg (Int.mul (Float.Model.floorDiv (¬s) m p) (OfNat p)) :=
    Float.Theory.negIntMul (Float.Model.floorDiv (¬s) m p) p
  match s with | True | False => arithmetic [h, n]

--| A whole number of doubles' units: `n` at scale 1 is `n × 2^1074` units.
theorem Float.Theory.roundWholeShift ∀ (s: Bool) (k: Nat) (z: Bool):
    Float.Model.roundRatio (Int.signed s k) 1 (OfNat 0) z
      = Float.Model.roundRatio (Int.signed s (k * Float.Model.pow2 1074)) 1 (-1074) z :=
  Float.Theory.orCase
    (Float.Theory.zeroOrPos k)
    (k0 =>
      rewrite k0 then
        match s with
          | False => byComputing
          | True => byComputing)
    (pk =>
      Float.Theory.roundRatioCross s k
        (k * Float.Model.pow2 1074)
        (OfNat 0)
        (-1074)
        z
        z
        pk
        (Float.Theory.mulPos k (Float.Model.pow2 1074) pk byComputing)
        (Nat.mulOne (k * Float.Model.pow2 1074 * 1)).flipped)

theorem Float.Theory.roundWhole ∀ (n: Int) (z: Bool):
    Float.Model.roundRatio n 1 (OfNat 0) z
      = Float.Model.roundRatio (Int.mul n (OfNat (Float.Model.pow2 1074))) 1 (-1074) z :=
  match n with
    | OfNat k => Float.Theory.roundWholeShift False k z
    | NegSucc k => Float.Theory.roundWholeShift True (Succ k) z

theorem Float.Theory.signedNatAbs ∀ (s: Bool) (k: Nat): Int.signed s (Int.natAbs (Int.signed s k)) = Int.signed s k :=
  match s, k with
    | False, k => byComputing
    | True, Zero | Succ _ => byComputing

--| A finite pattern's units: its size, with its sign.
theorem Float.Theory.unitsSigned ∀ (a: Nat):
    Int.signed (Float.Model.signBit a) (Int.natAbs (Float.Model.units a)) = Float.Model.units a :=
  rewrite Float.Theory.unitsMag a then
    Float.Theory.signedNatAbs (Float.Model.signBit a) (Float.Theory.magUnits (Float.Model.magnitude a))

--| A whole number at most a finite double's value rounds to a double no greater.
theorem Float.Theory.wholeBelow ∀ (a: Nat)
    (fin: Float.Theory.FiniteBits a) (n: Int)
    (le: Int.leq (Int.mul n (OfNat (Float.Model.pow2 1074))) (Float.Model.units a) = True):
    Int.leq (Float.Theory.key (Float.Model.roundScaled n 0 (Float.Model.signBit a))) (Float.Theory.key a) = True :=
  Float.Theory.leqVia
    (Float.Theory.key (Float.Model.roundScaled n 0 (Float.Model.signBit a)))
    (Float.Theory.key a)
    (Float.Theory.roundKey (Int.mul n (OfNat (Float.Model.pow2 1074))) 1 (-1074) (Float.Model.signBit a))
    (Float.Theory.roundKey (Float.Model.units a) 1 (-1074) (Float.Model.signBit a))
    (Eq.cong Float.Theory.key (Float.Theory.roundWhole n (Float.Model.signBit a)))
    (Eq.cong Float.Theory.key (Float.Theory.roundRatioUnitsBits a fin).flipped)
    (Float.Theory.roundKeyMonoLe 1
      (-1074)
      (Float.Model.signBit a)
      (Float.Model.signBit a)
      byComputing
      (Int.mul n (OfNat (Float.Model.pow2 1074)))
      (Float.Model.units a)
      le
      (h => h))

--| A whole number at least a finite double's value rounds to a double no smaller.
theorem Float.Theory.wholeAbove ∀ (a: Nat)
    (fin: Float.Theory.FiniteBits a) (n: Int)
    (ge: Int.leq (Float.Model.units a) (Int.mul n (OfNat (Float.Model.pow2 1074))) = True):
    Int.leq (Float.Theory.key a) (Float.Theory.key (Float.Model.roundScaled n 0 (Float.Model.signBit a))) = True :=
  Float.Theory.leqVia
    (Float.Theory.key a)
    (Float.Theory.key (Float.Model.roundScaled n 0 (Float.Model.signBit a)))
    (Float.Theory.roundKey (Float.Model.units a) 1 (-1074) (Float.Model.signBit a))
    (Float.Theory.roundKey (Int.mul n (OfNat (Float.Model.pow2 1074))) 1 (-1074) (Float.Model.signBit a))
    (Eq.cong Float.Theory.key (Float.Theory.roundRatioUnitsBits a fin).flipped)
    (Eq.cong Float.Theory.key (Float.Theory.roundWhole n (Float.Model.signBit a)))
    (Float.Theory.roundKeyMonoLe 1
      (-1074)
      (Float.Model.signBit a)
      (Float.Model.signBit a)
      byComputing
      (Float.Model.units a)
      (Int.mul n (OfNat (Float.Model.pow2 1074)))
      ge
      (h => h))

theorem Float.Theory.finiteOfSpecial ∀ (a: Nat) (sp: Float.Model.isSpecial a = False): Float.Theory.FiniteBits a :=
  arithmetic [sp]

--| What `floorBits` computes for a finite pattern.
theorem Float.Theory.floorFinite ∀ (a: Nat)
    (sp: Float.Model.isSpecial a = False):
    Float.Model.floorBits a
      = Float.Model.roundScaled
        (Float.Model.floorDiv (Float.Model.signBit a) (Int.natAbs (Float.Model.units a)) (Float.Model.pow2 1074))
        0
        (Float.Model.signBit a) :=
  Float.Theory.ifFalse
    (Float.Model.isSpecial a)
    a
    (Float.Model.roundScaled
      (Float.Model.floorDiv (Float.Model.signBit a) (Int.natAbs (Float.Model.units a)) (Float.Model.pow2 1074))
      0
      (Float.Model.signBit a))
    sp

--| What `ceilBits` computes for a finite pattern.
theorem Float.Theory.ceilFinite ∀ (a: Nat)
    (sp: Float.Model.isSpecial a = False):
    Float.Model.ceilBits a
      = Float.Model.roundScaled
        (Int.neg
          (Float.Model.floorDiv (¬(Float.Model.signBit a)) (Int.natAbs (Float.Model.units a)) (Float.Model.pow2 1074)))
        0
        (Float.Model.signBit a) :=
  Float.Theory.ifFalse
    (Float.Model.isSpecial a)
    a
    (Float.Model.roundScaled
      (Int.neg
        (Float.Model.floorDiv (¬(Float.Model.signBit a)) (Int.natAbs (Float.Model.units a)) (Float.Model.pow2 1074)))
      0
      (Float.Model.signBit a))
    sp

--| A NaN or infinite pattern is its own floor.
theorem Float.Theory.floorSpecial ∀ (a: Nat) (sp: Float.Model.isSpecial a = True): Float.Model.floorBits a = a :=
  Float.Theory.ifTrue
    (Float.Model.isSpecial a)
    a
    (Float.Model.roundScaled
      (Float.Model.floorDiv (Float.Model.signBit a) (Int.natAbs (Float.Model.units a)) (Float.Model.pow2 1074))
      0
      (Float.Model.signBit a))
    sp

--| A NaN or infinite pattern is its own ceiling.
theorem Float.Theory.ceilSpecial ∀ (a: Nat) (sp: Float.Model.isSpecial a = True): Float.Model.ceilBits a = a :=
  Float.Theory.ifTrue
    (Float.Model.isSpecial a)
    a
    (Float.Model.roundScaled
      (Int.neg
        (Float.Model.floorDiv (¬(Float.Model.signBit a)) (Int.natAbs (Float.Model.units a)) (Float.Model.pow2 1074)))
      0
      (Float.Model.signBit a))
    sp

theorem Float.Theory.keyLeVia ∀ (r s a: Nat)
    (e: s = r)
    (h: Int.leq (Float.Theory.key r) (Float.Theory.key a) = True):
    Int.leq (Float.Theory.key s) (Float.Theory.key a) = True :=
  J (y w => Int.leq (Float.Theory.key y) (Float.Theory.key a) = True) h e.flipped

theorem Float.Theory.keyGeVia ∀ (r s a: Nat)
    (e: s = r)
    (h: Int.leq (Float.Theory.key a) (Float.Theory.key r) = True):
    Int.leq (Float.Theory.key a) (Float.Theory.key s) = True :=
  J (y w => Int.leq (Float.Theory.key a) (Float.Theory.key y) = True) h e.flipped

--| A pattern's floor is at most it in the total order.
theorem Float.Theory.floorBitsLe ∀ (a: Nat):
    Int.leq (Float.Theory.key (Float.Model.floorBits a)) (Float.Theory.key a) = True :=
  Float.Theory.orCase
    (Float.Theory.boolCases (Float.Model.isSpecial a))
    (sp =>
      Float.Theory.keyLeVia a
        (Float.Model.floorBits a)
        a
        (Float.Theory.floorSpecial a sp)
        (Float.Theory.keyRefl (Float.Theory.key a)))
    (sp =>
      let s: Bool := Float.Model.signBit a
      let m: Nat := Int.natAbs (Float.Model.units a)
      let n: Int := Float.Model.floorDiv s m (Float.Model.pow2 1074)
      let le: Int.leq (Int.mul n (OfNat (Float.Model.pow2 1074))) (Float.Model.units a) = True :=
        J
          (y w => Int.leq (Int.mul n (OfNat (Float.Model.pow2 1074))) y = True)
          (Float.Theory.floorDivLe s m (Float.Model.pow2 1074) byComputing)
          (Float.Theory.unitsSigned a)
      Float.Theory.keyLeVia
        (Float.Model.roundScaled n 0 s)
        (Float.Model.floorBits a)
        a
        (Float.Theory.floorFinite a sp)
        (Float.Theory.wholeBelow a (Float.Theory.finiteOfSpecial a sp) n le))

--| A pattern's ceiling is at least it in the total order.
theorem Float.Theory.ceilBitsGe ∀ (a: Nat):
    Int.leq (Float.Theory.key a) (Float.Theory.key (Float.Model.ceilBits a)) = True :=
  Float.Theory.orCase
    (Float.Theory.boolCases (Float.Model.isSpecial a))
    (sp =>
      Float.Theory.keyGeVia a
        (Float.Model.ceilBits a)
        a
        (Float.Theory.ceilSpecial a sp)
        (Float.Theory.keyRefl (Float.Theory.key a)))
    (sp =>
      let s: Bool := Float.Model.signBit a
      let m: Nat := Int.natAbs (Float.Model.units a)
      let n: Int := Int.neg (Float.Model.floorDiv (¬s) m (Float.Model.pow2 1074))
      let ge: Int.leq (Float.Model.units a) (Int.mul n (OfNat (Float.Model.pow2 1074))) = True :=
        J
          (y w => Int.leq y (Int.mul n (OfNat (Float.Model.pow2 1074))) = True)
          (Float.Theory.ceilDivGe s m (Float.Model.pow2 1074) byComputing)
          (Float.Theory.unitsSigned a)
      Float.Theory.keyGeVia
        (Float.Model.roundScaled n 0 s)
        (Float.Model.ceilBits a)
        a
        (Float.Theory.ceilFinite a sp)
        (Float.Theory.wholeAbove a (Float.Theory.finiteOfSpecial a sp) n ge))

theorem Float.Theory.floorBitsValid ∀ (a: Nat)
    (v: Float.isValid a = True):
    Float.isValid (Float.Model.floorBits a) = True :=
  Float.Theory.orCase
    (Float.Theory.boolCases (Float.Model.isSpecial a))
    (sp => Float.Theory.validTo (Float.Model.floorBits a) a (Float.Theory.floorSpecial a sp) v)
    (sp =>
      Float.Theory.validTo
        (Float.Model.floorBits a)
        (Float.Model.roundScaled
          (Float.Model.floorDiv (Float.Model.signBit a) (Int.natAbs (Float.Model.units a)) (Float.Model.pow2 1074))
          0
          (Float.Model.signBit a))
        (Float.Theory.floorFinite a sp)
        (Float.Theory.roundRatioValid 1 0
          (Float.Model.signBit a)
          byComputing
          (Float.Model.floorDiv (Float.Model.signBit a) (Int.natAbs (Float.Model.units a)) (Float.Model.pow2 1074))))

theorem Float.Theory.ceilBitsValid ∀ (a: Nat)
    (v: Float.isValid a = True):
    Float.isValid (Float.Model.ceilBits a) = True :=
  Float.Theory.orCase
    (Float.Theory.boolCases (Float.Model.isSpecial a))
    (sp => Float.Theory.validTo (Float.Model.ceilBits a) a (Float.Theory.ceilSpecial a sp) v)
    (sp =>
      Float.Theory.validTo
        (Float.Model.ceilBits a)
        (Float.Model.roundScaled
          (Int.neg
            (Float.Model.floorDiv
              (¬(Float.Model.signBit a))
              (Int.natAbs (Float.Model.units a))
              (Float.Model.pow2 1074)))
          0
          (Float.Model.signBit a))
        (Float.Theory.ceilFinite a sp)
        (Float.Theory.roundRatioValid 1 0
          (Float.Model.signBit a)
          byComputing
          (Int.neg
            (Float.Model.floorDiv
              (¬(Float.Model.signBit a))
              (Int.natAbs (Float.Model.units a))
              (Float.Model.pow2 1074)))))

theorem Float.Theory.floorOfBits ∀ (x: Float): (Float.floor x).bits = Float.Model.floorBits x.bits :=
  let e: Float.floor x = Float.ofBits (Float.Model.floorBits x.bits) := match x with
    | { bits = a, valid = p } => byComputing
  Eq.trans
    (Eq.cong (q => q.bits) e)
    (Float.Theory.ofBitsBits (Float.Model.floorBits x.bits) (Float.Theory.floorBitsValid x.bits x.valid))

theorem Float.Theory.ceilOfBits ∀ (x: Float): (Float.ceil x).bits = Float.Model.ceilBits x.bits :=
  let e: Float.ceil x = Float.ofBits (Float.Model.ceilBits x.bits) := match x with
    | { bits = a, valid = p } => byComputing
  Eq.trans
    (Eq.cong (q => q.bits) e)
    (Float.Theory.ofBitsBits (Float.Model.ceilBits x.bits) (Float.Theory.ceilBitsValid x.bits x.valid))

--| `floor x <= x` in the total order, for every double: the NaN and the
--| infinities are their own floors.
theorem Float.floorLe ∀ (x: Float): Float.floor x <= x :=
  Float.Theory.keyLeVia
    (Float.Model.floorBits x.bits)
    (Float.floor x).bits
    x.bits
    (Float.Theory.floorOfBits x)
    (Float.Theory.floorBitsLe x.bits)

--| `x <= ceil x` in the total order, for every double.
theorem Float.ceilGe ∀ (x: Float): x <= Float.ceil x :=
  Float.Theory.keyGeVia
    (Float.Model.ceilBits x.bits)
    (Float.ceil x).bits
    x.bits
    (Float.Theory.ceilOfBits x)
    (Float.Theory.ceilBitsGe x.bits)

theorem Float.Theory.roundSpecial ∀ (a: Nat) (sp: Float.Model.isSpecial a = True): Float.Model.roundBits a = a :=
  Float.Theory.ifTrue
    (Float.Model.isSpecial a)
    a
    (Float.Model.roundScaled
      (Float.Model.floorDiv
        (Int.isNeg (Int.add (Float.Model.units a) (OfNat (Float.Model.pow2 1073))))
        (Int.natAbs (Int.add (Float.Model.units a) (OfNat (Float.Model.pow2 1073))))
        (Float.Model.pow2 1074))
      0
      (Float.Model.signBit a))
    sp

--| A finite pattern whose value is the whole number `n` is its own rounding.
theorem Float.Theory.roundWholeBits ∀ (a: Nat) (n: Int)
    (whole: Float.Model.units a = Int.mul n (OfNat (Float.Model.pow2 1074))):
    Float.Model.roundBits a = a :=
  Float.Theory.orCase (Float.Theory.boolCases (Float.Model.isSpecial a)) (sp => Float.Theory.roundSpecial a sp) (sp =>
    let s: Bool := Float.Model.signBit a
    let half: Nat := Float.Model.pow2 1073
    let p: Nat := Float.Model.pow2 1074
    let back: Float.Model.floorDiv
      (Int.isNeg (Int.add (Int.mul n (OfNat p)) (OfNat half)))
      (Int.natAbs (Int.add (Int.mul n (OfNat p)) (OfNat half)))
      p
      = n :=
      Float.Theory.floorDivWhole n half p byComputing
    let q: Float.Model.floorDiv
      (Int.isNeg (Int.add (Float.Model.units a) (OfNat half)))
      (Int.natAbs (Int.add (Float.Model.units a) (OfNat half)))
      p
      = n :=
      J
        (y w => Float.Model.floorDiv (Int.isNeg (Int.add y (OfNat half))) (Int.natAbs (Int.add y (OfNat half))) p = n)
        back
        whole.flipped
    calc Float.Model.roundBits a
      _ = Float.Model.roundScaled
          (Float.Model.floorDiv
            (Int.isNeg (Int.add (Float.Model.units a) (OfNat half)))
            (Int.natAbs (Int.add (Float.Model.units a) (OfNat half)))
            p)
          0
          s :=
        Float.Theory.ifFalse
          (Float.Model.isSpecial a)
          a
          (Float.Model.roundScaled
            (Float.Model.floorDiv
              (Int.isNeg (Int.add (Float.Model.units a) (OfNat half)))
              (Int.natAbs (Int.add (Float.Model.units a) (OfNat half)))
              p)
            0
            s)
          sp
      _ = Float.Model.roundScaled n 0 s := Eq.cong (k => Float.Model.roundScaled k 0 s) q
      _ = Float.Model.roundRatio (Int.mul n (OfNat p)) 1 (-1074) s := Float.Theory.roundWhole n s
      _ = Float.Model.roundRatio (Float.Model.units a) 1 (-1074) s :=
        Eq.cong (u => Float.Model.roundRatio u 1 (-1074) s) whole.flipped
      _ = a := Float.Theory.roundRatioUnitsBits a (Float.Theory.finiteOfSpecial a sp))

--| `round x = x` for a double whose value is a whole number `n`: its units
--| (of 2^-1074) are `n × 2^1074`. The NaN and the infinities are their own
--| roundings too, whatever `n`.
theorem Float.roundOfWhole ∀ (x: Float) (n: Int)
    (whole: Float.Theory.units x = Int.mul n (OfNat (Float.Model.pow2 1074))):
    Float.round x = x :=
  match x with
    | { bits = a, valid = v } =>
      Float.bitsExt
        (Float.ofBits (Float.Model.roundBits a))
        { bits = a, valid = v }
        (Eq.trans
          (Float.Theory.ofBitsBits
            (Float.Model.roundBits a)
            (Float.Theory.validTo (Float.Model.roundBits a) a (Float.Theory.roundWholeBits a n whole) v))
          (Float.Theory.roundWholeBits a n whole))

--| `round (ofNat n) = ofNat n` for `n ≤ 2^53`, where `ofNat` is exact.
theorem Float.roundOfNat ∀ (n: Nat) (h: n ≤ 9007199254740992): Float.round (Float.ofNat n) = Float.ofNat n :=
  Float.roundOfWhole
    (Float.ofNat n)
    (OfNat n)
    (Eq.trans
      (Float.ofNatExact n h)
      (byComputing: OfNat (n * Nat.pow 2 1074) = Int.mul (OfNat n) (OfNat (Float.Model.pow2 1074))))

test "Float.floorLe" :=
  Float.floor 2.5 <= 2.5 ∧ Float.floor -2.5 <= -2.5 ∧ Float.floor -0.0 <= -0.0 ∧ Float.floor Float.nan <= Float.nan

test "Float.ceilGe" :=
  2.5 <= Float.ceil 2.5
    ∧ -2.5 <= Float.ceil -2.5
    ∧ -0.5 <= Float.ceil -0.5
    ∧ -Float.infinity <= Float.ceil -Float.infinity

test "Float.roundOfWhole" :=
  Float.round 3.0 == 3.0 ∧ Float.round -4.0 == -4.0 ∧ Float.round 4503599627370497.0 == 4503599627370497.0

test "Float.roundOfNat" :=
  Float.round (Float.ofNat 3) == Float.ofNat 3 ∧ Float.round 2.5 == 3.0 ∧ Float.round -2.5 == -2.0

-- Exact division of whole numbers

theorem Float.Theory.ltLeTrans ∀ (a b c: Int) (x: Int.less a b = True) (y: Int.leq b c = True): Int.less a c = True :=
  arithmetic [x, y]

--| `ofNat d` is positive for `1 ≤ d`.
theorem Float.ofNatPositive ∀ (d: Nat) (h: 1 ≤ d): 0.0 < Float.ofNat d :=
  Float.Theory.ltLeTrans
    (Float.orderKey 0.0)
    (Float.orderKey (Float.ofNat 1))
    (Float.orderKey (Float.ofNat d))
    byComputing
    (Float.ofNatMonotone 1 d h)

theorem Float.Theory.crossWhole ∀ (k d p q: Nat): k * d * p * q * 1 = k * q * (d * p) := algebra

--| `k × d × 2^1074` units over `d × 2^1074` round as `k` units of 1 do.
theorem Float.Theory.roundQuotientWhole ∀ (k d: Nat)
    (pk: 0 < k)
    (pd: 0 < d):
    Float.Model.roundRatio (OfNat (k * d * Nat.pow 2 1074)) (d * Nat.pow 2 1074) (OfNat 0) False
      = Float.Model.roundRatio (OfNat k) 1 (OfNat 0) False :=
  let p: Nat := Nat.pow 2 1074
  let pp: 0 < p := byComputing
  let pkd: 0 < k * d * p := Float.Theory.mulPos (k * d) p (Float.Theory.mulPos k d pk pd) pp
  calc Float.Model.roundRatio (OfNat (k * d * p)) (d * p) (OfNat 0) False
    _ = Float.Model.roundMagnitude False (k * d * p) (d * p) (Int.add (OfNat 0) (OfNat 1074)) :=
      Float.Theory.roundRatioOfPos (d * p) (OfNat 0) False (k * d * p) pkd
    _ = Float.Model.roundMagnitude False k 1 (Int.add (OfNat 0) (OfNat 1074)) :=
      Float.Theory.magnitudeCross
        (k * d * p)
        (d * p)
        k
        1
        (Int.add (OfNat 0) (OfNat 1074))
        (Int.add (OfNat 0) (OfNat 1074))
        pkd
        (Float.Theory.mulPos d p pd pp)
        pk
        byComputing
        (Float.Theory.crossWhole k d p (Float.Model.pow2 1074))
    _ = Float.Model.roundRatio (OfNat k) 1 (OfNat 0) False :=
      (Float.Theory.roundRatioOfPos 1 (OfNat 0) False k pk).flipped

theorem Float.Theory.posNonzero ∀ (n: Nat) (h: 0 < n): OfNat n ≠ OfNat 0 := match n with | Succ m => (e => cases)

--| Whole numbers up to 2^53 divide exactly where the quotient is whole:
--| `ofNat (k × d) / ofNat d = ofNat k` for `1 ≤ d ≤ 2^53` and `k × d ≤ 2^53`.
--| With `Float.ofNatMul`, `ofNat k * 10.0` and `/ 10.0` are exact for
--| `k × 10 ≤ 2^53`.
-- Both operands are exact (`ofNatExact`), so the quotient is the units'
-- ratio `k × d × 2^1074 / (d × 2^1074)`, which rounds as `k` does.
theorem Float.ofNatDivExact ∀ (k d: Nat)
    (pd: 1 ≤ d)
    (hd: d ≤ 9007199254740992)
    (hk: k * d ≤ 9007199254740992):
    Float.ofNat (k * d) / Float.ofNat d = Float.ofNat k :=
  let x: Float := Float.ofNat (k * d)
  let y: Float := Float.ofNat d
  let p: Nat := Nat.pow 2 1074
  let ux: Float.Model.units x.bits = OfNat (k * d * p) := Float.ofNatExact (k * d) hk
  let uy: Float.Model.units y.bits = OfNat (d * p) := Float.ofNatExact d hd
  let q: (x / y).bits = Float.Model.roundRatio (OfNat (k * d * p)) (d * p) (OfNat 0) (Float.Model.signBit x.bits) :=
    calc (x / y).bits
      _ = Float.Model.roundRatio
          (Float.Model.units x.bits)
          (Int.natAbs (Float.Model.units y.bits))
          (OfNat 0)
          (Float.Model.signBit x.bits) :=
        Float.Theory.quotientBits x y (Float.ofNatPositive d pd) (Float.ofNatFinite d hd) (Float.ofNatFinite (k * d) hk)
      _ = Float.Model.roundRatio
          (OfNat (k * d * p))
          (Int.natAbs (OfNat (d * p)))
          (OfNat 0)
          (Float.Model.signBit x.bits) :=
        Eq.cong2 (u w => Float.Model.roundRatio u (Int.natAbs w) (OfNat 0) (Float.Model.signBit x.bits)) ux uy
  Float.Theory.orCase
    [goal := x / y = Float.ofNat k]
    (Float.Theory.zeroOrPos k)
    (k0 =>
      Float.bitsExt
        (x / y)
        (Float.ofNat k)
        (Eq.trans q
          (rewrite k0: Float.Model.roundRatio (OfNat (k * d * p)) (d * p) (OfNat 0) (Float.Model.signBit x.bits)
            = (Float.ofNat k).bits)))
    (pk =>
      Float.bitsExt
        (x / y)
        (Float.ofNat k)
        (calc (x / y).bits
          _ = Float.Model.roundRatio (OfNat (k * d * p)) (d * p) (OfNat 0) (Float.Model.signBit x.bits) := q
          _ = Float.Model.roundRatio (OfNat (k * d * p)) (d * p) (OfNat 0) False :=
            Float.Theory.roundRatioSignIrrelevant
              (d * p)
              (OfNat 0)
              (Float.Model.signBit x.bits)
              False
              (OfNat (k * d * p))
              (Float.Theory.posNonzero
                (k * d * p)
                (Float.Theory.mulPos (k * d) p (Float.Theory.mulPos k d pk pd) byComputing))
          _ = Float.Model.roundRatio (OfNat k) 1 (OfNat 0) False := Float.Theory.roundQuotientWhole k d pk pd
          _ = (Float.ofNat k).bits :=
            (Float.Theory.ofBitsBits
              (Float.Model.ofIntBits (OfNat k))
              (Float.Theory.roundRatioValid 1 (OfNat 0) False byComputing (OfNat k))).flipped))

test "Float.ofNatDivExact" :=
  Float.ofNat 1234 / 10.0 == 123.4
    ∧ Float.ofNat 1230 / 10.0 == 123.0
    ∧ Float.ofNat 123 * 10.0 == Float.ofNat 1230
    ∧ Float.ofNat 90071992547409920 / 10.0 == Float.ofNat 9007199254740992

-- Whole numbers of units at any exponent are doubles

--| A pattern up to 2^53 is its own number of units: below 2^52 a
--| subnormal, then exponent field 1, whose scale is 2^0, and at 2^53 the
--| first pattern of field 2.
theorem Float.Theory.magUnitsSmall ∀ (q: Nat) (h: q ≤ 9007199254740992): Float.Theory.magUnits q = q :=
  calc Float.Theory.magUnits q
    _ = Float.Theory.magUnits (0 * 4503599627370496 + q) :=
      Eq.cong Float.Theory.magUnits (arithmetic: q = 0 * 4503599627370496 + q)
    _ = Nat.pow 2 0 * q := Float.Theory.magUnitsGrid 0 q h (Inl byComputing)
    _ = q := algebra

--| The pattern with twice `m`'s units: a subnormal's bits doubled, or one
--| exponent up.
def Float.Theory.doubleBits (m: Nat): Nat := if Nat.leq 4503599627370496 m then m + 4503599627370496 else m + m

theorem Float.Theory.magUnitsDoubleHigh ∀ (m: Nat)
    (c: Nat.leq 4503599627370496 m = True):
    Float.Theory.magUnits (Float.Theory.doubleBits m) = Float.Theory.magUnits m + Float.Theory.magUnits m :=
  let e: Nat := Nat.divFuel m m 4503599627370496
  let low: e * 4503599627370496 ≤ m := Nat.divFuelLe m m 4503599627370496
  let high: m < Succ e * 4503599627370496 :=
    Nat.divFuelBound m m 4503599627370496 (Nat.nonzeroOfPos 4503599627370496 byComputing) (Nat.leRefl m)
  let f: Nat := m - e * 4503599627370496
  let g: Nat := e - 1
  let here: Float.Theory.magUnits m = Nat.pow 2 g * (f + 4503599627370496) :=
    Eq.trans
      (Eq.cong Float.Theory.magUnits (arithmetic [c, low, high]: m = g * 4503599627370496 + 4503599627370496 + f))
      (Float.Theory.magUnitsFieldNext g f (arithmetic [low, high]))
  let up: Float.Theory.magUnits (m + 4503599627370496) = Nat.pow 2 (Succ g) * (f + 4503599627370496) :=
    Eq.trans
      (Eq.cong Float.Theory.magUnits
        (arithmetic [c, low, high]: m + 4503599627370496 = Succ g * 4503599627370496 + 4503599627370496 + f))
      (Float.Theory.magUnitsFieldNext (Succ g) f (arithmetic [low, high]))
  let d: Float.Theory.doubleBits m = m + 4503599627370496 := rewrite c
  calc Float.Theory.magUnits (Float.Theory.doubleBits m)
    _ = Float.Theory.magUnits (m + 4503599627370496) := Eq.cong Float.Theory.magUnits d
    _ = Nat.pow 2 (Succ g) * (f + 4503599627370496) := up
    _ = 2 * Nat.pow 2 g * (f + 4503599627370496) := Eq.cong (t => t * (f + 4503599627370496)) (Nat.powSucc 2 g)
    _ = Nat.pow 2 g * (f + 4503599627370496) + Nat.pow 2 g * (f + 4503599627370496) := algebra
    _ = Float.Theory.magUnits m + Float.Theory.magUnits m := rewrite here

theorem Float.Theory.magUnitsDouble ∀ (m: Nat):
    Float.Theory.magUnits (Float.Theory.doubleBits m) = Float.Theory.magUnits m + Float.Theory.magUnits m :=
  Float.Theory.orCase
    (Float.Theory.boolCases (Nat.leq 4503599627370496 m))
    (c => Float.Theory.magUnitsDoubleHigh m c)
    (c =>
      let d: Float.Theory.doubleBits m = m + m := rewrite c
      let small: Float.Theory.magUnits m = m := Float.Theory.magUnitsSmall m (arithmetic [c])
      calc Float.Theory.magUnits (Float.Theory.doubleBits m)
        _ = Float.Theory.magUnits (m + m) := Eq.cong Float.Theory.magUnits d
        _ = m + m := Float.Theory.magUnitsSmall (m + m) (arithmetic [c])
        _ = Float.Theory.magUnits m + Float.Theory.magUnits m := arithmetic [small])

--| The pattern of `q × 2^e` units: `q`'s own, doubled `e` times.
def Float.Theory.gridBits (q: Nat): (e: Nat) → Nat
  | Zero => q
  | Succ e => Float.Theory.doubleBits (Float.Theory.gridBits q e)

theorem Float.Theory.gridUnits ∀ (q e: Nat)
    (hq: q ≤ 9007199254740992):
    Float.Theory.magUnits (Float.Theory.gridBits q e) = q * Nat.pow 2 e :=
  match e with
    | Zero => Eq.trans (Float.Theory.magUnitsSmall q hq) (algebra: q = q * Nat.pow 2 0)
    | Succ e =>
      calc Float.Theory.magUnits (Float.Theory.doubleBits (Float.Theory.gridBits q e))
        _ = Float.Theory.magUnits (Float.Theory.gridBits q e) + Float.Theory.magUnits (Float.Theory.gridBits q e) :=
          Float.Theory.magUnitsDouble (Float.Theory.gridBits q e)
        _ = q * Nat.pow 2 e + q * Nat.pow 2 e := rewrite Float.Theory.gridUnits q e hq
        _ = q * (2 * Nat.pow 2 e) := algebra
        _ = q * Nat.pow 2 (Succ e) := Eq.cong (t => q * t) (Nat.powSucc 2 e).flipped

--| A pattern with fewer units than 2^1024 is finite.
theorem Float.Theory.atLeastOf ∀ (a b: Nat) (c: Nat.leq a b = True): a ≤ b := c

theorem Float.Theory.belowInfinity ∀ (m: Nat) (c: Nat.leq 9218868437227405312 m = False): m < 9218868437227405312 :=
  arithmetic [c]

theorem Float.Theory.leLessAbsurd ∀ (a b: Nat) (x: a ≤ b) (y: b < a): Void := arithmetic

theorem Float.Theory.finiteOfUnits ∀ (m: Nat) (h: Float.Theory.magUnits m < Nat.pow 2 2098): m < 9218868437227405312 :=
  Float.Theory.orCase
    (Float.Theory.boolCases (Nat.leq 9218868437227405312 m))
    (c =>
      let le: Float.Theory.magUnits 9218868437227405312 ≤ Float.Theory.magUnits m :=
        Float.Theory.magUnitsLe 9218868437227405312 m (Float.Theory.atLeastOf 9218868437227405312 m c)
      let inf: Float.Theory.magUnits 9218868437227405312 = Nat.pow 2 2098 :=
        Eq.trans Float.Theory.unitsAtInfinity (Float.Theory.pow2Pow 2098)
      Void.impossible
        (Float.Theory.leLessAbsurd
          (Nat.pow 2 2098)
          (Float.Theory.magUnits m)
          (J (y w => y ≤ Float.Theory.magUnits m) le inf)
          h))
    (c => Float.Theory.belowInfinity m c)

theorem Float.Theory.gridFinite ∀ (q e: Nat)
    (hq: q ≤ 9007199254740992)
    (fin: q * Nat.pow 2 e < Nat.pow 2 2098):
    Float.Theory.gridBits q e < 9218868437227405312 :=
  Float.Theory.finiteOfUnits
    (Float.Theory.gridBits q e)
    (J (y w => y < Nat.pow 2 2098) fin (Float.Theory.gridUnits q e hq).flipped)

theorem Float.Theory.signedNonzero ∀ (s: Bool) (n: Nat) (pn: 0 < n): Int.signed s n ≠ OfNat 0 := match s, n with
  | False | True, Succ _ => (e => cases)

--| The finite pattern of magnitude `m` and sign `s`: its units.
theorem Float.Theory.unitsOfMagnitude ∀ (m: Nat) (s: Bool)
    (fm: m < 9218868437227405312):
    Float.Theory.FiniteBits (if s then m + 9223372036854775808 else m)
      ∧ (Float.Model.units (if s then m + 9223372036854775808 else m) = Int.signed s (Float.Theory.magUnits m)) :=
  match s with
    | False =>
      let c: Nat.leq 9223372036854775808 m = False := arithmetic [fm]
      let mag: Float.Model.magnitude m = m := rewrite c
      Both (arithmetic [mag, fm]) (rewrite Float.Theory.unitsMag m, mag, c)
    | True =>
      let c: Nat.leq 9223372036854775808 (m + 9223372036854775808) = True := arithmetic
      let mag: Float.Model.magnitude (m + 9223372036854775808) = m := arithmetic
      Both (arithmetic [mag, fm]) (rewrite Float.Theory.unitsMag (m + 9223372036854775808), mag)

--| Representability: a whole number of units within the precision at its
--| size is a double. `±q × 2^e` units of 2^-1074, for `q ≤ 2^53` and below
--| 2^2098 units (2^1024, where the finite doubles end), round to a finite
--| double with exactly those units, whatever the zero sign.
-- The pattern is `gridBits q e`: `q`'s own pattern doubled `e` times.
theorem Float.Theory.roundGrid ∀ (s: Bool) (q e: Nat) (z: Bool)
    (hq: q ≤ 9007199254740992)
    (fin: q * Nat.pow 2 e < Nat.pow 2 2098):
    Float.Theory.FiniteBits (Float.Model.roundRatio (Int.signed s (q * Nat.pow 2 e)) 1 (-1074) z)
      ∧ (Float.Model.units (Float.Model.roundRatio (Int.signed s (q * Nat.pow 2 e)) 1 (-1074) z)
        = Int.signed s (q * Nat.pow 2 e)) :=
  Float.Theory.orCase
    (Float.Theory.zeroOrPos (q * Nat.pow 2 e))
    (n0 =>
      rewrite n0 then
        match s, z with
          | False, False | True => Both byComputing byComputing
          | True, False => Both byComputing byComputing
          | True, True => Both byComputing byComputing)
    (pn =>
      let m: Nat := Float.Theory.gridBits q e
      let um: Float.Theory.magUnits m = q * Nat.pow 2 e := Float.Theory.gridUnits q e hq
      let fm: m < 9218868437227405312 := Float.Theory.gridFinite q e hq fin
      let back: Float.Model.roundRatio (Int.signed s (Float.Theory.magUnits m)) 1 (-1074) s
        = (if s then m + 9223372036854775808 else m) :=
        Float.Theory.unitsRound (if s then m + 9223372036854775808 else m) m fm s byComputing
      let r: Float.Model.roundRatio (Int.signed s (q * Nat.pow 2 e)) 1 (-1074) z
        = (if s then m + 9223372036854775808 else m) :=
        rewrite Float.Theory.roundRatioSignIrrelevant 1
              (-1074)
              z
              s
              (Int.signed s (q * Nat.pow 2 e))
              (Float.Theory.signedNonzero s (q * Nat.pow 2 e) pn),
            um.flipped then
          back
      rewrite r, um.flipped then Float.Theory.unitsOfMagnitude m s fm)

theorem Float.Theory.leLessTrans ∀ (a b c: Nat) (x: a ≤ b) (y: b < c): a < c := arithmetic

theorem Float.Theory.wholeSignedForm ∀ (n: Int):
    Int.mul n (OfNat (Float.Model.pow2 1074)) = Int.signed (Int.isNeg n) (Int.natAbs n * Nat.pow 2 1074) :=
  match n with | OfNat _ | NegSucc _ => byComputing

--| A whole number `n` with `|n| ≤ 2^53`, as `n × 2^1074` units, rounds to
--| a finite double with exactly those units.
theorem Float.Theory.roundWholeUnits ∀ (n: Int) (z: Bool)
    (h: Int.natAbs n ≤ 9007199254740992):
    Float.Theory.FiniteBits (Float.Model.roundRatio (Int.mul n (OfNat (Float.Model.pow2 1074))) 1 (-1074) z)
      ∧ (Float.Model.units (Float.Model.roundRatio (Int.mul n (OfNat (Float.Model.pow2 1074))) 1 (-1074) z)
        = Int.mul n (OfNat (Float.Model.pow2 1074))) :=
  let bound: Int.natAbs n * Nat.pow 2 1074 < Nat.pow 2 2098 :=
    Float.Theory.leLessTrans
      (Int.natAbs n * Nat.pow 2 1074)
      (9007199254740992 * Nat.pow 2 1074)
      (Nat.pow 2 2098)
      (Nat.leMulRight (Int.natAbs n) 9007199254740992 (Nat.pow 2 1074) h)
      byComputing
  J
    (y w =>
      Float.Theory.FiniteBits (Float.Model.roundRatio y 1 (-1074) z)
        ∧ (Float.Model.units (Float.Model.roundRatio y 1 (-1074) z) = y))
    (Float.Theory.roundGrid (Int.isNeg n) (Int.natAbs n) 1074 z h bound)
    (Float.Theory.wholeSignedForm n).flipped

--| The same for `roundScaled n 0`, the double nearest the whole number `n`.
theorem Float.Theory.roundScaledWhole ∀ (n: Int) (z: Bool)
    (h: Int.natAbs n ≤ 9007199254740992):
    Float.Theory.FiniteBits (Float.Model.roundScaled n 0 z)
      ∧ (Float.Model.units (Float.Model.roundScaled n 0 z) = Int.mul n (OfNat (Float.Model.pow2 1074))) :=
  J
    (r w => Float.Theory.FiniteBits r ∧ (Float.Model.units r = Int.mul n (OfNat (Float.Model.pow2 1074))))
    (Float.Theory.roundWholeUnits n z h)
    (Float.Theory.roundWhole n z).flipped

theorem Float.Theory.cancelLessComm ∀ (a b c: Nat) (h: a * c < c * b): a < b :=
  Float.Theory.cancelLess a b c (J (y w => a * c < y) h (Nat.mulComm c b))

--| `floorDiv` of a size below `2^53 × p`: its quotient and the next whole
--| number are at most 2^53 in size, and the value is below the next one.
theorem Float.Theory.floorDivRange ∀ (s: Bool) (m p: Nat)
    (pp: 0 < p)
    (h: m < p * 9007199254740992):
    ((Int.natAbs (Float.Model.floorDiv s m p) ≤ 9007199254740992)
      ∧ (Int.natAbs (Int.add (Float.Model.floorDiv s m p) (OfNat 1)) ≤ 9007199254740992))
      ∧ (Int.less (Int.signed s m) (Int.mul (Int.add (Float.Model.floorDiv s m p) (OfNat 1)) (OfNat p)) = True) :=
  let q: Nat := Nat.divFuel m m p
  let low: q * p ≤ m := Nat.divFuelLe m m p
  let high: m < Succ q * p := Nat.divFuelBound m m p (Nat.nonzeroOfPos p pp) (Nat.leRefl m)
  match s with
    | False =>
      let f: Float.Model.floorDiv False m p = OfNat q := byComputing
      let qb: q < 9007199254740992 := Float.Theory.cancelLessComm q 9007199254740992 p (arithmetic [low, h])
      rewrite f then Both (Both (arithmetic [qb]) (arithmetic [qb])) (arithmetic [high, Float.Theory.succMul q p])
    | True =>
      Float.Theory.orCase
        (Float.Theory.boolCases (Nat.equal (q * p) m))
        (e =>
          let ex: q * p = m := Nat.equalSound (q * p) m e
          let f: Float.Model.floorDiv True m p = Int.neg (OfNat q) := rewrite e
          let qb: q < 9007199254740992 := Float.Theory.cancelLessComm q 9007199254740992 p (arithmetic [ex, h])
          let up: Int.mul (Int.add (Int.neg (OfNat q)) (OfNat 1)) (OfNat p)
            = Int.add (Int.neg (OfNat (q * p))) (OfNat p) :=
            algebra
          rewrite f, up then Both (Both (arithmetic [qb]) (arithmetic [qb])) (arithmetic [ex, pp]))
        (e =>
          let ne: q * p ≠ m := Nat.equalFalse (q * p) m e
          let f: Float.Model.floorDiv True m p = NegSucc q := rewrite e
          let qb: q < 9007199254740992 := Float.Theory.cancelLessComm q 9007199254740992 p (arithmetic [low, ne, h])
          let up: Int.mul (Int.add (NegSucc q) (OfNat 1)) (OfNat p) = Int.neg (OfNat (q * p)) := algebra
          rewrite f, up then Both (Both (arithmetic [qb]) (arithmetic [qb])) (arithmetic [low, ne]))

theorem Float.Theory.natAbsSigned ∀ (s: Bool) (k: Nat): Int.natAbs (Int.signed s k) = k := match s, k with
  | False, k => byComputing
  | True, Zero | Succ _ => byComputing

--| `|x|`'s key is its magnitude: clearing the sign of a valid pattern
--| leaves it below the sign bit.
theorem Float.Theory.absKeyBits ∀ (a: Nat)
    (v: Float.isValid a = True):
    Float.keyOf (Float.clearSignBits a) (Nat.leq 9223372036854775808 (Float.clearSignBits a))
      = OfNat (Float.Model.magnitude a) :=
  Float.Theory.orCase
    [goal := Float.keyOf (Float.clearSignBits a) (Nat.leq 9223372036854775808 (Float.clearSignBits a))
      = OfNat (Float.Model.magnitude a)]
    (Float.Theory.boolCases (Nat.leq 9223372036854775808 a))
    (c =>
      let low: Nat.leq 9223372036854775808 (a - 9223372036854775808) = False := arithmetic [Float.highBound a v c]
      rewrite c, low)
    (c => rewrite c, c)

theorem Float.Theory.absKey ∀ (x: Float): Float.orderKey (Float.abs x) = OfNat (Float.Model.magnitude x.bits) :=
  Float.Theory.absKeyBits x.bits x.valid

--| A double with `|x| < 2^53` is finite, with fewer than `2^53 × 2^1074` units either way.
theorem Float.Theory.absBelowUnits ∀ (x: Float)
    (small: Float.abs x < 9007199254740992.0):
    Float.Theory.FiniteBits x.bits
      ∧ (Int.natAbs (Float.Model.units x.bits) < Float.Model.pow2 1074 * 9007199254740992) :=
  let key: Float.orderKey 9007199254740992.0 = OfNat 4845873199050653696 := byComputing
  let below: Float.Model.magnitude x.bits < 4845873199050653696 := arithmetic [small, Float.Theory.absKey x, key]
  let top: Float.Theory.magUnits 4845873199050653696 = Float.Model.pow2 1074 * 9007199254740992 := byComputing
  Both
    (Nat.lessTrans (Float.Model.magnitude x.bits) 4845873199050653696 9218868437227405312 below byComputing)
    (rewrite Float.Theory.unitsMag x.bits, Float.Theory.natAbsSigned (Float.Model.signBit x.bits) then
      J
        (y w => Float.Theory.magUnits (Float.Model.magnitude x.bits) < y)
        (Float.Theory.magUnitsLess (Float.Model.magnitude x.bits) 4845873199050653696 below)
        top)

theorem Float.Theory.intLeLessAbsurd ∀ (a b: Int) (x: Int.leq a b = True) (y: Int.less b a = True): Void := arithmetic

--| Doubles whose units are in order are in the total order.
theorem Float.Theory.lessOfUnits ∀ (x y: Float)
    (h: Int.less (Float.Theory.units x) (Float.Theory.units y) = True):
    x < y :=
  Float.Theory.orCase
    (Float.Theory.boolCases (Int.leq (Float.Theory.key y.bits) (Float.Theory.key x.bits)))
    (c =>
      Void.impossible
        (Float.Theory.intLeLessAbsurd
          (Float.Theory.units y)
          (Float.Theory.units x)
          (Float.Theory.unitsMonoKey y.bits x.bits c)
          h))
    (c => (arithmetic [c]: Int.less (Float.Theory.key x.bits) (Float.Theory.key y.bits) = True))

theorem Float.Theory.isFiniteOf ∀ (x: Float) (h: Float.Theory.FiniteBits x.bits): Float.isFinite x = True :=
  let g: Nat.leq 9218868437227405312 (Float.Model.magnitude x.bits) = False := arithmetic [h]
  rewrite g

theorem Float.Theory.notSpecialOf ∀ (a: Nat) (h: Float.Theory.FiniteBits a): Float.Model.isSpecial a = False :=
  arithmetic [h]

theorem Float.Theory.addMulRight ∀ (f k: Int) (p: Nat):
    Int.add (Int.mul f (OfNat p)) (Int.mul k (OfNat p)) = Int.mul (Int.add f k) (OfNat p) :=
  algebra

--| The sum of two doubles of `f × 2^1074` and `k × 2^1074` units, for
--| whole numbers with `|f + k| ≤ 2^53`: exactly `f + k`.
theorem Float.Theory.addWhole ∀ (y c: Float) (f k: Int)
    (fy: Float.Theory.FiniteBits y.bits)
    (fc: Float.isFinite c = True)
    (uy: Float.Model.units y.bits = Int.mul f (OfNat (Float.Model.pow2 1074)))
    (uc: Float.Model.units c.bits = Int.mul k (OfNat (Float.Model.pow2 1074)))
    (h: Int.natAbs (Int.add f k) ≤ 9007199254740992):
    Float.Theory.units (y + c) = Int.mul (Int.add f k) (OfNat (Float.Model.pow2 1074)) :=
  let p: Nat := Float.Model.pow2 1074
  let z: Bool := Float.Model.signBit y.bits ∧ Float.Model.signBit c.bits
  let sumUnits: Int.add (Float.Theory.units y) (Float.Theory.units c) = Int.mul (Int.add f k) (OfNat p) :=
    Eq.trans (Eq.cong2 Int.add uy uc) (Float.Theory.addMulRight f k p)
  let sum: (y + c).bits = Float.Model.roundRatio (Int.mul (Int.add f k) (OfNat p)) 1 (-1074) z := calc (y + c).bits
    _ = (Float.ofBits
        (Float.Model.roundRatio (Int.add (Float.Theory.units y) (Float.Theory.units c)) 1 (-1074) z)).bits :=
      Eq.cong (w => w.bits) (Float.Theory.addFinite y c (Float.Theory.isFiniteOf y fy) fc)
    _ = Float.Model.roundRatio (Int.add (Float.Theory.units y) (Float.Theory.units c)) 1 (-1074) z :=
      Float.Theory.ofBitsBits
        (Float.Model.roundRatio (Int.add (Float.Theory.units y) (Float.Theory.units c)) 1 (-1074) z)
        (Float.Theory.roundRatioValid 1 (-1074) z byComputing (Int.add (Float.Theory.units y) (Float.Theory.units c)))
    _ = Float.Model.roundRatio (Int.mul (Int.add f k) (OfNat p)) 1 (-1074) z :=
      Eq.cong (u => Float.Model.roundRatio u 1 (-1074) z) sumUnits
  Eq.trans (Eq.cong Float.Model.units sum) (Float.Theory.roundWholeUnits (Int.add f k) z h).right

--| `x < floor x + 1.0` for `|x| < 2^53`: `floor x` and `floor x + 1.0` are
--| whole numbers of that size, so the sum is exact, and above `x`. From
--| 2^53 on, `x + 1.0` can round back down to `x`.
theorem Float.ltFloorAddOne ∀ (x: Float) (small: Float.abs x < 9007199254740992.0): x < Float.floor x + 1.0 :=
  let a: Nat := x.bits
  let s: Bool := Float.Model.signBit a
  let p: Nat := Float.Model.pow2 1074
  let n: Nat := Int.natAbs (Float.Model.units a)
  let f: Int := Float.Model.floorDiv s n p
  let fin: Float.Theory.FiniteBits a ∧ (n < p * 9007199254740992) := Float.Theory.absBelowUnits x small
  let range: ((Int.natAbs f ≤ 9007199254740992) ∧ (Int.natAbs (Int.add f (OfNat 1)) ≤ 9007199254740992))
    ∧ (Int.less (Int.signed s n) (Int.mul (Int.add f (OfNat 1)) (OfNat p)) = True) :=
    Float.Theory.floorDivRange s n p byComputing fin.right
  let fl: (Float.floor x).bits = Float.Model.roundScaled f 0 s :=
    Eq.trans (Float.Theory.floorOfBits x) (Float.Theory.floorFinite a (Float.Theory.notSpecialOf a fin.left))
  let fx: Float.Theory.FiniteBits (Float.floor x).bits
    ∧ (Float.Model.units (Float.floor x).bits = Int.mul f (OfNat p)) :=
    J
      (r w => Float.Theory.FiniteBits r ∧ (Float.Model.units r = Int.mul f (OfNat p)))
      (Float.Theory.roundScaledWhole f s range.left.left)
      fl.flipped
  let us: Float.Theory.units (Float.floor x + 1.0) = Int.mul (Int.add f (OfNat 1)) (OfNat p) :=
    Float.Theory.addWhole (Float.floor x) 1.0 f (OfNat 1) fx.left byComputing fx.right byComputing range.left.right
  Float.Theory.lessOfUnits x
    (Float.floor x + 1.0)
    (J
      (y w => Int.less y (Float.Theory.units (Float.floor x + 1.0)) = True)
      (J (y w => Int.less (Int.signed s n) y = True) range.right us.flipped)
      (Float.Theory.unitsSigned a))

test "Float.ltFloorAddOne" :=
  2.5 < Float.floor 2.5 + 1.0
    ∧ -2.5 < Float.floor -2.5 + 1.0
    ∧ -0.0 < Float.floor -0.0 + 1.0
    ∧ 9007199254740991.0 < Float.floor 9007199254740991.0 + 1.0
    ∧ ¬(9007199254740992.0 < Float.floor 9007199254740992.0 + 1.0)

theorem Float.Theory.signedFlip ∀ (s: Bool) (n: Nat): Int.signed s n = Int.neg (Int.signed (¬s) n) := match s with
  | False => algebra
  | True => byComputing

theorem Float.Theory.subOneMul ∀ (g: Int) (p: Nat):
    Int.mul (Int.add (Int.neg g) (Int.neg (OfNat 1))) (OfNat p) = Int.neg (Int.mul (Int.add g (OfNat 1)) (OfNat p)) :=
  algebra

theorem Float.Theory.natAbsNegLe ∀ (g: Int)
    (h: Int.natAbs g ≤ 9007199254740992):
    Int.natAbs (Int.neg g) ≤ 9007199254740992 :=
  arithmetic [h]

theorem Float.Theory.natAbsNegSuccLe ∀ (g: Int)
    (h: Int.natAbs (Int.add g (OfNat 1)) ≤ 9007199254740992):
    Int.natAbs (Int.add (Int.neg g) (Int.neg (OfNat 1))) ≤ 9007199254740992 :=
  arithmetic [h]

theorem Float.Theory.negLess ∀ (a b c d: Int)
    (h: Int.less b a = True)
    (ec: c = Int.neg a)
    (ed: d = Int.neg b):
    Int.less c d = True :=
  arithmetic [h, ec, ed]

--| `ceil x - 1.0 < x` for `|x| < 2^53`, where the difference is exact.
--| (`ceil x < x + 1.0` is false: `x + 1.0` rounds, and for `x` = 2^-60
--| both sides are `1.0`.)
theorem Float.ceilSubOneLt ∀ (x: Float) (small: Float.abs x < 9007199254740992.0): Float.ceil x - 1.0 < x :=
  let a: Nat := x.bits
  let s: Bool := Float.Model.signBit a
  let p: Nat := Float.Model.pow2 1074
  let n: Nat := Int.natAbs (Float.Model.units a)
  let g: Int := Float.Model.floorDiv (¬s) n p
  let fin: Float.Theory.FiniteBits a ∧ (n < p * 9007199254740992) := Float.Theory.absBelowUnits x small
  let range: ((Int.natAbs g ≤ 9007199254740992) ∧ (Int.natAbs (Int.add g (OfNat 1)) ≤ 9007199254740992))
    ∧ (Int.less (Int.signed (¬s) n) (Int.mul (Int.add g (OfNat 1)) (OfNat p)) = True) :=
    Float.Theory.floorDivRange (¬s) n p byComputing fin.right
  let cl: (Float.ceil x).bits = Float.Model.roundScaled (Int.neg g) 0 s :=
    Eq.trans (Float.Theory.ceilOfBits x) (Float.Theory.ceilFinite a (Float.Theory.notSpecialOf a fin.left))
  let cx: Float.Theory.FiniteBits (Float.ceil x).bits
    ∧ (Float.Model.units (Float.ceil x).bits = Int.mul (Int.neg g) (OfNat p)) :=
    J
      (r w => Float.Theory.FiniteBits r ∧ (Float.Model.units r = Int.mul (Int.neg g) (OfNat p)))
      (Float.Theory.roundScaledWhole (Int.neg g) s (Float.Theory.natAbsNegLe g range.left.left))
      cl.flipped
  let ud: Float.Theory.units (Float.ceil x - 1.0) = Int.mul (Int.add (Int.neg g) (Int.neg (OfNat 1))) (OfNat p) :=
    Eq.trans
      (Eq.cong Float.Theory.units (Float.subAddNeg (Float.ceil x) 1.0))
      (Float.Theory.addWhole
        (Float.ceil x)
        (-1.0)
        (Int.neg g)
        (Int.neg (OfNat 1))
        cx.left
        byComputing
        cx.right
        byComputing
        (Float.Theory.natAbsNegSuccLe g range.left.right))
  Float.Theory.lessOfUnits
    (Float.ceil x - 1.0)
    x
    (Float.Theory.negLess
      (Int.mul (Int.add g (OfNat 1)) (OfNat p))
      (Int.signed (¬s) n)
      (Float.Theory.units (Float.ceil x - 1.0))
      (Float.Theory.units x)
      range.right
      (Eq.trans ud (Float.Theory.subOneMul g p))
      (Eq.trans (Float.Theory.unitsSigned a).flipped (Float.Theory.signedFlip s n)))

test "Float.ceilSubOneLt" :=
  Float.ceil 2.5 - 1.0 < 2.5
    ∧ Float.ceil -2.5 - 1.0 < -2.5
    ∧ Float.ceil 0.0 - 1.0 < 0.0
    ∧ Float.ceil -9007199254740991.0 - 1.0 < -9007199254740991.0
    ∧ Float.ceil 8.673617379884035e-19 == 8.673617379884035e-19 + 1.0

-- Exact differences on a common grid

--| The exponent of a pattern's units: they are `2^expOf m × sigOf m`.
def Float.Theory.expOf (m: Nat): Nat := Nat.divFuel m m 4503599627370496 - 1

--| The significand of a pattern's units, below 2^53.
def Float.Theory.sigOf (m: Nat): Nat :=
  if Nat.equal (Nat.divFuel m m 4503599627370496) 0 then m
  else m - Nat.divFuel m m 4503599627370496 * 4503599627370496 + 4503599627370496

theorem Float.Theory.magUnitsShape ∀ (m: Nat):
    (Float.Theory.magUnits m = Nat.pow 2 (Float.Theory.expOf m) * Float.Theory.sigOf m)
      ∧ (Float.Theory.sigOf m < 9007199254740992) :=
  let e: Nat := Nat.divFuel m m 4503599627370496
  let low: e * 4503599627370496 ≤ m := Nat.divFuelLe m m 4503599627370496
  let high: m < Succ e * 4503599627370496 :=
    Nat.divFuelBound m m 4503599627370496 (Nat.nonzeroOfPos 4503599627370496 byComputing) (Nat.leRefl m)
  let split: Float.Theory.magUnits m
    = (if Nat.equal e 0 then m - e * 4503599627370496
       else Nat.pow 2 (e - 1) * (m - e * 4503599627370496 + 4503599627370496)) :=
    Float.Theory.magUnitsSplit m e low (arithmetic [high])
  Float.Theory.orCase
    [goal := (Float.Theory.magUnits m = Nat.pow 2 (Float.Theory.expOf m) * Float.Theory.sigOf m)
      ∧ (Float.Theory.sigOf m < 9007199254740992)]
    (Float.Theory.boolCases (Nat.equal e 0))
    (z =>
      let e0: e = 0 := Nat.equalSound e 0 z
      let sig: Float.Theory.sigOf m = m := rewrite z
      let ex: Float.Theory.expOf m = 0 := arithmetic [e0]
      let mu: Float.Theory.magUnits m = m := rewrite split, z then arithmetic [e0]
      Both
        (calc Float.Theory.magUnits m
          _ = m := mu
          _ = Nat.pow 2 0 * m := algebra
          _ = Nat.pow 2 (Float.Theory.expOf m) * Float.Theory.sigOf m :=
            Eq.cong2 (a b => Nat.pow 2 a * b) ex.flipped sig.flipped)
        (J (y w => y < 9007199254740992) (arithmetic [high, e0]: m < 9007199254740992) sig.flipped))
    (z =>
      let sig: Float.Theory.sigOf m = m - e * 4503599627370496 + 4503599627370496 := rewrite z
      let mu: Float.Theory.magUnits m = Nat.pow 2 (e - 1) * (m - e * 4503599627370496 + 4503599627370496) :=
        rewrite split, z
      Both
        (Eq.trans mu (Eq.cong (b => Nat.pow 2 (e - 1) * b) sig.flipped))
        (J
          (y w => y < 9007199254740992)
          (arithmetic [low, high]: m - e * 4503599627370496 + 4503599627370496 < 9007199254740992)
          sig.flipped))

--| `r` on the grid of `P`: from `r + Y × P = X × P` and `r ≤ Q × P`,
--| `r = (X - Y) × P` with `X - Y ≤ Q`.
theorem Float.Theory.gridSplit ∀ (r p x y q: Nat)
    (pp: 0 < p)
    (e: r + y * p = x * p)
    (b: r ≤ q * p):
    (r = (x - y) * p) ∧ (x - y ≤ q) :=
  let yx: y ≤ x := Float.Theory.cancelLe y x p pp (arithmetic [e])
  let split: x * p = (x - y) * p + y * p :=
    Eq.trans
      (Eq.cong (t => t * p) (arithmetic [yx]: x = (x - y) + y))
      (algebra: ((x - y) + y) * p = (x - y) * p + y * p)
  let re: r = (x - y) * p := arithmetic [e, split]
  Both re (Float.Theory.cancelLe (x - y) q p pp (arithmetic [re, b]))

theorem Float.Theory.powSplit ∀ (a b: Nat) (h: a ≤ b): Nat.pow 2 b = Nat.pow 2 (b - a) * Nat.pow 2 a :=
  Eq.trans (Eq.cong (Nat.pow 2) (arithmetic [h]: b = (b - a) + a)) (Nat.powAdd 2 (b - a) a)

theorem Float.Theory.gridExact ∀ (r d e: Nat) (s z: Bool)
    (re: r = d * Nat.pow 2 e)
    (hd: d ≤ 9007199254740992)
    (small: r < Nat.pow 2 2098):
    Float.Theory.FiniteBits (Float.Model.roundRatio (Int.signed s r) 1 (-1074) z)
      ∧ (Float.Model.units (Float.Model.roundRatio (Int.signed s r) 1 (-1074) z) = Int.signed s r) :=
  J
    (y w =>
      Float.Theory.FiniteBits (Float.Model.roundRatio (Int.signed s y) 1 (-1074) z)
        ∧ (Float.Model.units (Float.Model.roundRatio (Int.signed s y) 1 (-1074) z) = Int.signed s y))
    (Float.Theory.roundGrid s d e z hd (J (y w => y < Nat.pow 2 2098) small re))
    re.flipped

theorem Float.Theory.finiteUnitsBelow ∀ (m: Nat)
    (fm: m < 9218868437227405312):
    Float.Theory.magUnits m < Nat.pow 2 2098 :=
  J
    (y w => Float.Theory.magUnits m < y)
    (Float.Theory.magUnitsLess m 9218868437227405312 fm)
    (Eq.trans Float.Theory.unitsAtInfinity (Float.Theory.pow2Pow 2098))

--| Exactness on a common grid: a whole number `r` of units with
--| `r + k × B = j × A`, for the units `A` of a finite pattern and `B` of
--| another, and `r` at most both, is a double. Both `A` and `B` are
--| multiples of 2^E for the smaller of their exponents `E`, so `r` is too;
--| and `r` is at most the significand, below 2^53, of the one with that
--| exponent.
theorem Float.Theory.combinationExact ∀ (ma mb r j k: Nat) (s z: Bool)
    (fa: ma < 9218868437227405312)
    (e: r + k * Float.Theory.magUnits mb = j * Float.Theory.magUnits ma)
    (la: r ≤ Float.Theory.magUnits ma)
    (lb: r ≤ Float.Theory.magUnits mb):
    Float.Theory.FiniteBits (Float.Model.roundRatio (Int.signed s r) 1 (-1074) z)
      ∧ (Float.Model.units (Float.Model.roundRatio (Int.signed s r) 1 (-1074) z) = Int.signed s r) :=
  let ea: Nat := Float.Theory.expOf ma
  let eb: Nat := Float.Theory.expOf mb
  let qa: Nat := Float.Theory.sigOf ma
  let qb: Nat := Float.Theory.sigOf mb
  let sa: (Float.Theory.magUnits ma = Nat.pow 2 ea * qa) ∧ (qa < 9007199254740992) := Float.Theory.magUnitsShape ma
  let sb: (Float.Theory.magUnits mb = Nat.pow 2 eb * qb) ∧ (qb < 9007199254740992) := Float.Theory.magUnitsShape mb
  Float.Theory.orCase
    (Float.Theory.boolCases (Nat.leq ea eb))
    (c =>
      let p: Nat := Nat.pow 2 ea
      let bs: Float.Theory.magUnits mb = Nat.pow 2 (eb - ea) * qb * p :=
        rewrite sb.left, Float.Theory.powSplit ea eb c then algebra
      let as: Float.Theory.magUnits ma = qa * p := rewrite sa.left then algebra
      let ek: k * Float.Theory.magUnits mb = k * (Nat.pow 2 (eb - ea) * qb) * p := rewrite bs then algebra
      let ej: j * Float.Theory.magUnits ma = j * qa * p := rewrite as then algebra
      let g: (r = (j * qa - k * (Nat.pow 2 (eb - ea) * qb)) * p) ∧ (j * qa - k * (Nat.pow 2 (eb - ea) * qb) ≤ qa) :=
        Float.Theory.gridSplit r p
          (j * qa)
          (k * (Nat.pow 2 (eb - ea) * qb))
          qa
          (Nat.powSuccPos 1 ea)
          (arithmetic [e, ek, ej])
          (arithmetic [la, as])
      Float.Theory.gridExact r
        (j * qa - k * (Nat.pow 2 (eb - ea) * qb))
        ea
        s
        z
        g.left
        (arithmetic [g.right, sa.right])
        (Float.Theory.leLessTrans r
          (Float.Theory.magUnits ma)
          (Nat.pow 2 2098)
          la
          (Float.Theory.finiteUnitsBelow ma fa)))
    (c =>
      let p: Nat := Nat.pow 2 eb
      let as: Float.Theory.magUnits ma = Nat.pow 2 (ea - eb) * qa * p :=
        rewrite sa.left, Float.Theory.powSplit eb ea (arithmetic [c]) then algebra
      let bs: Float.Theory.magUnits mb = qb * p := rewrite sb.left then algebra
      let ek: k * Float.Theory.magUnits mb = k * qb * p := rewrite bs then algebra
      let ej: j * Float.Theory.magUnits ma = j * (Nat.pow 2 (ea - eb) * qa) * p := rewrite as then algebra
      let g: (r = (j * (Nat.pow 2 (ea - eb) * qa) - k * qb) * p) ∧ (j * (Nat.pow 2 (ea - eb) * qa) - k * qb ≤ qb) :=
        Float.Theory.gridSplit r p
          (j * (Nat.pow 2 (ea - eb) * qa))
          (k * qb)
          qb
          (Nat.powSuccPos 1 eb)
          (arithmetic [e, ek, ej])
          (arithmetic [lb, bs])
      Float.Theory.gridExact r
        (j * (Nat.pow 2 (ea - eb) * qa) - k * qb)
        eb
        s
        z
        g.left
        (arithmetic [g.right, sb.right])
        (Float.Theory.leLessTrans r
          (Float.Theory.magUnits ma)
          (Nat.pow 2 2098)
          la
          (Float.Theory.finiteUnitsBelow ma fa)))

-- The remainder

--| A finite pattern's size in units is its magnitude's units.
theorem Float.Theory.natAbsUnits ∀ (a: Nat):
    Int.natAbs (Float.Model.units a) = Float.Theory.magUnits (Float.Model.magnitude a) :=
  Eq.trans
    (Eq.cong Int.natAbs (Float.Theory.unitsMag a))
    (Float.Theory.natAbsSigned (Float.Model.signBit a) (Float.Theory.magUnits (Float.Model.magnitude a)))

--| What `remBits` computes for a finite pattern over a finite nonzero one.
theorem Float.Theory.remFiniteBits ∀ (a b: Nat)
    (fa: Float.Theory.FiniteBits a)
    (fb: Float.Theory.FiniteBits b)
    (zb: Float.Model.isZero b = False):
    Float.Model.remBits a b
      = Float.Model.roundScaled
        (Int.signed
          (Float.Model.signBit a)
          (Int.natAbs (Float.Model.units a)
            - Nat.divFuel
              (Int.natAbs (Float.Model.units a))
              (Int.natAbs (Float.Model.units a))
              (Int.natAbs (Float.Model.units b))
              * Int.natAbs (Float.Model.units b)))
        (-1074)
        (Float.Model.signBit a) :=
  let m: Nat := Int.natAbs (Float.Model.units a)
  let d: Nat := Int.natAbs (Float.Model.units b)
  let fin: Nat :=
    Float.Model.roundScaled
      (Int.signed (Float.Model.signBit a) (m - Nat.divFuel m m d * d))
      (-1074)
      (Float.Model.signBit a)
  calc Float.Model.remBits a b
    _ = (if Float.Model.isInfinite b then a else fin) :=
      Float.Theory.ifFalse
        (Float.Model.isNaN a ∨ Float.Model.isNaN b ∨ Float.Model.isInfinite a ∨ Float.Model.isZero b)
        9221120237041090560
        (if Float.Model.isInfinite b then a else fin)
        (Float.Theory.orFalse
          (Float.Model.isNaN a)
          (Float.Model.isNaN b ∨ Float.Model.isInfinite a ∨ Float.Model.isZero b)
          (Float.Theory.finiteNotNaN a fa)
          (Float.Theory.orFalse
            (Float.Model.isNaN b)
            (Float.Model.isInfinite a ∨ Float.Model.isZero b)
            (Float.Theory.finiteNotNaN b fb)
            (Float.Theory.orFalse
              (Float.Model.isInfinite a)
              (Float.Model.isZero b)
              (Float.Theory.finiteNotInfinite a fa)
              zb)))
    _ = fin := Float.Theory.ifFalse (Float.Model.isInfinite b) a fin (Float.Theory.finiteNotInfinite b fb)

--| The remainder of a finite pattern by a finite nonzero one: finite, of
--| units with the dividend's sign and a size below the divisor's.
theorem Float.Theory.remExact ∀ (a b: Nat)
    (fa: Float.Theory.FiniteBits a)
    (fb: Float.Theory.FiniteBits b)
    (zb: Float.Model.isZero b = False):
    (Float.Theory.FiniteBits (Float.Model.remBits a b)
      ∧ (Float.Model.remBits a b
        = Float.Model.roundRatio
          (Int.signed (Float.Model.signBit a) (Int.natAbs (Float.Model.units (Float.Model.remBits a b))))
          1
          (-1074)
          (Float.Model.signBit a)))
      ∧ (Int.natAbs (Float.Model.units (Float.Model.remBits a b)) < Int.natAbs (Float.Model.units b)) :=
  let s: Bool := Float.Model.signBit a
  let m: Nat := Int.natAbs (Float.Model.units a)
  let d: Nat := Int.natAbs (Float.Model.units b)
  let q: Nat := Nat.divFuel m m d
  let r: Nat := m - q * d
  let mm: m = Float.Theory.magUnits (Float.Model.magnitude a) := Float.Theory.natAbsUnits a
  let dd: d = Float.Theory.magUnits (Float.Model.magnitude b) := Float.Theory.natAbsUnits b
  let magPos: 0 < Float.Model.magnitude b := arithmetic [zb]
  let dpos: 0 < d := J (y w => 0 < y) (Float.Theory.magUnitsLess 0 (Float.Model.magnitude b) magPos) dd.flipped
  let low: q * d ≤ m := Nat.divFuelLe m m d
  let high: m < Succ q * d := Nat.divFuelBound m m d (Nat.nonzeroOfPos d dpos) (Nat.leRefl m)
  let lt: r < d := arithmetic [low, high, Float.Theory.succMul q d]
  let qd: q * d = q * Float.Theory.magUnits (Float.Model.magnitude b) := Eq.cong (t => q * t) dd
  let ex: (Float.Theory.FiniteBits (Float.Model.roundRatio (Int.signed s r) 1 (-1074) s))
    ∧ (Float.Model.units (Float.Model.roundRatio (Int.signed s r) 1 (-1074) s) = Int.signed s r) :=
    Float.Theory.combinationExact
      (Float.Model.magnitude a)
      (Float.Model.magnitude b)
      r
      1
      q
      s
      s
      fa
      (arithmetic [low, mm, qd])
      (arithmetic [low, mm])
      (arithmetic [lt, dd])
  let rb: Float.Model.remBits a b = Float.Model.roundRatio (Int.signed s r) 1 (-1074) s :=
    Float.Theory.remFiniteBits a b fa fb zb
  let size: Int.natAbs (Float.Model.units (Float.Model.remBits a b)) = r := calc Int.natAbs
    (Float.Model.units (Float.Model.remBits a b))
    _ = Int.natAbs (Float.Model.units (Float.Model.roundRatio (Int.signed s r) 1 (-1074) s)) :=
      Eq.cong (w => Int.natAbs (Float.Model.units w)) rb
    _ = Int.natAbs (Int.signed s r) := Eq.cong Int.natAbs ex.right
    _ = r := Float.Theory.natAbsSigned s r
  J
    (y w =>
      (Float.Theory.FiniteBits (Float.Model.remBits a b)
        ∧ (Float.Model.remBits a b = Float.Model.roundRatio (Int.signed s y) 1 (-1074) s))
        ∧ (y < d))
    (Both (Both (J (w v => Float.Theory.FiniteBits w) ex.left rb.flipped) rb) lt)
    size.flipped

theorem Float.Theory.modelNotZero ∀ (y: Float) (zy: Float.isZero y = False): Float.Model.isZero y.bits = False :=
  let b: Nat := y.bits
  let n0: Nat.equal b 0 = False := Float.Theory.orLeftFalse (Nat.equal b 0) (Nat.equal b 9223372036854775808) zy
  let n1: Nat.equal b 9223372036854775808 = False :=
    Float.Theory.orRightFalse (Nat.equal b 0) (Nat.equal b 9223372036854775808) zy
  Float.Theory.orCase
    [goal := Float.Model.isZero b = False]
    (Float.Theory.boolCases (Nat.leq 9223372036854775808 b))
    (c => rewrite c then arithmetic [c, n1])
    (c => rewrite c then n0)

theorem Float.Theory.magLessOfUnits ∀ (m n: Nat) (h: Float.Theory.magUnits m < Float.Theory.magUnits n): m < n :=
  Float.Theory.orCase
    (Float.Theory.boolCases (Nat.leq n m))
    (c =>
      Void.impossible
        (Float.Theory.leLessAbsurd
          (Float.Theory.magUnits n)
          (Float.Theory.magUnits m)
          (Float.Theory.magUnitsLe n m (Float.Theory.atLeastOf n m c))
          h))
    (c => arithmetic [c])

--| `x % y` on finite doubles, `y` not a zero: their bits' remainder.
theorem Float.Theory.remOfBits ∀ (x y: Float)
    (fx: Float.isFinite x = True)
    (fy: Float.isFinite y = True)
    (zy: Float.isZero y = False):
    (x % y).bits = Float.Model.remBits x.bits y.bits :=
  let e: x % y = Float.ofBits (Float.Model.remBits x.bits y.bits) := match x, y with
    | { bits = a, valid = p }, { bits = b, valid = q } => byComputing
  let ex :=
    Float.Theory.remExact x.bits y.bits
      (Float.Theory.finiteBits x fx)
      (Float.Theory.finiteBits y fy)
      (Float.Theory.modelNotZero y zy)
  Eq.trans
    (Eq.cong (q => q.bits) e)
    (Float.Theory.ofBitsBits
      (Float.Model.remBits x.bits y.bits)
      (Float.Theory.validTo
        (Float.Model.remBits x.bits y.bits)
        (Float.Model.roundRatio
          (Int.signed (Float.Model.signBit x.bits) (Int.natAbs (Float.Model.units (Float.Model.remBits x.bits y.bits))))
          1
          (-1074)
          (Float.Model.signBit x.bits))
        ex.left.right
        (Float.Theory.roundRatioValid 1
          (-1074)
          (Float.Model.signBit x.bits)
          byComputing
          (Int.signed
            (Float.Model.signBit x.bits)
            (Int.natAbs (Float.Model.units (Float.Model.remBits x.bits y.bits)))))))

theorem Float.Theory.absLessOf ∀ (u v: Float)
    (h: Float.Model.magnitude u.bits < Float.Model.magnitude v.bits):
    Float.abs u < Float.abs v :=
  arithmetic [Float.Theory.absKey u, Float.Theory.absKey v, h]

theorem Float.Theory.signedNonneg ∀ (k: Nat): Int.leq (OfNat 0) (Int.signed False k) = True := arithmetic

theorem Float.Theory.signedNonpos ∀ (k: Nat): Int.leq (Int.signed True k) (Int.signed True 0) = True := arithmetic

--| `|x % y| < |y|` for finite `x` and finite nonzero `y`: the remainder
--| `x - n × y`, for the whole `n` of `x / y` truncated, is exact, so it is
--| below `y` in size as the exact one is.
-- Exact because `x` and `y` are multiples of 2^E for the smaller of their
-- exponents `E`, and so is the remainder, which is at most both of them
-- (`Float.Theory.combinationExact`).
theorem Float.remAbsLt ∀ (x y: Float)
    (fx: Float.isFinite x = True)
    (fy: Float.isFinite y = True)
    (zy: Float.isZero y = False):
    Float.abs (x % y) < Float.abs y :=
  let a: Nat := x.bits
  let b: Nat := y.bits
  let ex :=
    Float.Theory.remExact a b
      (Float.Theory.finiteBits x fx)
      (Float.Theory.finiteBits y fy)
      (Float.Theory.modelNotZero y zy)
  let rb: (x % y).bits = Float.Model.remBits a b := Float.Theory.remOfBits x y fx fy zy
  let units: Float.Theory.magUnits (Float.Model.magnitude (Float.Model.remBits a b))
    < Float.Theory.magUnits (Float.Model.magnitude b) :=
    J
      (u w => u < Float.Theory.magUnits (Float.Model.magnitude b))
      (J (u w => Int.natAbs (Float.Model.units (Float.Model.remBits a b)) < u) ex.right (Float.Theory.natAbsUnits b))
      (Float.Theory.natAbsUnits (Float.Model.remBits a b))
  let mags: Float.Model.magnitude (x % y).bits < Float.Model.magnitude b :=
    J
      (r w => Float.Model.magnitude r < Float.Model.magnitude b)
      (Float.Theory.magLessOfUnits (Float.Model.magnitude (Float.Model.remBits a b)) (Float.Model.magnitude b) units)
      rb.flipped
  Float.Theory.absLessOf (x % y) y mags

theorem Float.Theory.signSetOf ∀ (b: Nat)
    (h: Int.leq (Float.Theory.key b) (NegSucc 0) = True):
    Nat.leq 9223372036854775808 b = True :=
  Float.Theory.orCase (Float.Theory.boolCases (Nat.leq 9223372036854775808 b)) (c => c) (c =>
    Void.impossible
      (Float.Theory.intLeLessAbsurd (Float.Theory.key b) (NegSucc 0) h (arithmetic [Float.Theory.keyClear b c])))

--| The key of `x % y` for finite `x` and finite nonzero `y`: a rounding of
--| a whole number of units with `x`'s sign.
theorem Float.Theory.remKey ∀ (x y: Float)
    (fx: Float.isFinite x = True)
    (fy: Float.isFinite y = True)
    (zy: Float.isZero y = False) (s: Bool)
    (sx: Nat.leq 9223372036854775808 x.bits = s):
    Float.orderKey (x % y)
      = Float.Theory.roundKey
        (Int.signed s (Int.natAbs (Float.Model.units (Float.Model.remBits x.bits y.bits))))
        1
        (-1074)
        s :=
  let ex :=
    Float.Theory.remExact x.bits y.bits
      (Float.Theory.finiteBits x fx)
      (Float.Theory.finiteBits y fy)
      (Float.Theory.modelNotZero y zy)
  let k: Nat := Int.natAbs (Float.Model.units (Float.Model.remBits x.bits y.bits))
  calc Float.Theory.key (x % y).bits
    _ = Float.Theory.key (Float.Model.remBits x.bits y.bits) :=
      Eq.cong Float.Theory.key (Float.Theory.remOfBits x y fx fy zy)
    _ = Float.Theory.key
        (Float.Model.roundRatio (Int.signed (Float.Model.signBit x.bits) k) 1 (-1074) (Float.Model.signBit x.bits)) :=
      Eq.cong Float.Theory.key ex.left.right
    _ = Float.Theory.key (Float.Model.roundRatio (Int.signed s k) 1 (-1074) s) :=
      Eq.cong (t => Float.Theory.key (Float.Model.roundRatio (Int.signed t k) 1 (-1074) t)) sx

--| `x % y` has `x`'s sign: `0.0 <= x % y` when `0.0 <= x`.
theorem Float.remNonneg ∀ (x y: Float)
    (fx: Float.isFinite x = True)
    (fy: Float.isFinite y = True)
    (zy: Float.isZero y = False)
    (h: 0.0 <= x):
    0.0 <= x % y :=
  let k: Nat := Int.natAbs (Float.Model.units (Float.Model.remBits x.bits y.bits))
  Float.Theory.leqVia
    (Float.orderKey 0.0)
    (Float.orderKey (x % y))
    (Float.Theory.roundKey (OfNat 0) 1 (-1074) False)
    (Float.Theory.roundKey (Int.signed False k) 1 (-1074) False)
    byComputing
    (Float.Theory.remKey x y fx fy zy False (Float.Theory.signClear x.bits h))
    (Float.Theory.roundKeyMonoLe 1
      (-1074)
      False
      False
      byComputing
      (OfNat 0)
      (Int.signed False k)
      (Float.Theory.signedNonneg k)
      (w => w))

--| `x % y <= -0.0` when `x <= -0.0`.
theorem Float.remNonpos ∀ (x y: Float)
    (fx: Float.isFinite x = True)
    (fy: Float.isFinite y = True)
    (zy: Float.isZero y = False)
    (h: x <= -0.0):
    x % y <= -0.0 :=
  let k: Nat := Int.natAbs (Float.Model.units (Float.Model.remBits x.bits y.bits))
  Float.Theory.leqVia
    (Float.orderKey (x % y))
    (Float.orderKey (-0.0))
    (Float.Theory.roundKey (Int.signed True k) 1 (-1074) True)
    (Float.Theory.roundKey (Int.signed True 0) 1 (-1074) True)
    (Float.Theory.remKey x y fx fy zy True (Float.Theory.signSetOf x.bits h))
    byComputing
    (Float.Theory.roundKeyMonoLe 1
      (-1074)
      True
      True
      byComputing
      (Int.signed True k)
      (Int.signed True 0)
      (Float.Theory.signedNonpos k)
      (w => w))

test "Float.remAbsLt" :=
  Float.abs (5.5 % 2.0) < Float.abs 2.0
    ∧ Float.abs (-5.5 % 2.0) < Float.abs 2.0
    ∧ Float.abs (1e300 % 3e-300) < 3e-300
    ∧ Float.abs (5e-324 % -1e300) < 1e300
    ∧ 0.0 <= 7.0 % -3.0
    ∧ -7.0 % 3.0 <= -0.0
    ∧ -6.0 % 3.0 == -0.0

-- Sterbenz's lemma

theorem Float.Theory.negFromBits ∀ (y: Float) (b: Bool)
    (h: Float.isNaN y = b)
    (e: b = False):
    (Float.negFrom y b h).bits = Float.flipSignBits y.bits :=
  match b with | False => byComputing

--| `-y` flips the sign bit of every double but the NaN.
theorem Float.Theory.negBits ∀ (y: Float) (n: Float.isNaN y = False): (-y).bits = Float.flipSignBits y.bits :=
  Float.Theory.negFromBits y (Float.isNaN y) byComputing n

theorem Float.Theory.positiveMag ∀ (x: Float) (pos: 0.0 < x): Float.Model.magnitude x.bits = x.bits :=
  rewrite Float.Theory.positiveSignClear x pos

theorem Float.Theory.positiveUnits ∀ (x: Float)
    (pos: 0.0 < x):
    Float.Theory.units x = OfNat (Float.Theory.magUnits x.bits) :=
  rewrite Float.Theory.positiveSignClear x pos

--| `-y` for a positive finite `y`: finite, of `-units y` units, sign bit set.
theorem Float.Theory.negPositive ∀ (y: Float)
    (pos: 0.0 < y)
    (fy: Float.isFinite y = True):
    ((-y).bits = y.bits + 9223372036854775808)
      ∧ (Float.Theory.FiniteBits (-y).bits
        ∧ (Float.Theory.units (-y) = Int.neg (OfNat (Float.Theory.magUnits y.bits)))) :=
  let fin: y.bits < 9218868437227405312 :=
    J (m w => m < 9218868437227405312) (Float.Theory.finiteBits y fy) (Float.Theory.positiveMag y pos)
  let bits: (-y).bits = y.bits + 9223372036854775808 :=
    Eq.trans
      (Float.Theory.negBits y (Float.Theory.finiteNotNaN y.bits (Float.Theory.finiteBits y fy)))
      (Float.flipLow y.bits (Float.Theory.positiveSignClear y pos))
  Both bits
    (J
      (b w => Float.Theory.FiniteBits b ∧ (Float.Model.units b = Int.neg (OfNat (Float.Theory.magUnits y.bits))))
      (Float.Theory.unitsOfMagnitude y.bits True fin)
      bits.flipped)

theorem Float.Theory.lessLe ∀ (a b c: Nat) (x: a < b) (y: b ≤ c): a ≤ c := arithmetic

theorem Float.Theory.belowOf ∀ (a b: Nat) (c: Nat.leq a b = False): b < a := arithmetic [c]

theorem Float.Theory.lessToLe ∀ (a: Nat) (h: a < 9007199254740992): a ≤ 9007199254740992 := arithmetic [h]

theorem Float.Theory.subSignedLe ∀ (u v: Nat)
    (c: Nat.leq v u = True):
    Int.signed False (u - v) = Int.add (OfNat u) (Int.neg (OfNat v)) :=
  arithmetic [c]

theorem Float.Theory.subSignedGt ∀ (u v: Nat)
    (c: Nat.leq v u = False):
    Int.signed True (v - u) = Int.add (OfNat u) (Int.neg (OfNat v)) :=
  arithmetic [c]

theorem Float.Theory.subAddBack ∀ (u v: Nat) (c: v ≤ u): u - v + 1 * v = 1 * u := arithmetic [c]

theorem Float.Theory.subLeSelf ∀ (u v: Nat): u - v ≤ u := arithmetic

theorem Float.Theory.subLeOf ∀ (u v: Nat) (h: u ≤ v + v): u - v ≤ v := arithmetic [h]

theorem Float.Theory.leOfLeqFalse ∀ (u v: Nat) (c: Nat.leq v u = False): u ≤ v := arithmetic [c]

theorem Float.Theory.addSelfSigned ∀ (i: Int) (v: Nat) (h: i = OfNat v): Int.add i i = Int.signed False (v + v) :=
  arithmetic [h]

theorem Float.Theory.natLeOfInt ∀ (a b: Int) (ua ub: Nat)
    (k: Int.leq a b = True)
    (ea: a = OfNat ua)
    (eb: b = OfNat ub):
    ua ≤ ub :=
  arithmetic [k, ea, eb]

theorem Float.Theory.doubleShape ∀ (v e q: Nat) (h: v = Nat.pow 2 e * q): v + v = q * Nat.pow 2 (Succ e) :=
  rewrite h, Nat.powSucc 2 e then algebra

--| For positive finite `x` and `y`, `x <= y + y` bounds `x`'s units by
--| twice `y`'s: `y + y` is exact, or so large that every finite double is
--| below it.
theorem Float.Theory.leDouble ∀ (x y: Float)
    (px: 0.0 < x)
    (py: 0.0 < y)
    (fx: Float.isFinite x = True)
    (fy: Float.isFinite y = True)
    (h: x <= y + y):
    Float.Theory.magUnits x.bits ≤ Float.Theory.magUnits y.bits + Float.Theory.magUnits y.bits :=
  let v: Nat := Float.Theory.magUnits y.bits
  Float.Theory.orCase
    (Float.Theory.boolCases (Nat.leq (Nat.pow 2 2098) (v + v)))
    (c =>
      Float.Theory.lessLe
        (Float.Theory.magUnits x.bits)
        (Nat.pow 2 2098)
        (v + v)
        (Float.Theory.finiteUnitsBelow x.bits
          (J (m w => m < 9218868437227405312) (Float.Theory.finiteBits x fx) (Float.Theory.positiveMag x px)))
        (Float.Theory.atLeastOf (Nat.pow 2 2098) (v + v) c))
    (c =>
      let sh: (v = Nat.pow 2 (Float.Theory.expOf y.bits) * Float.Theory.sigOf y.bits)
        ∧ (Float.Theory.sigOf y.bits < 9007199254740992) :=
        Float.Theory.magUnitsShape y.bits
      let g: Float.Theory.FiniteBits (Float.Model.roundRatio (Int.signed False (v + v)) 1 (-1074) False)
        ∧ (Float.Model.units (Float.Model.roundRatio (Int.signed False (v + v)) 1 (-1074) False)
          = Int.signed False (v + v)) :=
        Float.Theory.gridExact
          (v + v)
          (Float.Theory.sigOf y.bits)
          (Succ (Float.Theory.expOf y.bits))
          False
          False
          (Float.Theory.doubleShape v (Float.Theory.expOf y.bits) (Float.Theory.sigOf y.bits) sh.left)
          (Float.Theory.lessToLe (Float.Theory.sigOf y.bits) sh.right)
          (Float.Theory.belowOf (Nat.pow 2 2098) (v + v) c)
      let uy: Float.Theory.units y = OfNat v := Float.Theory.positiveUnits y py
      let sy: Float.Model.signBit y.bits = False := Float.Theory.positiveSignClear y py
      let sum: (y + y).bits = Float.Model.roundRatio (Int.signed False (v + v)) 1 (-1074) False := calc (y + y).bits
        _ = (Float.ofBits
            (Float.Model.roundRatio
              (Int.add (Float.Theory.units y) (Float.Theory.units y))
              1
              (-1074)
              (Float.Model.signBit y.bits ∧ Float.Model.signBit y.bits))).bits :=
          Eq.cong (w => w.bits) (Float.Theory.addFinite y y fy fy)
        _ = Float.Model.roundRatio
            (Int.add (Float.Theory.units y) (Float.Theory.units y))
            1
            (-1074)
            (Float.Model.signBit y.bits ∧ Float.Model.signBit y.bits) :=
          Float.Theory.ofBitsBits
            (Float.Model.roundRatio
              (Int.add (Float.Theory.units y) (Float.Theory.units y))
              1
              (-1074)
              (Float.Model.signBit y.bits ∧ Float.Model.signBit y.bits))
            (Float.Theory.roundRatioValid 1
              (-1074)
              (Float.Model.signBit y.bits ∧ Float.Model.signBit y.bits)
              byComputing
              (Int.add (Float.Theory.units y) (Float.Theory.units y)))
        _ = Float.Model.roundRatio (Int.signed False (v + v)) 1 (-1074) False :=
          Eq.cong2
            (n z => Float.Model.roundRatio n 1 (-1074) z)
            (Float.Theory.addSelfSigned (Float.Theory.units y) v uy)
            (rewrite sy: (Float.Model.signBit y.bits ∧ Float.Model.signBit y.bits) = False)
      let uyy: Float.Theory.units (y + y) = OfNat (v + v) := Eq.trans (Eq.cong Float.Model.units sum) g.right
      let k: Int.leq (Float.Theory.units x) (Float.Theory.units (y + y)) = True :=
        Float.Theory.unitsMonoKey x.bits (y + y).bits h
      Float.Theory.natLeOfInt
        (Float.Model.units x.bits)
        (Float.Model.units (y + y).bits)
        (Float.Theory.magUnits x.bits)
        (v + v)
        k
        (Float.Theory.positiveUnits x px)
        uyy)

--| The difference of two patterns' units, each at most twice the other, is
--| a double: Sterbenz's lemma on units.
theorem Float.Theory.sterbenzUnits ∀ (ma mb: Nat) (z: Bool)
    (fa: ma < 9218868437227405312)
    (fb: mb < 9218868437227405312)
    (h1: Float.Theory.magUnits ma ≤ Float.Theory.magUnits mb + Float.Theory.magUnits mb)
    (h2: Float.Theory.magUnits mb ≤ Float.Theory.magUnits ma + Float.Theory.magUnits ma):
    Float.Model.units
      (Float.Model.roundRatio
        (Int.add (OfNat (Float.Theory.magUnits ma)) (Int.neg (OfNat (Float.Theory.magUnits mb))))
        1
        (-1074)
        z)
      = Int.add (OfNat (Float.Theory.magUnits ma)) (Int.neg (OfNat (Float.Theory.magUnits mb))) :=
  let u: Nat := Float.Theory.magUnits ma
  let v: Nat := Float.Theory.magUnits mb
  Float.Theory.orCase
    (Float.Theory.boolCases (Nat.leq v u))
    (c =>
      let ex: (Float.Theory.FiniteBits (Float.Model.roundRatio (Int.signed False (u - v)) 1 (-1074) z))
        ∧ (Float.Model.units (Float.Model.roundRatio (Int.signed False (u - v)) 1 (-1074) z)
          = Int.signed False (u - v)) :=
        Float.Theory.combinationExact ma mb
          (u - v)
          1
          1
          False
          z
          fa
          (Float.Theory.subAddBack u v (Float.Theory.atLeastOf v u c))
          (Float.Theory.subLeSelf u v)
          (Float.Theory.subLeOf u v h1)
      J (n w => Float.Model.units (Float.Model.roundRatio n 1 (-1074) z) = n) ex.right (Float.Theory.subSignedLe u v c))
    (c =>
      let ex: (Float.Theory.FiniteBits (Float.Model.roundRatio (Int.signed True (v - u)) 1 (-1074) z))
        ∧ (Float.Model.units (Float.Model.roundRatio (Int.signed True (v - u)) 1 (-1074) z)
          = Int.signed True (v - u)) :=
        Float.Theory.combinationExact mb ma
          (v - u)
          1
          1
          True
          z
          fb
          (Float.Theory.subAddBack v u (Float.Theory.leOfLeqFalse u v c))
          (Float.Theory.subLeSelf v u)
          (Float.Theory.subLeOf v u h2)
      J (n w => Float.Model.units (Float.Model.roundRatio n 1 (-1074) z) = n) ex.right (Float.Theory.subSignedGt u v c))

--| Sterbenz's lemma: for positive finite `x` and `y` within a factor of two
--| of each other (`x <= y + y` and `y <= x + x`), `x - y` is exact.
-- Both are multiples of 2^E for the smaller of their exponents, and so is
-- the difference, which is at most the smaller of the two
-- (`Float.Theory.combinationExact`).
theorem Float.sterbenz ∀ (x y: Float)
    (px: 0.0 < x)
    (py: 0.0 < y)
    (fx: Float.isFinite x = True)
    (fy: Float.isFinite y = True)
    (hx: x <= y + y)
    (hy: y <= x + x):
    Float.Theory.units (x - y) = Int.sub (Float.Theory.units x) (Float.Theory.units y) :=
  let u: Nat := Float.Theory.magUnits x.bits
  let v: Nat := Float.Theory.magUnits y.bits
  let ny := Float.Theory.negPositive y py fy
  let zz: Bool := Float.Model.signBit x.bits ∧ Float.Model.signBit (-y).bits
  let ux: Float.Theory.units x = OfNat u := Float.Theory.positiveUnits x px
  let uy: Float.Theory.units y = OfNat v := Float.Theory.positiveUnits y py
  let finx: x.bits < 9218868437227405312 :=
    J (m w => m < 9218868437227405312) (Float.Theory.finiteBits x fx) (Float.Theory.positiveMag x px)
  let finy: y.bits < 9218868437227405312 :=
    J (m w => m < 9218868437227405312) (Float.Theory.finiteBits y fy) (Float.Theory.positiveMag y py)
  calc Float.Theory.units (x - y)
    _ = Float.Theory.units (x + (-y)) := Eq.cong Float.Theory.units (Float.subAddNeg x y)
    _ = Float.Model.units
        (Float.Model.roundRatio (Int.add (Float.Theory.units x) (Float.Theory.units (-y))) 1 (-1074) zz) :=
      Eq.trans
        (Eq.cong Float.Theory.units (Float.Theory.addFinite x (-y) fx (Float.Theory.isFiniteOf (-y) ny.right.left)))
        (Eq.cong Float.Model.units
          (Float.Theory.ofBitsBits
            (Float.Model.roundRatio (Int.add (Float.Theory.units x) (Float.Theory.units (-y))) 1 (-1074) zz)
            (Float.Theory.roundRatioValid 1
              (-1074)
              zz
              byComputing
              (Int.add (Float.Theory.units x) (Float.Theory.units (-y))))))
    _ = Float.Model.units (Float.Model.roundRatio (Int.add (OfNat u) (Int.neg (OfNat v))) 1 (-1074) zz) :=
      Eq.cong (n => Float.Model.units (Float.Model.roundRatio n 1 (-1074) zz)) (Eq.cong2 Int.add ux ny.right.right)
    _ = Int.add (OfNat u) (Int.neg (OfNat v)) :=
      Float.Theory.sterbenzUnits x.bits y.bits zz finx finy
        (Float.Theory.leDouble x y px py fx fy hx)
        (Float.Theory.leDouble y x py px fy fx hy)
    _ = Int.sub (Float.Theory.units x) (Float.Theory.units y) := arithmetic [ux, uy]

test "Float.sterbenz" :=
  Float.Theory.units (0.3 - 0.2) == Int.sub (Float.Theory.units 0.3) (Float.Theory.units 0.2)
    ∧ Float.Theory.units (359.9 - 180.0) == Int.sub (Float.Theory.units 359.9) (Float.Theory.units 180.0)
    ∧ Float.Theory.units (1e-310 - 6e-311) == Int.sub (Float.Theory.units 1e-310) (Float.Theory.units 6e-311)
    ∧ ¬(Float.Theory.units (1.0 - 1e-17) == Int.sub (Float.Theory.units 1.0) (Float.Theory.units 1e-17))

-- Sums between two doubles

theorem Float.Theory.overflowAbsurd ∀ (o x b: Nat) (eb: b = x * 1) (h1: 1 * o ≤ b) (h2: x < o): Void :=
  arithmetic [eb, h1, h2]

theorem Float.Theory.atInfinity ∀ (r: Nat)
    (c: Nat.leq 9218868437227405312 r = True)
    (b: r ≤ 9218868437227405312):
    r = 9218868437227405312 :=
  arithmetic [c, b]

--| A positive number of units below the overflow threshold rounds to a finite pattern.
theorem Float.Theory.magnitudeFinite ∀ (x: Nat)
    (px: 0 < x)
    (h: x < Float.Theory.overflowUnits):
    Float.Model.roundMagnitude False x 1 (OfNat 0) < 9218868437227405312 :=
  let r: Nat := Float.Model.roundMagnitude False x 1 (OfNat 0)
  let spec: Float.Theory.RoundsTo (Float.Model.scaleUp x (OfNat 0)) (Float.Model.scaleDown 1 (OfNat 0)) r :=
    Float.Theory.roundMagnitudeSpec x 1 (OfNat 0) px byComputing
  Float.Theory.orCase
    (Float.Theory.boolCases (Nat.leq 9218868437227405312 r))
    (c =>
      Void.impossible
        (Float.Theory.overflowAbsurd Float.Theory.overflowUnits x
          (Float.Model.scaleUp x (OfNat 0))
          byComputing
          (spec.overflow (Float.Theory.atInfinity r c spec.bounded))
          h))
    (c => Float.Theory.belowInfinity r c)

--| A sum of units below the overflow threshold in size rounds to a finite
--| double.
theorem Float.Theory.roundFinite ∀ (num: Int) (z: Bool)
    (h: Int.natAbs num < Float.Theory.overflowUnits):
    Float.Theory.FiniteBits (Float.Model.roundRatio num 1 (-1074) z) :=
  match num with
    | OfNat Zero =>
      match z with
        | True | False => byComputing
    | OfNat (Succ k) =>
      J
        (r w => Float.Theory.FiniteBits r)
        (Float.Theory.unitsOfMagnitude
          (Float.Model.roundMagnitude False (Succ k) 1 (OfNat 0))
          False
          (Float.Theory.magnitudeFinite (Succ k) byComputing h)).left
        (Float.Theory.roundRatioOfPos 1 (-1074) z (Succ k) byComputing).flipped
    | NegSucc k =>
      J
        (r w => Float.Theory.FiniteBits r)
        (Float.Theory.unitsOfMagnitude
          (Float.Model.roundMagnitude False (Succ k) 1 (OfNat 0))
          True
          (Float.Theory.magnitudeFinite (Succ k) byComputing h)).left
        (Float.Theory.roundRatioOfNeg 1 (-1074) z (Succ k) byComputing).flipped

--| The bits of a sum of finite doubles: their units' sum, rounded.
theorem Float.Theory.addBitsOf ∀ (x c: Float)
    (fx: Float.isFinite x = True)
    (fc: Float.isFinite c = True):
    (x + c).bits
      = Float.Model.roundRatio
        (Int.add (Float.Theory.units x) (Float.Theory.units c))
        1
        (-1074)
        (Float.Model.signBit x.bits ∧ Float.Model.signBit c.bits) :=
  let z: Bool := Float.Model.signBit x.bits ∧ Float.Model.signBit c.bits
  let n: Int := Int.add (Float.Theory.units x) (Float.Theory.units c)
  Eq.trans
    (Eq.cong (w => w.bits) (Float.Theory.addFinite x c fx fc))
    (Float.Theory.ofBitsBits
      (Float.Model.roundRatio n 1 (-1074) z)
      (Float.Theory.roundRatioValid 1 (-1074) z byComputing n))

--| A sum of finite doubles with fewer units than the overflow threshold is finite.
theorem Float.Theory.addFiniteOf ∀ (x c: Float)
    (fx: Float.isFinite x = True)
    (fc: Float.isFinite c = True)
    (h: Int.natAbs (Int.add (Float.Theory.units x) (Float.Theory.units c)) < Float.Theory.overflowUnits):
    Float.isFinite (x + c) = True :=
  Float.Theory.isFiniteOf
    (x + c)
    (J
      (r w => Float.Theory.FiniteBits r)
      (Float.Theory.roundFinite
        (Int.add (Float.Theory.units x) (Float.Theory.units c))
        (Float.Model.signBit x.bits ∧ Float.Model.signBit c.bits)
        h)
      (Float.Theory.addBitsOf x c fx fc).flipped)

--| A sum of finite doubles whose exact value is at least a finite double's is
--| at least it in the total order, unless the bound is `0.0` and the sum a
--| `-0.0`.
theorem Float.Theory.addAtLeast ∀ (x c lo: Float)
    (fx: Float.isFinite x = True)
    (fc: Float.isFinite c = True)
    (flo: Float.isFinite lo = True)
    (h: Int.leq (Float.Theory.units lo) (Int.add (Float.Theory.units x) (Float.Theory.units c)) = True)
    (zs: Float.Model.signBit lo.bits = False → (Float.Model.signBit x.bits ∧ Float.Model.signBit c.bits) = False):
    lo <= x + c :=
  Float.Theory.leqVia
    (Float.orderKey lo)
    (Float.orderKey (x + c))
    (Float.Theory.roundKey (Float.Theory.units lo) 1 (-1074) (Float.Model.signBit lo.bits))
    (Float.Theory.roundKey
      (Int.add (Float.Theory.units x) (Float.Theory.units c))
      1
      (-1074)
      (Float.Model.signBit x.bits ∧ Float.Model.signBit c.bits))
    (Eq.cong Float.Theory.key (Float.Theory.roundRatioUnitsBits lo.bits (Float.Theory.finiteBits lo flo)).flipped)
    (Eq.cong Float.Theory.key (Float.Theory.addBitsOf x c fx fc))
    (Float.Theory.roundKeyMonoLe 1
      (-1074)
      (Float.Model.signBit lo.bits)
      (Float.Model.signBit x.bits ∧ Float.Model.signBit c.bits)
      byComputing
      (Float.Theory.units lo)
      (Int.add (Float.Theory.units x) (Float.Theory.units c))
      h
      zs)

--| A sum of finite doubles whose exact value is at most a finite double's is
--| at most it, unless the sum is a `0.0` and the bound `-0.0`.
theorem Float.Theory.addAtMost ∀ (x c hi: Float)
    (fx: Float.isFinite x = True)
    (fc: Float.isFinite c = True)
    (fhi: Float.isFinite hi = True)
    (h: Int.leq (Int.add (Float.Theory.units x) (Float.Theory.units c)) (Float.Theory.units hi) = True)
    (zs: (Float.Model.signBit x.bits ∧ Float.Model.signBit c.bits) = False → Float.Model.signBit hi.bits = False):
    x + c <= hi :=
  Float.Theory.leqVia
    (Float.orderKey (x + c))
    (Float.orderKey hi)
    (Float.Theory.roundKey
      (Int.add (Float.Theory.units x) (Float.Theory.units c))
      1
      (-1074)
      (Float.Model.signBit x.bits ∧ Float.Model.signBit c.bits))
    (Float.Theory.roundKey (Float.Theory.units hi) 1 (-1074) (Float.Model.signBit hi.bits))
    (Eq.cong Float.Theory.key (Float.Theory.addBitsOf x c fx fc))
    (Eq.cong Float.Theory.key (Float.Theory.roundRatioUnitsBits hi.bits (Float.Theory.finiteBits hi fhi)).flipped)
    (Float.Theory.roundKeyMonoLe 1
      (-1074)
      (Float.Model.signBit x.bits ∧ Float.Model.signBit c.bits)
      (Float.Model.signBit hi.bits)
      byComputing
      (Int.add (Float.Theory.units x) (Float.Theory.units c))
      (Float.Theory.units hi)
      h
      zs)

theorem Float.Theory.intMulLeRight ∀ (a b c: Int)
    (h: Int.leq a b = True)
    (hc: Int.leq (OfNat 0) c = True):
    Int.leq (Int.mul a c) (Int.mul b c) = True :=
  let d: 0 ≤ (b - a) * c := Int.mulNonneg (b - a) c (arithmetic [h]) hc
  let e: (b - a) * c = b * c - a * c := algebra
  arithmetic [d, e]

theorem Float.Theory.intMulLeLeft ∀ (a b c: Int)
    (h: Int.leq a b = True)
    (hc: Int.leq (OfNat 0) c = True):
    Int.leq (Int.mul c a) (Int.mul c b) = True :=
  rewrite Int.mulComm c a, Int.mulComm c b then Float.Theory.intMulLeRight a b c h hc

--| A non-negative double has non-negative units.
theorem Float.Theory.unitsNonneg ∀ (c: Float) (hc: 0.0 <= c): Int.leq (OfNat 0) (Float.Theory.units c) = True :=
  let sc: Nat.leq 9223372036854775808 c.bits = False := Float.Theory.signClear c.bits hc
  let uc: Float.Theory.units c = OfNat (Float.Theory.magUnits c.bits) := rewrite sc
  rewrite uc

--| The bits of a product of finite doubles: their units' product, rounded.
theorem Float.Theory.mulBitsOf ∀ (x c: Float)
    (fx: Float.isFinite x = True)
    (fc: Float.isFinite c = True):
    (x * c).bits
      = Float.Model.roundRatio
        (Int.mul (Float.Theory.units x) (Float.Theory.units c))
        1
        (-2148)
        (Bool.xor (Float.Model.signBit x.bits) (Float.Model.signBit c.bits)) :=
  let fa: Float.Theory.FiniteBits x.bits := Float.Theory.finiteBits x fx
  let fb: Float.Theory.FiniteBits c.bits := Float.Theory.finiteBits c fc
  let n: Int := Int.mul (Float.Theory.units x) (Float.Theory.units c)
  let z: Bool := Bool.xor (Float.Model.signBit x.bits) (Float.Model.signBit c.bits)
  let rounded: Float.Model.mulBits x.bits c.bits = Float.Model.roundRatio n 1 (-2148) z :=
    Float.Theory.mulFiniteBits x.bits c.bits
      (Float.Theory.finiteNotNaN x.bits fa)
      (Float.Theory.finiteNotNaN c.bits fb)
      (Float.Theory.finiteNotInfinite x.bits fa)
      (Float.Theory.finiteNotInfinite c.bits fb)
  let valid: Float.isValid (Float.Model.mulBits x.bits c.bits) = True :=
    J (r w => Float.isValid r = True) (Float.Theory.roundRatioValid 1 (-2148) z byComputing n) rounded.flipped
  calc (x * c).bits
    _ = (Float.ofBits (Float.Model.mulBits x.bits c.bits)).bits := Eq.cong (w => w.bits) (Float.Theory.mulOfBits x c)
    _ = Float.Model.mulBits x.bits c.bits := Float.Theory.ofBitsBits (Float.Model.mulBits x.bits c.bits) valid
    _ = Float.Model.roundRatio n 1 (-2148) z := rounded

--| Adding the same finite double to finite doubles keeps their order.
theorem Float.addMonotoneLeft ∀ (x y z: Float)
    (fx: Float.isFinite x = True)
    (fy: Float.isFinite y = True)
    (fz: Float.isFinite z = True)
    (h: x <= y):
    x + z <= y + z :=
  let sx: Bool := Float.Model.signBit x.bits
  let sy: Bool := Float.Model.signBit y.bits
  let sz: Bool := Float.Model.signBit z.bits
  let ux: Int := Float.Theory.units x
  let uy: Int := Float.Theory.units y
  let uz: Int := Float.Theory.units z
  let units: Int.leq ux uy = True := Float.Theory.unitsMonoKey x.bits y.bits h
  Float.Theory.leqVia
    (Float.orderKey (x + z))
    (Float.orderKey (y + z))
    (Float.Theory.roundKey (Int.add ux uz) 1 (-1074) (sx ∧ sz))
    (Float.Theory.roundKey (Int.add uy uz) 1 (-1074) (sy ∧ sz))
    (Eq.cong Float.Theory.key (Float.Theory.addBitsOf x z fx fz))
    (Eq.cong Float.Theory.key (Float.Theory.addBitsOf y z fy fz))
    (Float.Theory.roundKeyMonoLe 1
      (-1074)
      (sx ∧ sz)
      (sy ∧ sz)
      byComputing
      (Int.add ux uz)
      (Int.add uy uz)
      (arithmetic [units])
      (Float.Theory.andFalseUp sx sy sz (Float.Theory.signClearUp x.bits y.bits h)))

test "Float.addMonotoneLeft" :=
  -0.0 + 0.0 <= 0.0 + 0.0
    ∧ -0.0 + (-0.0) <= 0.0 + (-0.0)
    ∧ 1.0 + 1e-17 <= 1.0000000000000002 + 1e-17
    ∧ -1.7976931348623157e308 + -1.7976931348623157e308 <= 1.0 + -1.7976931348623157e308

--| Adding a finite double to the same finite double keeps their order.
theorem Float.addMonotone ∀ (x y z: Float)
    (fx: Float.isFinite x = True)
    (fy: Float.isFinite y = True)
    (fz: Float.isFinite z = True)
    (h: x <= y):
    z + x <= z + y :=
  rewrite Float.addComm z x, Float.addComm z y then Float.addMonotoneLeft x y z fx fy fz h

--| Multiplying finite doubles by the same non-negative finite double keeps
--| their order.
theorem Float.mulMonotoneLeft ∀ (x y c: Float)
    (fx: Float.isFinite x = True)
    (fy: Float.isFinite y = True)
    (fc: Float.isFinite c = True)
    (hc: 0.0 <= c)
    (h: x <= y):
    x * c <= y * c :=
  let sx: Bool := Float.Model.signBit x.bits
  let sy: Bool := Float.Model.signBit y.bits
  let sc: Bool := Float.Model.signBit c.bits
  let ux: Int := Float.Theory.units x
  let uy: Int := Float.Theory.units y
  let uc: Int := Float.Theory.units c
  Float.Theory.leqVia
    (Float.orderKey (x * c))
    (Float.orderKey (y * c))
    (Float.Theory.roundKey (Int.mul ux uc) 1 (-2148) (Bool.xor sx sc))
    (Float.Theory.roundKey (Int.mul uy uc) 1 (-2148) (Bool.xor sy sc))
    (Eq.cong Float.Theory.key (Float.Theory.mulBitsOf x c fx fc))
    (Eq.cong Float.Theory.key (Float.Theory.mulBitsOf y c fy fc))
    (Float.Theory.roundKeyMonoLe 1
      (-2148)
      (Bool.xor sx sc)
      (Bool.xor sy sc)
      byComputing
      (Int.mul ux uc)
      (Int.mul uy uc)
      (Float.Theory.intMulLeRight ux uy uc (Float.Theory.unitsMonoKey x.bits y.bits h) (Float.Theory.unitsNonneg c hc))
      (Float.Theory.xorFalseUp sx sy sc (Float.Theory.signClear c.bits hc) (Float.Theory.signClearUp x.bits y.bits h)))

--| Multiplying the same non-negative finite double by finite doubles keeps
--| their order.
theorem Float.mulMonotone ∀ (x y c: Float)
    (fx: Float.isFinite x = True)
    (fy: Float.isFinite y = True)
    (fc: Float.isFinite c = True)
    (hc: 0.0 <= c)
    (h: x <= y):
    c * x <= c * y :=
  let sx: Bool := Float.Model.signBit x.bits
  let sy: Bool := Float.Model.signBit y.bits
  let sc: Bool := Float.Model.signBit c.bits
  let ux: Int := Float.Theory.units x
  let uy: Int := Float.Theory.units y
  let uc: Int := Float.Theory.units c
  let clear: sc = False := Float.Theory.signClear c.bits hc
  Float.Theory.leqVia
    (Float.orderKey (c * x))
    (Float.orderKey (c * y))
    (Float.Theory.roundKey (Int.mul uc ux) 1 (-2148) (Bool.xor sc sx))
    (Float.Theory.roundKey (Int.mul uc uy) 1 (-2148) (Bool.xor sc sy))
    (Eq.cong Float.Theory.key (Float.Theory.mulBitsOf c x fc fx))
    (Eq.cong Float.Theory.key (Float.Theory.mulBitsOf c y fc fy))
    (Float.Theory.roundKeyMonoLe 1
      (-2148)
      (Bool.xor sc sx)
      (Bool.xor sc sy)
      byComputing
      (Int.mul uc ux)
      (Int.mul uc uy)
      (Float.Theory.intMulLeLeft ux uy uc (Float.Theory.unitsMonoKey x.bits y.bits h) (Float.Theory.unitsNonneg c hc))
      (k => rewrite clear then Float.Theory.signClearUp x.bits y.bits h (rewrite clear at k)))

test "Float.mulMonotoneLeft" :=
  -0.0 * 0.0 <= 0.0 * 0.0
    ∧ -1.0 * 0.0 <= 1.0 * 0.0
    ∧ 0.1 * 3.0 <= 0.2 * 3.0
    ∧ -1.7976931348623157e308 * 2.0 <= 1.0 * 2.0
    ∧ 5e-324 * 0.5 <= 1e-323 * 0.5
    ∧ 0.15 * 7.0 <= 0.85 * 7.0

--| A finite double has at most the largest finite double's units in size.
theorem Float.Theory.unitsAtMostMax ∀ (x: Float)
    (fx: Float.isFinite x = True):
    Int.natAbs (Float.Theory.units x) ≤ Float.Theory.magUnits 9218868437227405311 :=
  J
    (u w => u ≤ Float.Theory.magUnits 9218868437227405311)
    (Float.Theory.magUnitsLe
      (Float.Model.magnitude x.bits)
      9218868437227405311
      (arithmetic [Float.Theory.finiteBits x fx]))
    (Float.Theory.natAbsUnits x.bits).flipped

--| `x % y` for finite `x` and finite nonzero `y`: finite, and of fewer
--| units than `y` in size.
theorem Float.Theory.remUnits ∀ (x y: Float)
    (fx: Float.isFinite x = True)
    (fy: Float.isFinite y = True)
    (zy: Float.isZero y = False):
    (Float.isFinite (x % y) = True) ∧ (Int.natAbs (Float.Theory.units (x % y)) < Int.natAbs (Float.Theory.units y)) :=
  let ex :=
    Float.Theory.remExact x.bits y.bits
      (Float.Theory.finiteBits x fx)
      (Float.Theory.finiteBits y fy)
      (Float.Theory.modelNotZero y zy)
  let rb: (x % y).bits = Float.Model.remBits x.bits y.bits := Float.Theory.remOfBits x y fx fy zy
  Both
    (Float.Theory.isFiniteOf (x % y) (J (r w => Float.Theory.FiniteBits r) ex.left.left rb.flipped))
    (J (r w => Int.natAbs (Float.Model.units r) < Int.natAbs (Float.Model.units y.bits)) ex.right rb.flipped)

-- Scaling by one and by ten

--| Rounding `num × d / den1 × 2^s1` and `num / den2 × 2^s2` gives the same
--| double when the two fractions are equal for every positive `num`.
theorem Float.Theory.roundRatioScale ∀ (num: Int) (d den1 den2: Nat) (s1 s2: Int) (z: Bool)
    (pd: 0 < d)
    (p1: 0 < den1)
    (p2: 0 < den2)
    (e: ∀ (k: Nat) => Float.Model.scaleUp (k * d) (Int.add s1 (OfNat 1074))
      * Float.Model.scaleDown den2 (Int.add s2 (OfNat 1074))
      = Float.Model.scaleUp k (Int.add s2 (OfNat 1074)) * Float.Model.scaleDown den1 (Int.add s1 (OfNat 1074))):
    Float.Model.roundRatio (Int.mul num (OfNat d)) den1 s1 z = Float.Model.roundRatio num den2 s2 z :=
  match num with
    | OfNat Zero =>
      rewrite (algebra: Int.mul (OfNat 0) (OfNat d) = OfNat 0) then
        Eq.trans (Float.Theory.roundRatioZeroNum den1 s1 z) (Float.Theory.roundRatioZeroNum den2 s2 z).flipped
    | OfNat (Succ k) =>
      let pk: 0 < Succ k := byComputing
      let pkd: 0 < Succ k * d := Float.Theory.mulPos (Succ k) d pk pd
      rewrite (algebra: Int.mul (OfNat (Succ k)) (OfNat d) = OfNat (Succ k * d)) then
        calc Float.Model.roundRatio (OfNat (Succ k * d)) den1 s1 z
          _ = Float.Model.roundMagnitude False (Succ k * d) den1 (Int.add s1 (OfNat 1074)) :=
            Float.Theory.roundRatioOfPos den1 s1 z (Succ k * d) pkd
          _ = Float.Model.roundMagnitude False (Succ k) den2 (Int.add s2 (OfNat 1074)) :=
            Float.Theory.magnitudeCross
              (Succ k * d)
              den1
              (Succ k)
              den2
              (Int.add s1 (OfNat 1074))
              (Int.add s2 (OfNat 1074))
              pkd
              p1
              pk
              p2
              (e (Succ k))
          _ = Float.Model.roundRatio (OfNat (Succ k)) den2 s2 z :=
            (Float.Theory.roundRatioOfPos den2 s2 z (Succ k) pk).flipped
    | NegSucc k =>
      let pk: 0 < Succ k := byComputing
      let pkd: 0 < Succ k * d := Float.Theory.mulPos (Succ k) d pk pd
      rewrite (algebra: Int.mul (NegSucc k) (OfNat d) = Int.neg (OfNat (Succ k * d))) then
        calc Float.Model.roundRatio (Int.neg (OfNat (Succ k * d))) den1 s1 z
          _ = Float.Model.roundMagnitude False (Succ k * d) den1 (Int.add s1 (OfNat 1074)) + 9223372036854775808 :=
            Float.Theory.roundRatioOfNeg den1 s1 z (Succ k * d) pkd
          _ = Float.Model.roundMagnitude False (Succ k) den2 (Int.add s2 (OfNat 1074)) + 9223372036854775808 :=
            Eq.cong
              (t => t + 9223372036854775808)
              (Float.Theory.magnitudeCross
                (Succ k * d)
                den1
                (Succ k)
                den2
                (Int.add s1 (OfNat 1074))
                (Int.add s2 (OfNat 1074))
                pkd
                p1
                pk
                p2
                (e (Succ k)))
          _ = Float.Model.roundRatio (NegSucc k) den2 s2 z := (Float.Theory.roundRatioNeg k den2 s2 z).flipped

--| Units over `2^1074` at scale 0 are the units themselves at scale -1074.
theorem Float.Theory.roundRatioUnitDen ∀ (num: Int) (z: Bool):
    Float.Model.roundRatio num (Float.Model.pow2 1074) (OfNat 0) z = Float.Model.roundRatio num 1 (-1074) z :=
  let p: Nat := Float.Model.pow2 1074
  Eq.trans
    (Eq.cong (t => Float.Model.roundRatio t p (OfNat 0) z) (algebra: num = Int.mul num (OfNat 1)))
    (Float.Theory.roundRatioScale num 1 p 1 (OfNat 0) (-1074) z byComputing byComputing byComputing (k =>
      (algebra: k * 1 * p * 1 = k * 1 * p)))

theorem Float.Theory.divOneBits ∀ (a: Nat)
    (va: Float.isValid a = True):
    Float.Model.divBits a 4607182418800017408 = a :=
  Float.Theory.orCase
    (Float.Theory.boolCases (Float.Model.isSpecial a))
    (sp => Float.Theory.divSpecialBits a 4607182418800017408 va sp byComputing byComputing)
    (sp =>
      let fa: Float.Theory.FiniteBits a := Float.Theory.finiteOfSpecial a sp
      calc Float.Model.divBits a 4607182418800017408
        _ = Float.Model.roundRatio
            (Float.Model.units a)
            (Int.natAbs (Float.Model.units 4607182418800017408))
            (OfNat 0)
            (Float.Model.signBit a) :=
          Float.Theory.divPosBits a 4607182418800017408 fa byComputing byComputing byComputing
        _ = Float.Model.roundRatio (Float.Model.units a) (Float.Model.pow2 1074) (OfNat 0) (Float.Model.signBit a) :=
          Eq.cong
            (d => Float.Model.roundRatio (Float.Model.units a) d (OfNat 0) (Float.Model.signBit a))
            (byComputing: Int.natAbs (Float.Model.units 4607182418800017408) = Float.Model.pow2 1074)
        _ = Float.Model.roundRatio (Float.Model.units a) 1 (-1074) (Float.Model.signBit a) :=
          Float.Theory.roundRatioUnitDen (Float.Model.units a) (Float.Model.signBit a)
        _ = a := Float.Theory.roundRatioUnitsBits a fa)

--| `x / 1.0` is `x`, zeros, infinities and the NaN included.
theorem Float.divOneRight ∀ (x: Float): x / 1.0 = x := match x with
  | { bits = a, valid = p } =>
    Float.bitsExt
      (Float.ofBits (Float.Model.divBits a 4607182418800017408))
      { bits = a, valid = p }
      (Eq.trans
        (Float.Theory.ofBitsBits
          (Float.Model.divBits a 4607182418800017408)
          (Float.Theory.validTo (Float.Model.divBits a 4607182418800017408) a (Float.Theory.divOneBits a p) p))
        (Float.Theory.divOneBits a p))

test "Float.divOneRight" :=
  2.5 / 1.0 == 2.5
    ∧ Float.ieeeEq (-87.60000000000001 / 1.0) (-87.60000000000001)
    ∧ (-0.0 / 1.0).bits == 9223372036854775808
    ∧ 5e-324 / 1.0 == 5e-324
    ∧ Float.infinity / 1.0 == Float.infinity
    ∧ Float.isNaN (Float.nan / 1.0)

--| A whole double times ten: for `y` of `n × 2^1074` units (the whole
--| number `n`, negative or not) with `|10n| ≤ 2^53`, `y * 10.0` is finite
--| with exactly `10n × 2^1074` units.
theorem Float.Theory.mulTenWhole ∀ (y: Float) (n: Int)
    (fy: Float.Theory.FiniteBits y.bits)
    (uy: Float.Theory.units y = Int.mul n (OfNat (Float.Model.pow2 1074)))
    (h: Int.natAbs (Int.mul n (OfNat 10)) ≤ 9007199254740992):
    Float.Theory.FiniteBits (y * 10.0).bits
      ∧ (Float.Theory.units (y * 10.0) = Int.mul (Int.mul n (OfNat 10)) (OfNat (Float.Model.pow2 1074))) :=
  let p: Nat := Float.Model.pow2 1074
  let a: Nat := y.bits
  let z: Bool := Bool.xor (Float.Model.signBit a) False
  let ten: Int := Int.mul n (OfNat 10)
  let product: Int.mul (Float.Model.units a) (Float.Model.units 4621819117588971520)
    = Int.mul (Int.mul ten (OfNat p)) (OfNat p) :=
    rewrite uy, (byComputing: Float.Model.units 4621819117588971520 = OfNat (10 * p)) then algebra
  let m: Float.Model.mulBits a 4621819117588971520 = Float.Model.roundRatio (Int.mul ten (OfNat p)) 1 (-1074) z :=
    calc Float.Model.mulBits a 4621819117588971520
      _ = Float.Model.roundRatio
          (Int.mul (Float.Model.units a) (Float.Model.units 4621819117588971520))
          1
          (-2148)
          (Bool.xor (Float.Model.signBit a) (Float.Model.signBit 4621819117588971520)) :=
        Float.Theory.mulFiniteBits a 4621819117588971520
          (Float.Theory.finiteNotNaN a fy)
          byComputing
          (Float.Theory.finiteNotInfinite a fy)
          byComputing
      _ = Float.Model.roundRatio (Int.mul (Int.mul ten (OfNat p)) (OfNat p)) 1 (-2148) z :=
        Eq.cong (u => Float.Model.roundRatio u 1 (-2148) z) product
      _ = Float.Model.roundRatio (Int.mul ten (OfNat p)) 1 (-1074) z :=
        Float.Theory.roundRatioScale
          (Int.mul ten (OfNat p))
          p
          1
          1
          (-2148)
          (-1074)
          z
          byComputing
          byComputing
          byComputing
          (k => (algebra: k * p * 1 = k * 1 * (1 * p)))
  let r: (y * 10.0).bits = Float.Model.roundRatio (Int.mul ten (OfNat p)) 1 (-1074) z := calc (y * 10.0).bits
    _ = (Float.ofBits (Float.Model.mulBits a 4621819117588971520)).bits :=
      Eq.cong (q => q.bits) (Float.Theory.mulOfBits y 10.0)
    _ = Float.Model.mulBits a 4621819117588971520 :=
      Float.Theory.ofBitsBits
        (Float.Model.mulBits a 4621819117588971520)
        (Float.Theory.validTo
          (Float.Model.mulBits a 4621819117588971520)
          (Float.Model.roundRatio (Int.mul ten (OfNat p)) 1 (-1074) z)
          m
          (Float.Theory.roundRatioValid 1 (-1074) z byComputing (Int.mul ten (OfNat p))))
    _ = Float.Model.roundRatio (Int.mul ten (OfNat p)) 1 (-1074) z := m
  J
    (b w => Float.Theory.FiniteBits b ∧ (Float.Model.units b = Int.mul ten (OfNat p)))
    (Float.Theory.roundWholeUnits ten z h)
    r.flipped

--| A multiple of ten over ten: for `c` of `10n × 2^1074` units with `|n| ≤
--| 2^53`, `c / 10.0` is finite with exactly `n × 2^1074` units.
theorem Float.Theory.divTenWhole ∀ (c: Float) (n: Int)
    (fc: Float.Theory.FiniteBits c.bits)
    (uc: Float.Theory.units c = Int.mul (Int.mul n (OfNat 10)) (OfNat (Float.Model.pow2 1074)))
    (h: Int.natAbs n ≤ 9007199254740992):
    Float.Theory.FiniteBits (c / 10.0).bits
      ∧ (Float.Theory.units (c / 10.0) = Int.mul n (OfNat (Float.Model.pow2 1074))) :=
  let p: Nat := Float.Model.pow2 1074
  let z: Bool := Float.Model.signBit c.bits
  let q: (c / 10.0).bits = Float.Model.roundRatio (Int.mul n (OfNat p)) 1 (-1074) z := calc (c / 10.0).bits
    _ = Float.Model.roundRatio (Float.Model.units c.bits) (Int.natAbs (Float.Model.units 10.0.bits)) (OfNat 0) z :=
      Float.Theory.quotientBits c 10.0 byComputing byComputing (Float.Theory.isFiniteOf c fc)
    _ = Float.Model.roundRatio (Int.mul n (OfNat (10 * p))) (10 * p) (OfNat 0) z :=
      Eq.cong2
        (u d => Float.Model.roundRatio u d (OfNat 0) z)
        (Eq.trans uc (algebra: Int.mul (Int.mul n (OfNat 10)) (OfNat p) = Int.mul n (OfNat (10 * p))))
        (byComputing: Int.natAbs (Float.Model.units 10.0.bits) = 10 * p)
    _ = Float.Model.roundRatio n 1 (OfNat 0) z :=
      Float.Theory.roundRatioScale n (10 * p) (10 * p) 1 (OfNat 0) (OfNat 0) z byComputing byComputing byComputing (k =>
        (algebra: k * (10 * p) * p * 1 = k * p * (10 * p)))
    _ = Float.Model.roundRatio (Int.mul n (OfNat p)) 1 (-1074) z := Float.Theory.roundWhole n z
  J
    (b w => Float.Theory.FiniteBits b ∧ (Float.Model.units b = Int.mul n (OfNat p)))
    (Float.Theory.roundWholeUnits n z h)
    q.flipped

--| Two finite doubles with the same nonzero units are the same double.
theorem Float.Theory.unitsInjective ∀ (x y: Float)
    (fx: Float.Theory.FiniteBits x.bits)
    (fy: Float.Theory.FiniteBits y.bits)
    (e: Float.Theory.units x = Float.Theory.units y)
    (nz: Float.Theory.units x ≠ OfNat 0):
    x = y :=
  Float.bitsExt x y
    (calc x.bits
      _ = Float.Model.roundRatio (Float.Model.units x.bits) 1 (-1074) (Float.Model.signBit x.bits) :=
        (Float.Theory.roundRatioUnitsBits x.bits fx).flipped
      _ = Float.Model.roundRatio (Float.Model.units x.bits) 1 (-1074) (Float.Model.signBit y.bits) :=
        Float.Theory.roundRatioSignIrrelevant 1
          (-1074)
          (Float.Model.signBit x.bits)
          (Float.Model.signBit y.bits)
          (Float.Model.units x.bits)
          nz
      _ = Float.Model.roundRatio (Float.Model.units y.bits) 1 (-1074) (Float.Model.signBit y.bits) :=
        Eq.cong (u => Float.Model.roundRatio u 1 (-1074) (Float.Model.signBit y.bits)) e
      _ = y.bits := Float.Theory.roundRatioUnitsBits y.bits fy)

theorem Float.Theory.mulNonzero ∀ (n: Int) (p: Nat) (pp: 0 < p) (nz: n ≠ OfNat 0): Int.mul n (OfNat p) ≠ OfNat 0 :=
  match n with
    | OfNat Zero => Void.impossible (nz byComputing)
    | OfNat (Succ k) =>
      let pos: 0 < Succ k * p := Float.Theory.mulPos (Succ k) p byComputing pp
      rewrite (algebra: Int.mul (OfNat (Succ k)) (OfNat p) = OfNat (Succ k * p)) then (e => arithmetic [e, pos])
    | NegSucc k =>
      let pos: 0 < Succ k * p := Float.Theory.mulPos (Succ k) p byComputing pp
      rewrite (algebra: Int.mul (NegSucc k) (OfNat p) = Int.neg (OfNat (Succ k * p))) then (e => arithmetic [e, pos])

--| A whole double survives `round (y * 10.0) / 10.0`, zero signs included:
--| for `y` of `n × 2^1074` units with `|10n| ≤ 2^53`, `* 10.0` and
--| `/ 10.0` are exact and `round` keeps a whole number.
theorem Float.Theory.roundTenthsWhole ∀ (y: Float) (n: Int)
    (fy: Float.Theory.FiniteBits y.bits)
    (uy: Float.Theory.units y = Int.mul n (OfNat (Float.Model.pow2 1074)))
    (h: Int.natAbs (Int.mul n (OfNat 10)) ≤ 9007199254740992):
    Float.round (y * 10.0) / 10.0 = y :=
  let p: Nat := Float.Model.pow2 1074
  Float.Theory.orCase
    [goal := Float.round (y * 10.0) / 10.0 = y]
    (Float.Theory.intZeroCases n)
    (n0 =>
      let u0: Float.Model.units y.bits = OfNat 0 := Eq.trans uy (rewrite n0 then algebra)
      Float.Theory.orCase
        (Float.Theory.unitsZeroIsZeroBits y.bits u0)
        (b =>
          J
            (w k => Float.round (w * 10.0) / 10.0 = w)
            (byComputing: Float.round (0.0 * 10.0) / 10.0 = 0.0)
            (Float.bitsExt y 0.0 b).flipped)
        (b =>
          J
            (w k => Float.round (w * 10.0) / 10.0 = w)
            (byComputing: Float.round (-0.0 * 10.0) / 10.0 = -0.0)
            (Float.bitsExt y (-0.0) b).flipped))
    (nz =>
      let m: Float.Theory.FiniteBits (y * 10.0).bits
        ∧ (Float.Theory.units (y * 10.0) = Int.mul (Int.mul n (OfNat 10)) (OfNat p)) :=
        Float.Theory.mulTenWhole y n fy uy h
      let r: Float.round (y * 10.0) = y * 10.0 := Float.roundOfWhole (y * 10.0) (Int.mul n (OfNat 10)) m.right
      let d: Float.Theory.FiniteBits (y * 10.0 / 10.0).bits
        ∧ (Float.Theory.units (y * 10.0 / 10.0) = Int.mul n (OfNat p)) :=
        Float.Theory.divTenWhole (y * 10.0) n m.left m.right (arithmetic [h])
      rewrite r then
        Float.Theory.unitsInjective
          (y * 10.0 / 10.0)
          y
          d.left
          fy
          (Eq.trans d.right uy.flipped)
          (J (u k => u ≠ OfNat 0) (Float.Theory.mulNonzero n p byComputing nz) d.right.flipped))

theorem Float.Theory.absBelowBits ∀ (x b: Float)
    (sb: Nat.leq 9223372036854775808 b.bits = False)
    (small: Float.abs x < b):
    Float.Model.magnitude x.bits < b.bits :=
  let kb: Float.orderKey b = OfNat b.bits := Float.Theory.keyClear b.bits sb
  arithmetic [small, Float.Theory.absKey x, kb]

theorem Float.Theory.tenfoldBelow ∀ (f: Int)
    (h: Int.natAbs f ≤ 562949953421312):
    (Int.natAbs f ≤ 9007199254740992) ∧ (Int.natAbs (Int.mul f (OfNat 10)) ≤ 9007199254740992) :=
  Both (arithmetic [h]) (arithmetic [h])

theorem Float.Theory.tenfoldBelowNeg ∀ (g: Int)
    (h: Int.natAbs g ≤ 562949953421312):
    (Int.natAbs (Int.neg g) ≤ 9007199254740992) ∧ (Int.natAbs (Int.mul (Int.neg g) (OfNat 10)) ≤ 9007199254740992) :=
  Both (arithmetic [h]) (arithmetic [h])

--| A double below a positive finite `b` in size (`b` of `bound × 2^1074`
--| units) is finite, with fewer than `bound × 2^1074` units either way.
theorem Float.Theory.absBelowUnitsOf ∀ (x b: Float) (bound: Nat)
    (fb: Float.Theory.FiniteBits b.bits)
    (sb: Nat.leq 9223372036854775808 b.bits = False)
    (ub: Float.Theory.magUnits b.bits = Float.Model.pow2 1074 * bound)
    (small: Float.abs x < b):
    Float.Theory.FiniteBits x.bits ∧ (Int.natAbs (Float.Model.units x.bits) < Float.Model.pow2 1074 * bound) :=
  let mb: Float.Model.magnitude b.bits = b.bits := rewrite sb
  let below: Float.Model.magnitude x.bits < b.bits := Float.Theory.absBelowBits x b sb small
  Both
    (Nat.lessTrans
      (Float.Model.magnitude x.bits)
      b.bits
      9218868437227405312
      below
      (J (y w => y < 9218868437227405312) fb mb))
    (rewrite Float.Theory.unitsMag x.bits, Float.Theory.natAbsSigned (Float.Model.signBit x.bits) then
      J
        (y w => Float.Theory.magUnits (Float.Model.magnitude x.bits) < y)
        (Float.Theory.magUnitsLess (Float.Model.magnitude x.bits) b.bits below)
        ub)

--| `floorDiv` of a size below `bound × p` is at most `bound` in size.
theorem Float.Theory.floorDivBelow ∀ (s: Bool) (m p bound: Nat)
    (pp: 0 < p)
    (h: m < p * bound):
    Int.natAbs (Float.Model.floorDiv s m p) ≤ bound :=
  let q: Nat := Nat.divFuel m m p
  let low: q * p ≤ m := Nat.divFuelLe m m p
  match s with
    | False =>
      let f: Float.Model.floorDiv False m p = OfNat q := byComputing
      let qb: q < bound := Float.Theory.cancelLessComm q bound p (arithmetic [low, h])
      rewrite f then arithmetic [qb]
    | True =>
      Float.Theory.orCase
        (Float.Theory.boolCases (Nat.equal (q * p) m))
        (e =>
          let ex: q * p = m := Nat.equalSound (q * p) m e
          let f: Float.Model.floorDiv True m p = Int.neg (OfNat q) := rewrite e
          let qb: q < bound := Float.Theory.cancelLessComm q bound p (arithmetic [ex, h])
          rewrite f then arithmetic [qb])
        (e =>
          let ne: q * p ≠ m := Nat.equalFalse (q * p) m e
          let f: Float.Model.floorDiv True m p = NegSucc q := rewrite e
          let qb: q < bound := Float.Theory.cancelLessComm q bound p (arithmetic [low, ne, h])
          rewrite f then arithmetic [qb])

--| `floor x` survives `round (floor x * 10.0) / 10.0` for `|x| < 2^49`
--| (where `floor x * 10.0` is exact), zero signs included. So rounding a
--| whole-degree floor "to tenths" leaves it as it is.
theorem Float.roundTenthsOfFloor ∀ (x: Float)
    (small: Float.abs x < 562949953421312.0):
    Float.round (Float.floor x * 10.0) / 10.0 = Float.floor x :=
  let a: Nat := x.bits
  let s: Bool := Float.Model.signBit a
  let p: Nat := Float.Model.pow2 1074
  let n: Nat := Int.natAbs (Float.Model.units a)
  let f: Int := Float.Model.floorDiv s n p
  let fin: Float.Theory.FiniteBits a ∧ (n < p * 562949953421312) :=
    Float.Theory.absBelowUnitsOf x 562949953421312.0 562949953421312 byComputing byComputing byComputing small
  let fb: Int.natAbs f ≤ 562949953421312 := Float.Theory.floorDivBelow s n p 562949953421312 byComputing fin.right
  let fl: (Float.floor x).bits = Float.Model.roundScaled f 0 s :=
    Eq.trans (Float.Theory.floorOfBits x) (Float.Theory.floorFinite a (Float.Theory.notSpecialOf a fin.left))
  let tb := Float.Theory.tenfoldBelow f fb
  let fx: Float.Theory.FiniteBits (Float.floor x).bits
    ∧ (Float.Model.units (Float.floor x).bits = Int.mul f (OfNat p)) :=
    J
      (r w => Float.Theory.FiniteBits r ∧ (Float.Model.units r = Int.mul f (OfNat p)))
      (Float.Theory.roundScaledWhole f s tb.left)
      fl.flipped
  Float.Theory.roundTenthsWhole (Float.floor x) f fx.left fx.right tb.right

--| `ceil x` survives `round (ceil x * 10.0) / 10.0` for `|x| < 2^49`, zero
--| signs included.
theorem Float.roundTenthsOfCeil ∀ (x: Float)
    (small: Float.abs x < 562949953421312.0):
    Float.round (Float.ceil x * 10.0) / 10.0 = Float.ceil x :=
  let a: Nat := x.bits
  let s: Bool := Float.Model.signBit a
  let p: Nat := Float.Model.pow2 1074
  let n: Nat := Int.natAbs (Float.Model.units a)
  let g: Int := Float.Model.floorDiv (¬s) n p
  let fin: Float.Theory.FiniteBits a ∧ (n < p * 562949953421312) :=
    Float.Theory.absBelowUnitsOf x 562949953421312.0 562949953421312 byComputing byComputing byComputing small
  let gb: Int.natAbs g ≤ 562949953421312 := Float.Theory.floorDivBelow (¬s) n p 562949953421312 byComputing fin.right
  let cl: (Float.ceil x).bits = Float.Model.roundScaled (Int.neg g) 0 s :=
    Eq.trans (Float.Theory.ceilOfBits x) (Float.Theory.ceilFinite a (Float.Theory.notSpecialOf a fin.left))
  let tb := Float.Theory.tenfoldBelowNeg g gb
  let cx: Float.Theory.FiniteBits (Float.ceil x).bits
    ∧ (Float.Model.units (Float.ceil x).bits = Int.mul (Int.neg g) (OfNat p)) :=
    J
      (r w => Float.Theory.FiniteBits r ∧ (Float.Model.units r = Int.mul (Int.neg g) (OfNat p)))
      (Float.Theory.roundScaledWhole (Int.neg g) s tb.left)
      cl.flipped
  Float.Theory.roundTenthsWhole (Float.ceil x) (Int.neg g) cx.left cx.right tb.right

test "Float.roundTenthsOfFloor" :=
  Float.round (Float.floor 2.5 * 10.0) / 10.0 == Float.floor 2.5
    ∧ Float.round (Float.floor -87.60000000000001 * 10.0) / 10.0 == -88.0
    ∧ (Float.round (Float.floor -0.0 * 10.0) / 10.0).bits == 9223372036854775808
    ∧ Float.round (Float.ceil -0.5 * 10.0) / 10.0 == Float.ceil -0.5
    ∧ (Float.round (Float.ceil -0.5 * 10.0) / 10.0).bits == 9223372036854775808
    ∧ Float.round (Float.ceil 562949953421311.5 * 10.0) / 10.0 == 562949953421312.0

-- Negation and subtraction in the total order

theorem Float.Theory.bitsBelow ∀ (x: Float): x.bits < 18446744073709551616 := arithmetic [x.valid]

--| Flipping the sign of a pattern mirrors its key about -½: `key (flip n) = -1 - key n`.
theorem Float.Theory.keyFlip ∀ (n: Nat)
    (v: n < 18446744073709551616):
    Float.Theory.key (Float.flipSignBits n) = Int.sub (NegSucc 0) (Float.Theory.key n) :=
  match c: Nat.leq 9223372036854775808 n with
    | True =>
      let c2: Nat.leq 9223372036854775808 (n - 9223372036854775808) = False := arithmetic [c, v]
      rewrite c2 then arithmetic [c]
    | False =>
      let c2: Nat.leq 9223372036854775808 (n + 9223372036854775808) = True := arithmetic
      rewrite c2 then arithmetic

--| Flipping the sign keeps the magnitude.
theorem Float.Theory.magFlip ∀ (n: Nat)
    (v: n < 18446744073709551616):
    Float.Model.magnitude (Float.flipSignBits n) = Float.Model.magnitude n :=
  match c: Nat.leq 9223372036854775808 n with
    | True =>
      let c2: Nat.leq 9223372036854775808 (n - 9223372036854775808) = False := arithmetic [c, v]
      rewrite c2
    | False =>
      let c2: Nat.leq 9223372036854775808 (n + 9223372036854775808) = True := arithmetic
      rewrite c2 then arithmetic

--| Negation reverses the total order, for doubles other than the NaN.
theorem Float.negAntitone ∀ (x y: Float)
    (nx: Float.isNaN x = False)
    (ny: Float.isNaN y = False)
    (h: x <= y):
    -y <= -x :=
  let hk: Int.leq (Float.Theory.key x.bits) (Float.Theory.key y.bits) = True := h
  Float.Theory.leqVia
    (Float.orderKey (-y))
    (Float.orderKey (-x))
    (Int.sub (NegSucc 0) (Float.Theory.key y.bits))
    (Int.sub (NegSucc 0) (Float.Theory.key x.bits))
    (Eq.trans
      (Eq.cong Float.Theory.key (Float.Theory.negBits y ny))
      (Float.Theory.keyFlip y.bits (Float.Theory.bitsBelow y)))
    (Eq.trans
      (Eq.cong Float.Theory.key (Float.Theory.negBits x nx))
      (Float.Theory.keyFlip x.bits (Float.Theory.bitsBelow x)))
    (arithmetic [hk])

--| The negation of a finite double is finite.
theorem Float.negFinite ∀ (x: Float) (fx: Float.isFinite x = True): Float.isFinite (-x) = True :=
  let fb: Float.Theory.FiniteBits x.bits := Float.Theory.finiteBits x fx
  let nx: Float.isNaN x = False := Float.Theory.finiteNotNaN x.bits fb
  Float.Theory.isFiniteOf
    (-x)
    (J
      (b w => Float.Theory.FiniteBits b)
      (J (m w => m < 9218868437227405312) fb (Float.Theory.magFlip x.bits (Float.Theory.bitsBelow x)).flipped)
      (Float.Theory.negBits x nx).flipped)

test "Float.negAntitone" := -2.0 <= -1.0 ∧ -0.0 <= -(-0.0) ∧ -Float.infinity <= -1e308 ∧ Float.isFinite (-5e-324)

--| Subtracting the same finite double from finite doubles keeps their order.
theorem Float.subMonotoneLeft ∀ (x y c: Float)
    (fx: Float.isFinite x = True)
    (fy: Float.isFinite y = True)
    (fc: Float.isFinite c = True)
    (h: x <= y):
    x - c <= y - c :=
  rewrite Float.subAddNeg x c, Float.subAddNeg y c then Float.addMonotoneLeft x y (-c) fx fy (Float.negFinite c fc) h

--| Subtracting more from a finite double gives no more.
theorem Float.subAntitoneRight ∀ (x a b: Float)
    (fx: Float.isFinite x = True)
    (fa: Float.isFinite a = True)
    (fb: Float.isFinite b = True)
    (h: a <= b):
    x - b <= x - a :=
  rewrite Float.subAddNeg x b, Float.subAddNeg x a then
    Float.addMonotone
      (-b)
      (-a)
      x
      (Float.negFinite b fb)
      (Float.negFinite a fa)
      fx
      (Float.negAntitone a b
        (Float.Theory.finiteNotNaN a.bits (Float.Theory.finiteBits a fa))
        (Float.Theory.finiteNotNaN b.bits (Float.Theory.finiteBits b fb))
        h)

test "Float.subAntitoneRight" := 1.0 - 0.3 <= 1.0 - 0.2 ∧ 0.0 - 0.0 <= 0.0 - (-0.0) ∧ 5.0 - 1.0 <= 6.0 - 1.0

--| A finite pattern's key lies strictly between the infinities'.
theorem Float.Theory.keyFiniteRange ∀ (n: Nat)
    (v: n < 18446744073709551616)
    (f: Float.Theory.FiniteBits n):
    (Int.less (NegSucc 9218868437227405312) (Float.Theory.key n) = True)
      ∧ (Int.less (Float.Theory.key n) (OfNat 9218868437227405312) = True) :=
  match c: Nat.leq 9223372036854775808 n with
    | True =>
      let m: Float.Model.magnitude n = n - 9223372036854775808 := rewrite c
      (arithmetic [c, f, m], arithmetic)
    | False =>
      let m: Float.Model.magnitude n = n := rewrite c
      (arithmetic, arithmetic [f, m])

--| A double between two finite doubles is finite.
theorem Float.finiteBetween ∀ (lo x hi: Float)
    (flo: Float.isFinite lo = True)
    (fhi: Float.isFinite hi = True)
    (a: lo <= x)
    (b: x <= hi):
    Float.isFinite x = True :=
  let ka: Int.leq (Float.Theory.key lo.bits) (Float.Theory.key x.bits) = True := a
  let kb: Int.leq (Float.Theory.key x.bits) (Float.Theory.key hi.bits) = True := b
  let rl := Float.Theory.keyFiniteRange lo.bits (Float.Theory.bitsBelow lo) (Float.Theory.finiteBits lo flo)
  let rh := Float.Theory.keyFiniteRange hi.bits (Float.Theory.bitsBelow hi) (Float.Theory.finiteBits hi fhi)
  let v: x.bits < 18446744073709551616 := Float.Theory.bitsBelow x
  Float.Theory.isFiniteOf x
    (match c: Nat.leq 9223372036854775808 x.bits with
      | True =>
        let m: Float.Model.magnitude x.bits = x.bits - 9223372036854775808 := rewrite c
        let k: Float.Theory.key x.bits = NegSucc (x.bits - 9223372036854775808) := Float.Theory.keySet x.bits c
        (arithmetic [m, k, ka, rl.left, c]: Float.Model.magnitude x.bits < 9218868437227405312)
      | False =>
        let m: Float.Model.magnitude x.bits = x.bits := rewrite c
        let k: Float.Theory.key x.bits = OfNat x.bits := Float.Theory.keyClear x.bits c
        (arithmetic [m, k, kb, rh.right]: Float.Model.magnitude x.bits < 9218868437227405312))

test "Float.finiteBetween" := Float.isFinite (0.5 * 0.7) ∧ ¬Float.isFinite Float.infinity

--| `*` commutes on finite doubles.
theorem Float.mulCommFinite ∀ (x c: Float) (fx: Float.isFinite x = True) (fc: Float.isFinite c = True): x * c = c * x :=
  let ux: Int := Float.Theory.units x
  let uc: Int := Float.Theory.units c
  let sx: Bool := Float.Model.signBit x.bits
  let sc: Bool := Float.Model.signBit c.bits
  Float.bitsExt
    (x * c)
    (c * x)
    (calc (x * c).bits
      _ = Float.Model.roundRatio (Int.mul ux uc) 1 (-2148) (Bool.xor sx sc) := Float.Theory.mulBitsOf x c fx fc
      _ = Float.Model.roundRatio (Int.mul uc ux) 1 (-2148) (Bool.xor sx sc) :=
        Eq.cong (n => Float.Model.roundRatio n 1 (-2148) (Bool.xor sx sc)) (Int.mulComm ux uc)
      _ = Float.Model.roundRatio (Int.mul uc ux) 1 (-2148) (Bool.xor sc sx) :=
        Eq.cong (z => Float.Model.roundRatio (Int.mul uc ux) 1 (-2148) z) (Float.Theory.xorComm sx sc)
      _ = (c * x).bits := (Float.Theory.mulBitsOf c x fc fx).flipped)

--| `0.0 * c` is `0.0` for a non-negative finite `c`.
theorem Float.zeroMulNonneg ∀ (c: Float) (fc: Float.isFinite c = True) (hc: 0.0 <= c): 0.0 * c = 0.0 :=
  let z: Int.mul (Float.Theory.units 0.0) (Float.Theory.units c) = OfNat 0 :=
    rewrite (byComputing: Float.Theory.units 0.0 = OfNat 0) then algebra
  let s: Float.Model.signBit c.bits = False := Float.Theory.signClear c.bits hc
  Float.bitsExt (0.0 * c) 0.0 (rewrite Float.Theory.mulBitsOf 0.0 c byComputing fc, z, s)

test "Float.mulCommFinite" := 0.1 * 3.0 == 3.0 * 0.1 ∧ (-0.0) * 2.0 == 2.0 * (-0.0) ∧ (0.0 * 5.0).bits == 0

-- Rounding error

--| A rounding to a finite pattern is at least as near `t / d` as any
--| representable grid point `q × 2^e` units (`q ≤ 2^53`, below 2^2098).
theorem Float.Theory.roundsToGrid ∀ (t d r q e: Nat)
    (spec: Float.Theory.RoundsTo t d r)
    (fr: r < 9218868437227405312)
    (hq: q ≤ 9007199254740992)
    (fin: q * Nat.pow 2 e < Nat.pow 2 2098):
    Nat.absDiff (Float.Theory.magUnits r * d) t ≤ Nat.absDiff (q * Nat.pow 2 e * d) t :=
  J
    (u w => Nat.absDiff (Float.Theory.magUnits r * d) t ≤ Nat.absDiff (u * d) t)
    (spec.nearest (Float.Theory.gridBits q e) (Float.Theory.gridFinite q e hq fin) fr)
    (Float.Theory.gridUnits q e hq)

theorem Float.Theory.halfSpacing ∀ (a h p: Nat) (x: a ≤ h) (y: a ≤ p - h) (hp: h < p): a + a ≤ p :=
  arithmetic [x, y, hp]

theorem Float.Theory.quotientRoom ∀ (t p q h: Nat)
    (split: t = q * p + h)
    (top: t < p * 9007199254740992):
    q + 1 ≤ 9007199254740992 :=
  let below: q * p < p * 9007199254740992 := arithmetic [split, top]
  let less: q < 9007199254740992 :=
    Float.Theory.cancelLess q 9007199254740992 p (J (y w => q * p < y) below (Nat.mulComm p 9007199254740992))
  arithmetic [less]

theorem Float.Theory.pow53: 9007199254740992 = Nat.pow 2 53 := byComputing

theorem Float.Theory.powLtDouble ∀ (n: Nat): Nat.pow 2 n < Nat.pow 2 (Succ n) :=
  arithmetic [Nat.powSucc 2 n, Nat.powSuccPos 1 n]

theorem Float.Theory.mulPowLe ∀ (k e b: Nat) (kb: k ≤ Nat.pow 2 b): k * Nat.pow 2 e ≤ Nat.pow 2 (b + e) :=
  J (y w => k * Nat.pow 2 e ≤ y) (Nat.leMulRight k (Nat.pow 2 b) (Nat.pow 2 e) kb) (Nat.powAdd 2 b e).flipped

--| Grid points of up to 53 bits at spacing `2^e` are below 2^2098 units if `53 + e ≤ 2097`.
theorem Float.Theory.gridRoom ∀ (k e: Nat)
    (kb: k ≤ Nat.pow 2 53)
    (room: 53 + e ≤ 2097):
    k * Nat.pow 2 e < Nat.pow 2 2098 :=
  let kLe: k * Nat.pow 2 e ≤ Nat.pow 2 (53 + e) := Float.Theory.mulPowLe k e 53 kb
  Float.Theory.leLessTrans
    (k * Nat.pow 2 e)
    (Nat.pow 2 2097)
    (Nat.pow 2 2098)
    (Nat.leTrans (k * Nat.pow 2 e) (Nat.pow 2 (53 + e)) (Nat.pow 2 2097) kLe (Nat.powMono 1 (53 + e) 2097 room))
    (Float.Theory.powLtDouble 2097)

theorem Float.Theory.absDiffBelow ∀ (t a h: Nat) (split: t = a + h): Nat.absDiff a t = h :=
  rewrite Float.Theory.absDiffDef a t then arithmetic [split]

theorem Float.Theory.absDiffAbove ∀ (t a h p: Nat) (split: t = a + h) (hp: h < p): Nat.absDiff (a + p) t = p - h :=
  rewrite Float.Theory.absDiffDef (a + p) t then arithmetic [split, hp]

--| `roundsToSpacing` with the quotient and remainder named.
theorem Float.Theory.roundsToSpacingAt ∀ (t d r e q h: Nat)
    (spec: Float.Theory.RoundsTo t d r)
    (fr: r < 9218868437227405312)
    (split: t = q * (d * Nat.pow 2 e) + h)
    (hp: h < d * Nat.pow 2 e)
    (qTop: q + 1 ≤ 9007199254740992)
    (room: 53 + e ≤ 2097):
    Nat.absDiff (Float.Theory.magUnits r * d) t + Nat.absDiff (Float.Theory.magUnits r * d) t ≤ d * Nat.pow 2 e :=
  let p: Nat := d * Nat.pow 2 e
  let qb: q ≤ 9007199254740992 := arithmetic [qTop]
  let below: Nat.absDiff (Float.Theory.magUnits r * d) t ≤ Nat.absDiff (q * Nat.pow 2 e * d) t :=
    Float.Theory.roundsToGrid t d r q e spec fr qb
      (Float.Theory.gridRoom q e (J (y w => q ≤ y) qb Float.Theory.pow53) room)
  let above: Nat.absDiff (Float.Theory.magUnits r * d) t ≤ Nat.absDiff ((q + 1) * Nat.pow 2 e * d) t :=
    Float.Theory.roundsToGrid t d r
      (q + 1)
      e
      spec
      fr
      qTop
      (Float.Theory.gridRoom (q + 1) e (J (y w => q + 1 ≤ y) qTop Float.Theory.pow53) room)
  let eq1: q * Nat.pow 2 e * d = q * p := algebra
  let eq2: (q + 1) * Nat.pow 2 e * d = q * p + p := algebra
  Float.Theory.halfSpacing
    (Nat.absDiff (Float.Theory.magUnits r * d) t)
    h
    p
    (J
      (y w => Nat.absDiff (Float.Theory.magUnits r * d) t ≤ y)
      below
      (Eq.trans (Eq.cong (u => Nat.absDiff u t) eq1) (Float.Theory.absDiffBelow t (q * p) h split)))
    (J
      (y w => Nat.absDiff (Float.Theory.magUnits r * d) t ≤ y)
      above
      (Eq.trans (Eq.cong (u => Nat.absDiff u t) eq2) (Float.Theory.absDiffAbove t (q * p) h p split hp)))
    hp

theorem Float.Theory.powLessReflect ∀ (a b: Nat) (h: Nat.pow 2 a < Nat.pow 2 b): a < b := match c: Nat.leq b a with
  | True => Void.impossible (arithmetic [h, Nat.powMono 1 b a (arithmetic [c])])
  | False => arithmetic [c]

--| `d · 2^a ≤ t < d · 2^b` puts `a` below `b`.
theorem Float.Theory.powRoom ∀ (d t a b: Nat) (low: d * Nat.pow 2 a ≤ t) (small: t < d * Nat.pow 2 b): a < b :=
  match c: Nat.leq b a with
    | True =>
      Void.impossible
        (arithmetic [
          low,
          small,
          Float.Theory.mulLeLeft (Nat.pow 2 b) (Nat.pow 2 a) d (Nat.powMono 1 b a (arithmetic [c]))
        ])
    | False => arithmetic [c]

--| The relative error bound in the normal range: `t / d` from 2^53 units up,
--| whose bit length is `b`.
theorem Float.Theory.relErrorNormal ∀ (t d r n rem b: Nat)
    (spec: Float.Theory.RoundsTo t d r)
    (fr: r < 9218868437227405312)
    (pd: 0 < d)
    (split0: t = n * d + rem)
    (rlt: rem < d)
    (big: 9007199254740992 ≤ n)
    (bs: Float.Theory.IsBitLength n b)
    (roomOf: ∀ (e: Nat) => d * Nat.pow 2 (e + 52) ≤ t → 53 + e ≤ 2097):
    Nat.absDiff (Float.Theory.magUnits r * d) t * 9007199254740992 ≤ t + d * 4503599627370496 :=
  let b53: 53 < b :=
    Float.Theory.powLessReflect 53 b (Float.Theory.leLessTrans (Nat.pow 2 53) n (Nat.pow 2 b) big bs.left)
  let e: Nat := b - 53
  let eb: b = e + 53 := arithmetic [b53]
  let x: Nat := Nat.pow 2 e
  let pb: Nat.pow 2 b = x * 9007199254740992 := rewrite eb then Nat.powAdd 2 e 53
  let nHigh: n + 1 ≤ x * 9007199254740992 := arithmetic [bs.left, pb]
  let nLow: x * 4503599627370496 ≤ n := arithmetic [bs.right, pb]
  let pp: Nat := d * x
  let lowN: x * 4503599627370496 * d ≤ n * d := Nat.leMulRight (x * 4503599627370496) n d nLow
  let lowE: x * 4503599627370496 * d = pp * 4503599627370496 := algebra
  let low: pp * 4503599627370496 ≤ t := arithmetic [lowN, lowE, split0]
  let highN: (n + 1) * d ≤ x * 9007199254740992 * d := Nat.leMulRight (n + 1) (x * 9007199254740992) d nHigh
  let highE1: (n + 1) * d = n * d + d := algebra
  let highE2: x * 9007199254740992 * d = pp * 9007199254740992 := algebra
  let top: t < pp * 9007199254740992 := arithmetic [highN, highE1, highE2, split0, rlt]
  let xPos: 0 < x := Nat.powSuccPos 1 e
  let ppPos: 0 < pp := arithmetic [Float.Theory.mulLeLeft 1 x d (arithmetic [xPos]), pd]
  let q: Nat := t / pp
  let h: Nat := t % pp
  let split: t = q * pp + h := Nat.divModEq t pp
  let hp: h < pp := Nat.modLess t pp (arithmetic [ppPos])
  let qTop: q + 1 ≤ 9007199254740992 := Float.Theory.quotientRoom t pp q h split top
  let lowPow: d * Nat.pow 2 (e + 52) ≤ t :=
    J
      (y w => d * y ≤ t)
      (rewrite (algebra: d * (x * Nat.pow 2 52) = pp * 4503599627370496) then low)
      (Nat.powAdd 2 e 52).flipped
  let room: 53 + e ≤ 2097 := roomOf e lowPow
  let sp := Float.Theory.roundsToSpacingAt t d r e q h spec fr split hp qTop room
  arithmetic [sp, low]

theorem Float.Theory.succLeOf ∀ (a b: Nat) (h: a + 52 < b): 53 + a ≤ b := arithmetic [h]

--| Below 2^2097 units, every binade's grid has room for its next point.
theorem Float.Theory.roomFromSmall ∀ (d t: Nat)
    (small: t < d * Nat.pow 2 2097) (e: Nat)
    (low: d * Nat.pow 2 (e + 52) ≤ t):
    53 + e ≤ 2097 :=
  Float.Theory.succLeOf e 2097 (Float.Theory.powRoom d t (e + 52) 2097 low small)

theorem Float.Theory.posNonzeroNat ∀ (n: Nat) (h: 0 < n): n ≠ 0 := arithmetic [h]

theorem Float.Theory.relErrorBy ∀ (t d r n rem: Nat)
    (spec: Float.Theory.RoundsTo t d r)
    (fr: r < 9218868437227405312)
    (pd: 0 < d)
    (split0: t = n * d + rem)
    (rlt: rem < d)
    (roomOf: ∀ (e: Nat) => d * Nat.pow 2 (e + 52) ≤ t → 53 + e ≤ 2097):
    Nat.absDiff (Float.Theory.magUnits r * d) t * 9007199254740992 ≤ t + d * 4503599627370496 :=
  match c: Nat.leq 9007199254740992 n with
    | True =>
      Float.Theory.relErrorNormal t d r n rem
        (Float.Model.bitLength n)
        spec
        fr
        pd
        split0
        rlt
        (arithmetic [c])
        (Float.Theory.bitLengthSpec n (arithmetic [c]))
        roomOf
    | False =>
      let e0: d * Nat.pow 2 0 = d := algebra
      let sp: Nat.absDiff (Float.Theory.magUnits r * d) t + Nat.absDiff (Float.Theory.magUnits r * d) t
        ≤ d * Nat.pow 2 0 :=
        Float.Theory.roundsToSpacingAt t d r 0 n rem spec fr
          (rewrite e0 then split0)
          (rewrite e0 then rlt)
          (arithmetic [c])
          byComputing
      arithmetic [sp, e0]

--| The standard error model, from the rounding specification: a rounding
--| to a finite pattern `r` of `t / d` units, below 2^2097 units (2^1023),
--| misses by at most `t / d` × 2^-53 in the normal range and half a unit
--| (2^-1075) below it: `2^53 |r − t/d| ≤ t/d + 2^52` units.
theorem Float.Theory.roundsToRelError ∀ (t d r: Nat)
    (spec: Float.Theory.RoundsTo t d r)
    (fr: r < 9218868437227405312)
    (pd: 0 < d)
    (small: t < d * Nat.pow 2 2097):
    Nat.absDiff (Float.Theory.magUnits r * d) t * 9007199254740992 ≤ t + d * 4503599627370496 :=
  Float.Theory.relErrorBy t d r
    (t / d)
    (t % d)
    spec
    fr
    pd
    (Nat.divModEq t d)
    (Nat.modLess t d (Float.Theory.posNonzeroNat d pd))
    (Float.Theory.roomFromSmall d t small)

--| The magnitude of a rounding of a nonzero numerator is the rounded magnitude.
theorem Float.Theory.ratioMagnitude ∀ (num: Int) (den: Nat) (scale: Int) (z: Bool)
    (nz: 0 < Int.natAbs num)
    (mb: Float.Model.roundMagnitude False (Int.natAbs num) den (Int.add scale (OfNat 1074)) ≤ 9218868437227405312):
    Float.Model.magnitude (Float.Model.roundRatio num den scale z)
      = Float.Model.roundMagnitude False (Int.natAbs num) den (Int.add scale (OfNat 1074)) :=
  match num with
    | OfNat (Succ k) =>
      let m: Nat := Float.Model.roundMagnitude False (Succ k) den (Int.add scale (OfNat 1074))
      let c: Nat.leq 9223372036854775808 m = False := arithmetic [mb]
      rewrite Float.Theory.roundRatioPos k den scale z, c
    | NegSucc k => rewrite Float.Theory.roundRatioNeg k den scale z

theorem Float.Theory.ratioMagnitudeBound ∀ (num: Int) (den: Nat) (scale: Int) (z: Bool)
    (nz: 0 < Int.natAbs num)
    (pd: 0 < den):
    Float.Model.roundMagnitude False (Int.natAbs num) den (Int.add scale (OfNat 1074)) ≤ 9218868437227405312 :=
  (Float.Theory.roundMagnitudeSpec (Int.natAbs num) den (Int.add scale (OfNat 1074)) nz pd).bounded

theorem Float.Theory.ratioZeroUnitsAt ∀ (num: Int) (den: Nat) (scale: Int) (z: Bool)
    (n0: Int.natAbs num = 0):
    Float.Theory.magUnits (Float.Model.magnitude (Float.Model.roundRatio num den scale z)) = 0 :=
  let e: num = OfNat 0 := arithmetic [n0]
  rewrite e then match z with | True | False => byComputing

theorem Float.Theory.divRelErrorZero ∀ (a den n p: Nat)
    (n0: n = 0)
    (a0: a = 0):
    Nat.absDiff (a * den) (n * p) * 9007199254740992 ≤ n * p + den * 4503599627370496 :=
  rewrite n0, a0

--| The standard error model for `/` by a positive finite double: for a
--| finite quotient below 2^1023 in size, `|x / d|` misses `|x| / d` by at
--| most 2^-53 of it, or half a unit (2^-1075) below the normal range. In
--| units of 2^-1074: `2^53 |q·d − x·2^1074| ≤ x·2^1074 + d·2^52`, where
--| `q`, `d` and `x` are the sizes of the quotient's, divisor's and dividend's units.
theorem Float.divRelError ∀ (x d: Float)
    (pos: 0.0 < d)
    (fd: Float.isFinite d = True)
    (fx: Float.isFinite x = True)
    (fq: Float.isFinite (x / d) = True)
    (small: Int.natAbs (Float.Theory.units x) * Float.Model.pow2 1074
      < Int.natAbs (Float.Theory.units d) * Nat.pow 2 2097):
    Nat.absDiff
      (Int.natAbs (Float.Theory.units (x / d)) * Int.natAbs (Float.Theory.units d))
      (Int.natAbs (Float.Theory.units x) * Float.Model.pow2 1074)
      * 9007199254740992
      ≤ Int.natAbs (Float.Theory.units x) * Float.Model.pow2 1074
        + Int.natAbs (Float.Theory.units d) * 4503599627370496 :=
  let ux: Int := Float.Theory.units x
  let n: Nat := Int.natAbs ux
  let den: Nat := Int.natAbs (Float.Theory.units d)
  let pd: 0 < den := Float.Theory.natAbsPos (Float.Model.units d.bits) (Float.Theory.unitsPositive d pos)
  let qb: (x / d).bits = Float.Model.roundRatio ux den (OfNat 0) (Float.Model.signBit x.bits) :=
    Float.Theory.quotientBits x d pos fd fx
  let fqb: Float.Theory.FiniteBits (x / d).bits := Float.Theory.finiteBits (x / d) fq
  let qAbs: Int.natAbs (Float.Theory.units (x / d)) = Float.Theory.magUnits (Float.Model.magnitude (x / d).bits) :=
    Float.Theory.natAbsUnits (x / d).bits
  match Float.Theory.zeroOrPos n with
    | Inl n0 =>
      Float.Theory.divRelErrorZero
        (Int.natAbs (Float.Theory.units (x / d)))
        den
        n
        (Float.Model.pow2 1074)
        n0
        (rewrite qAbs, qb then Float.Theory.ratioZeroUnitsAt ux den (OfNat 0) (Float.Model.signBit x.bits) n0)
    | Inr np =>
      let m: Nat := Float.Model.roundMagnitude False n den (OfNat 1074)
      let mm: Float.Model.magnitude (x / d).bits = m :=
        J
          (b w => Float.Model.magnitude b = m)
          (Float.Theory.ratioMagnitude ux den
            (OfNat 0)
            (Float.Model.signBit x.bits)
            np
            (Float.Theory.ratioMagnitudeBound ux den (OfNat 0) (Float.Model.signBit x.bits) np pd))
          qb.flipped
      let spec: Float.Theory.RoundsTo (n * Float.Model.pow2 1074) den m :=
        Float.Theory.roundMagnitudeSpec n den (OfNat 1074) np pd
      let fm: m < 9218868437227405312 := J (y w => y < 9218868437227405312) fqb mm
      rewrite qAbs, mm then Float.Theory.roundsToRelError (n * Float.Model.pow2 1074) den m spec fm pd small

test "Float.divRelError" :=
  let err := (x d: Float) =>
    Nat.absDiff
      (Int.natAbs (Float.Theory.units (x / d)) * Int.natAbs (Float.Theory.units d))
      (Int.natAbs (Float.Theory.units x) * Float.Model.pow2 1074)
      * 9007199254740992
  let bound := (x d: Float) =>
    Int.natAbs (Float.Theory.units x) * Float.Model.pow2 1074 + Int.natAbs (Float.Theory.units d) * 4503599627370496
  err 1.0 3.0 ≤ bound 1.0 3.0
    ∧ err (-359.9) 0.1 ≤ bound (-359.9) 0.1
    ∧ err 5e-324 3.0 ≤ bound 5e-324 3.0
    ∧ 0 < err 1.0 3.0

theorem Float.Theory.divNearArith ∀ (ux uq: Int) (n q den p: Nat)
    (en: n = Int.natAbs ux)
    (eq: q = Int.natAbs uq)
    (pd: 0 < den)
    (err: Nat.absDiff (q * den) (n * p) * 9007199254740992 ≤ n * p + den * 4503599627370496)
    (sign: ((Int.less (OfNat 0) ux = True) ∧ (Int.leq (OfNat 0) uq = True))
      ∨ (((Int.less ux (OfNat 0) = True) ∧ (Int.leq uq (OfNat 0) = True)) ∨ (ux = OfNat 0))):
    (Int.leq
      (Int.mul (Int.mul uq (OfNat den)) (OfNat 9007199254740992))
      (Int.add (Int.mul (Int.mul ux (OfNat p)) (OfNat 9007199254740992)) (OfNat (n * p + den * 4503599627370496)))
      = True)
      ∧ (Int.leq
        (Int.mul (Int.mul ux (OfNat p)) (OfNat 9007199254740992))
        (Int.add (Int.mul (Int.mul uq (OfNat den)) (OfNat 9007199254740992)) (OfNat (n * p + den * 4503599627370496)))
        = True) :=
  let d: Nat.absDiff (q * den) (n * p) = ((q * den) - (n * p)) + ((n * p) - (q * den)) :=
    Float.Theory.absDiffDef (q * den) (n * p)
  match sign with
    | Inl b =>
      let uqe: uq = OfNat q := arithmetic [eq, b.right]
      let uxe: ux = OfNat n := arithmetic [en, b.left]
      rewrite uqe, uxe then Both (arithmetic [d, err]) (arithmetic [d, err])
    | Inr r =>
      match r with
        | Inl b =>
          let uqe: uq = Int.neg (OfNat q) := arithmetic [eq, b.right]
          let uxe: ux = Int.neg (OfNat n) := arithmetic [en, b.left]
          let mq := Float.Theory.negMul q den
          let mn := Float.Theory.negMul n p
          rewrite uqe, uxe then Both (arithmetic [d, err, mq, mn]) (arithmetic [d, err, mq, mn])
        | Inr z =>
          let nz: n = 0 := arithmetic [en, z]
          let np0: n * p = 0 := rewrite nz
          match Float.Theory.zeroOrPos q with
            | Inl q0 =>
              let u0: uq = OfNat 0 := arithmetic [eq, q0]
              rewrite z, u0, nz then Both (arithmetic) (arithmetic)
            | Inr qp =>
              let h: 1 * den ≤ q * den := Nat.leMulRight 1 q den qp
              Both (arithmetic [d, err, np0, h, pd]) (arithmetic [d, err, np0, h, pd])

--| `Float.divRelError` for signed units: `|x / d|` misses `x / d` by at
--| most 2^-53 of it (or half a unit below the normal range), both ways, with
--| the signs kept. With `ux`, `uq` and `n` the units of `x` and `x / d` and
--| the size of `x`'s, `den` the size of `d`'s units and `p` = 2^1074:
--| `2^53 (uq·den − ux·p) ≤ n·p + den·2^52` and `2^53 (ux·p − uq·den) ≤ n·p +
--| den·2^52`, written without subtraction. `sign` says the quotient's units
--| are of `x`'s sign (as `0 < ux` gives `0 ≤ uq`, shown by `Float.divMonotone`
--| against 0.0); it is the caller's, since a zero dividend's sign takes a
--| computed `0.0 / d = 0.0` or `-0.0 / d = -0.0`.
theorem Float.divNear ∀ (x d: Float)
    (pos: 0.0 < d)
    (fd: Float.isFinite d = True)
    (fx: Float.isFinite x = True)
    (fq: Float.isFinite (x / d) = True)
    (small: Int.natAbs (Float.Theory.units x) * Float.Model.pow2 1074
      < Int.natAbs (Float.Theory.units d) * Nat.pow 2 2097)
    (sign: ((Int.less (OfNat 0) (Float.Theory.units x) = True)
      ∧ (Int.leq (OfNat 0) (Float.Theory.units (x / d)) = True))
      ∨ (((Int.less (Float.Theory.units x) (OfNat 0) = True) ∧ (Int.leq (Float.Theory.units (x / d)) (OfNat 0) = True))
        ∨ (Float.Theory.units x = OfNat 0))):
    (Int.leq
      (Int.mul
        (Int.mul (Float.Theory.units (x / d)) (OfNat (Int.natAbs (Float.Theory.units d))))
        (OfNat 9007199254740992))
      (Int.add
        (Int.mul (Int.mul (Float.Theory.units x) (OfNat (Float.Model.pow2 1074))) (OfNat 9007199254740992))
        (OfNat
          (Int.natAbs (Float.Theory.units x) * Float.Model.pow2 1074
            + Int.natAbs (Float.Theory.units d) * 4503599627370496)))
      = True)
      ∧ (Int.leq
        (Int.mul (Int.mul (Float.Theory.units x) (OfNat (Float.Model.pow2 1074))) (OfNat 9007199254740992))
        (Int.add
          (Int.mul
            (Int.mul (Float.Theory.units (x / d)) (OfNat (Int.natAbs (Float.Theory.units d))))
            (OfNat 9007199254740992))
          (OfNat
            (Int.natAbs (Float.Theory.units x) * Float.Model.pow2 1074
              + Int.natAbs (Float.Theory.units d) * 4503599627370496)))
        = True) :=
  Float.Theory.divNearArith
    (Float.Theory.units x)
    (Float.Theory.units (x / d))
    (Int.natAbs (Float.Theory.units x))
    (Int.natAbs (Float.Theory.units (x / d)))
    (Int.natAbs (Float.Theory.units d))
    (Float.Model.pow2 1074)
    byComputing
    byComputing
    (Float.Theory.natAbsPos (Float.Model.units d.bits) (Float.Theory.unitsPositive d pos))
    (Float.divRelError x d pos fd fx fq small)
    sign

test "Float.divNear" :=
  let near := (x d: Float) =>
    let ux := Float.Theory.units x
    let y :=
      Int.mul
        (Int.mul (Float.Theory.units (x / d)) (OfNat (Int.natAbs (Float.Theory.units d))))
        (OfNat 9007199254740992)
    let z := Int.mul (Int.mul ux (OfNat (Float.Model.pow2 1074))) (OfNat 9007199254740992)
    let h := OfNat (Int.natAbs ux * Float.Model.pow2 1074 + Int.natAbs (Float.Theory.units d) * 4503599627370496)
    (Int.leq y (Int.add z h) = True) ∧ (Int.leq z (Int.add y h) = True)
  near 1.0 3.0 ∧ near (-359.9) 0.1 ∧ near (-1.0) 3.0

theorem Float.Theory.mulRelErrorZero ∀ (a n p: Nat)
    (n0: n = 0)
    (a0: a = 0):
    Nat.absDiff (a * p) n * 9007199254740992 ≤ n + p * 4503599627370496 :=
  rewrite n0, a0

--| The standard error model for `*` of finite doubles: for a finite
--| product below 2^1023 in size, `|x * c|` misses `|x|·|c|` by at most 2^-53
--| of it, or half a unit (2^-1075) below the normal range. In units of
--| 2^-1074, with `n` the size of the units' product (2^1074 times the exact
--| product's): `2^53 |p·2^1074 − n| ≤ n + 2^1074·2^52`.
theorem Float.mulRelError ∀ (x c: Float)
    (fx: Float.isFinite x = True)
    (fc: Float.isFinite c = True)
    (fp: Float.isFinite (x * c) = True)
    (small: Int.natAbs (Int.mul (Float.Theory.units x) (Float.Theory.units c))
      < Float.Model.pow2 1074 * Nat.pow 2 2097):
    Nat.absDiff
      (Int.natAbs (Float.Theory.units (x * c)) * Float.Model.pow2 1074)
      (Int.natAbs (Int.mul (Float.Theory.units x) (Float.Theory.units c)))
      * 9007199254740992
      ≤ Int.natAbs (Int.mul (Float.Theory.units x) (Float.Theory.units c)) + Float.Model.pow2 1074 * 4503599627370496 :=
  let num: Int := Int.mul (Float.Theory.units x) (Float.Theory.units c)
  let n: Nat := Int.natAbs num
  let z: Bool := Bool.xor (Float.Model.signBit x.bits) (Float.Model.signBit c.bits)
  let pb: (x * c).bits = Float.Model.roundRatio num 1 (-2148) z := Float.Theory.mulBitsOf x c fx fc
  let fpb: Float.Theory.FiniteBits (x * c).bits := Float.Theory.finiteBits (x * c) fp
  let pAbs: Int.natAbs (Float.Theory.units (x * c)) = Float.Theory.magUnits (Float.Model.magnitude (x * c).bits) :=
    Float.Theory.natAbsUnits (x * c).bits
  let pd: 0 < Float.Model.pow2 1074 := byComputing
  match Float.Theory.zeroOrPos n with
    | Inl n0 =>
      Float.Theory.mulRelErrorZero
        (Int.natAbs (Float.Theory.units (x * c)))
        n
        (Float.Model.pow2 1074)
        n0
        (rewrite pAbs, pb then Float.Theory.ratioZeroUnitsAt num 1 (-2148) z n0)
    | Inr np =>
      let m: Nat := Float.Model.roundMagnitude False n 1 (-1074)
      let mm: Float.Model.magnitude (x * c).bits = m :=
        J
          (b w => Float.Model.magnitude b = m)
          (Float.Theory.ratioMagnitude num 1
            (-2148)
            z
            np
            (Float.Theory.ratioMagnitudeBound num 1 (-2148) z np byComputing))
          pb.flipped
      let spec: Float.Theory.RoundsTo n (Float.Model.pow2 1074) m :=
        Float.Theory.roundMagnitudeSpec n 1 (-1074) np byComputing
      let fm: m < 9218868437227405312 := J (y w => y < 9218868437227405312) fpb mm
      rewrite pAbs, mm then Float.Theory.roundsToRelError n (Float.Model.pow2 1074) m spec fm pd small

theorem Float.Theory.addRelErrorZero ∀ (a n: Nat)
    (n0: n = 0)
    (a0: a = 0):
    Nat.absDiff (a * 1) n * 9007199254740992 ≤ n + 1 * 4503599627370496 :=
  rewrite n0, a0

--| The standard error model for `+` of finite doubles: for a finite sum
--| below 2^1023 in size, `|x + c|` misses the exact sum's size by at most
--| 2^-53 of it, or half a unit (2^-1075) below the normal range. In units
--| of 2^-1074, with `n` the size of the units' sum: `2^53 |s − n| ≤ n + 2^52`.
--| (In the subnormal range the sum is exact; the bound doesn't say so.)
theorem Float.addRelError ∀ (x c: Float)
    (fx: Float.isFinite x = True)
    (fc: Float.isFinite c = True)
    (fs: Float.isFinite (x + c) = True)
    (small: Int.natAbs (Int.add (Float.Theory.units x) (Float.Theory.units c)) < 1 * Nat.pow 2 2097):
    Nat.absDiff
      (Int.natAbs (Float.Theory.units (x + c)) * 1)
      (Int.natAbs (Int.add (Float.Theory.units x) (Float.Theory.units c)))
      * 9007199254740992
      ≤ Int.natAbs (Int.add (Float.Theory.units x) (Float.Theory.units c)) + 1 * 4503599627370496 :=
  let num: Int := Int.add (Float.Theory.units x) (Float.Theory.units c)
  let n: Nat := Int.natAbs num
  let z: Bool := Float.Model.signBit x.bits ∧ Float.Model.signBit c.bits
  let sb: (x + c).bits = Float.Model.roundRatio num 1 (-1074) z := Float.Theory.addBitsOf x c fx fc
  let fsb: Float.Theory.FiniteBits (x + c).bits := Float.Theory.finiteBits (x + c) fs
  let sAbs: Int.natAbs (Float.Theory.units (x + c)) = Float.Theory.magUnits (Float.Model.magnitude (x + c).bits) :=
    Float.Theory.natAbsUnits (x + c).bits
  match Float.Theory.zeroOrPos n with
    | Inl n0 =>
      Float.Theory.addRelErrorZero
        (Int.natAbs (Float.Theory.units (x + c)))
        n
        n0
        (rewrite sAbs, sb then Float.Theory.ratioZeroUnitsAt num 1 (-1074) z n0)
    | Inr np =>
      let m: Nat := Float.Model.roundMagnitude False n 1 (OfNat 0)
      let mm: Float.Model.magnitude (x + c).bits = m :=
        J
          (b w => Float.Model.magnitude b = m)
          (Float.Theory.ratioMagnitude num 1
            (-1074)
            z
            np
            (Float.Theory.ratioMagnitudeBound num 1 (-1074) z np byComputing))
          sb.flipped
      let spec: Float.Theory.RoundsTo n 1 m :=
        J
          (u w => Float.Theory.RoundsTo u 1 m)
          (Float.Theory.roundMagnitudeSpec n 1 (OfNat 0) np byComputing)
          (algebra: n * 1 = n)
      let fm: m < 9218868437227405312 := J (y w => y < 9218868437227405312) fsb mm
      rewrite sAbs, mm then Float.Theory.roundsToRelError n 1 m spec fm byComputing small

-- `round`'s specification

--| `floorDiv` finds `n` for any value in `[n·p, n·p + p)`.
theorem Float.Theory.floorDivNear ∀ (v n: Int) (p: Nat)
    (lo: Int.leq (Int.mul n (OfNat p)) v = True)
    (hi: Int.less v (Int.add (Int.mul n (OfNat p)) (OfNat p)) = True):
    Float.Model.floorDiv (Int.isNeg v) (Int.natAbs v) p = n :=
  let h: Nat := Int.natAbs (Int.sub v (Int.mul n (OfNat p)))
  let e: v = Int.add (Int.mul n (OfNat p)) (OfNat h) := arithmetic [lo]
  rewrite e then Float.Theory.floorDivWhole n h p (arithmetic [hi, lo])

--| `roundBits` of a finite pattern within half a unit below, or under half
--| above, `n`: `n`, with the pattern's zero sign.
theorem Float.Theory.roundBitsNear ∀ (a: Nat) (n: Int)
    (sp: Float.Model.isSpecial a = False)
    (lo: Int.leq
      (Int.mul n (OfNat (Float.Model.pow2 1074)))
      (Int.add (Float.Model.units a) (OfNat (Float.Model.pow2 1073)))
      = True)
    (hi: Int.less
      (Int.add (Float.Model.units a) (OfNat (Float.Model.pow2 1073)))
      (Int.add (Int.mul n (OfNat (Float.Model.pow2 1074))) (OfNat (Float.Model.pow2 1074)))
      = True):
    Float.Model.roundBits a = Float.Model.roundScaled n 0 (Float.Model.signBit a) :=
  let v: Int := Int.add (Float.Model.units a) (OfNat (Float.Model.pow2 1073))
  let p: Nat := Float.Model.pow2 1074
  let s: Bool := Float.Model.signBit a
  Eq.trans
    (Float.Theory.ifFalse
      (Float.Model.isSpecial a)
      a
      (Float.Model.roundScaled (Float.Model.floorDiv (Int.isNeg v) (Int.natAbs v) p) 0 s)
      sp)
    (Eq.cong (k => Float.Model.roundScaled k 0 s) (Float.Theory.floorDivNear v n p lo hi))

--| `round`'s specification: a finite `y` from half a unit below the whole
--| double `k` (of value `n ≠ 0`) up to just under half a unit above it
--| rounds to `k`. Units are 2^-1074, so half a unit is `2^1073` of them.
theorem Float.roundNear ∀ (y k: Float) (n: Int)
    (fy: Float.isFinite y = True)
    (fk: Float.isFinite k = True)
    (whole: Float.Theory.units k = Int.mul n (OfNat (Float.Model.pow2 1074)))
    (nz: n ≠ OfNat 0)
    (lo: Int.leq
      (Int.mul n (OfNat (Float.Model.pow2 1074)))
      (Int.add (Float.Theory.units y) (OfNat (Float.Model.pow2 1073)))
      = True)
    (hi: Int.less
      (Int.add (Float.Theory.units y) (OfNat (Float.Model.pow2 1073)))
      (Int.add (Int.mul n (OfNat (Float.Model.pow2 1074))) (OfNat (Float.Model.pow2 1074)))
      = True):
    Float.round y = k :=
  let p: Nat := Float.Model.pow2 1074
  let s: Bool := Float.Model.signBit y.bits
  let near: Float.Model.roundBits y.bits = Float.Model.roundScaled n 0 s :=
    Float.Theory.roundBitsNear y.bits n (Float.Theory.notSpecialOf y.bits (Float.Theory.finiteBits y fy)) lo hi
  let valid: Float.isValid (Float.Model.roundBits y.bits) = True :=
    J (r w => Float.isValid r = True) (Float.Theory.roundRatioValid 1 (OfNat 0) s byComputing n) near.flipped
  let e: Float.round y = Float.ofBits (Float.Model.roundBits y.bits) := match y with
    | { bits = a, valid = v } => byComputing
  Float.bitsExt
    (Float.round y)
    k
    (calc (Float.round y).bits
      _ = (Float.ofBits (Float.Model.roundBits y.bits)).bits := Eq.cong (r => r.bits) e
      _ = Float.Model.roundBits y.bits := Float.Theory.ofBitsBits (Float.Model.roundBits y.bits) valid
      _ = Float.Model.roundScaled n 0 s := near
      _ = Float.Model.roundRatio (Int.mul n (OfNat p)) 1 (-1074) s := Float.Theory.roundWhole n s
      _ = Float.Model.roundRatio (Int.mul n (OfNat p)) 1 (-1074) (Float.Model.signBit k.bits) :=
        Float.Theory.roundRatioSignIrrelevant 1
          (-1074)
          s
          (Float.Model.signBit k.bits)
          (Int.mul n (OfNat p))
          (Float.Theory.mulNonzero n p byComputing nz)
      _ = Float.Model.roundRatio (Float.Theory.units k) 1 (-1074) (Float.Model.signBit k.bits) :=
        Eq.cong (u => Float.Model.roundRatio u 1 (-1074) (Float.Model.signBit k.bits)) whole.flipped
      _ = k.bits := Float.Theory.roundRatioUnitsBits k.bits (Float.Theory.finiteBits k fk))

test "Float.roundNear" :=
  Float.round 2.4999999999999996 == 2.0
    ∧ Float.round 1.5 == 2.0
    ∧ Float.round (-2.5) == -2.0
    ∧ Float.round (-2.5000000000000004) == -3.0

-- Lemmas moved from the Whereabouts app (SW-3873, SW-3886)

--| Flipping the sign bit of a 64-bit word flips `signBit`.
theorem Float.Theory.signFlipBits ∀ (n: Nat)
    (v: n < 18446744073709551616):
    Float.Model.signBit (Float.flipSignBits n) = ¬(Float.Model.signBit n) :=
  match c: Nat.leq 9223372036854775808 n with
    | True =>
      let c2: Nat.leq 9223372036854775808 (n - 9223372036854775808) = False := arithmetic [c, v]
      rewrite c2
    | False =>
      let c2: Nat.leq 9223372036854775808 (n + 9223372036854775808) = True := arithmetic
      rewrite c2

--| `Int.signed` with the opposite sign is the negation.
theorem Float.Theory.signedNot ∀ (s: Bool) (m: Nat): Int.signed (¬s) m = Int.neg (Int.signed s m) := match s with
  | True => Float.Theory.signedFlip False m
  | False => Float.Theory.signedFlip True m

--| Negation negates units, for every double but the NaN: `units (-x) = -units x`.
theorem Float.Theory.unitsNeg ∀ (x: Float)
    (nx: Float.isNaN x = False):
    Float.Theory.units (-x) = Int.neg (Float.Theory.units x) :=
  let n: Nat := x.bits
  let v: n < 18446744073709551616 := Float.Theory.bitsBelow x
  let flip: Float.Model.units (Float.flipSignBits n) = Int.neg (Float.Model.units n) := calc Float.Model.units
    (Float.flipSignBits n)
    _ = Int.signed
        (Float.Model.signBit (Float.flipSignBits n))
        (Float.Theory.magUnits (Float.Model.magnitude (Float.flipSignBits n))) :=
      Float.Theory.unitsMag (Float.flipSignBits n)
    _ = Int.signed (¬(Float.Model.signBit n)) (Float.Theory.magUnits (Float.Model.magnitude n)) :=
      Eq.cong2
        (s m => Int.signed s (Float.Theory.magUnits m))
        (Float.Theory.signFlipBits n v)
        (Float.Theory.magFlip n v)
    _ = Int.neg (Int.signed (Float.Model.signBit n) (Float.Theory.magUnits (Float.Model.magnitude n))) :=
      Float.Theory.signedNot (Float.Model.signBit n) (Float.Theory.magUnits (Float.Model.magnitude n))
    _ = Int.neg (Float.Model.units n) := Eq.cong Int.neg (Float.Theory.unitsMag n).flipped
  J (b w => Float.Model.units b = Int.neg (Float.Model.units n)) flip (Float.Theory.negBits x nx).flipped

--| `<=` on doubles is transitive.
theorem Float.Theory.leTrans ∀ (x y z: Float) (xy: x <= y) (yz: y <= z): x <= z :=
  let a: Int.leq (Float.orderKey x) (Float.orderKey y) = True := xy
  let b: Int.leq (Float.orderKey y) (Float.orderKey z) = True := yz
  (arithmetic: Int.leq (Float.orderKey x) (Float.orderKey z) = True)

--| A double between `-b` and `b` is below `c` in size when `b < c`, for `b`
--| other than the NaN. By cases on `x`'s sign: the keys of `-b` and `b`
--| mirror about -1/2 (`keyFlip`), so `-b <= x` bounds a negative `x`'s
--| magnitude by `b`'s key and `x <= b` a positive one's; `absKey` reads the
--| size's key off the bits.
theorem Float.Theory.absBelowOf ∀ (x b c: Float)
    (nb: Float.isNaN b = False)
    (lo: -b <= x)
    (hi: x <= b)
    (bc: b < c):
    Float.abs x < c :=
  let kn: Float.Theory.key (-b).bits = Int.sub (NegSucc 0) (Float.Theory.key b.bits) :=
    Eq.trans
      (Eq.cong Float.Theory.key (Float.Theory.negBits b nb))
      (Float.Theory.keyFlip b.bits (Float.Theory.bitsBelow b))
  let kb: Int.less (Float.Theory.key b.bits) (Float.orderKey c) = True := bc
  match c2: Nat.leq 9223372036854775808 x.bits with
    | True =>
      let kl: Int.leq (Float.Theory.key (-b).bits) (Float.Theory.key x.bits) = True := lo
      let ks := Float.Theory.keySet x.bits c2
      let low: Nat.leq 9223372036854775808 (x.bits - 9223372036854775808) = False :=
        arithmetic [kl, kn, ks, Float.Theory.bitsBelow x]
      arithmetic [kl, kn, ks, kb, Float.Theory.keyClear (x.bits - 9223372036854775808) low, Float.Theory.absKey x]
    | False =>
      let kh: Int.leq (Float.Theory.key x.bits) (Float.Theory.key b.bits) = True := hi
      let m: Float.Model.magnitude x.bits = x.bits := rewrite c2
      arithmetic [kh, kb, Float.Theory.keyClear x.bits c2, m, Float.Theory.absKey x]

test "Float.Theory.absBelowOf" := Float.abs (-359.5) < 562949953421312.0 ∧ Float.abs 3600.0 < 9007199254740992.0

--| A negative integer: not at least zero.
theorem Float.Theory.intLessZeroOfNotNonneg ∀ (a: Int) (h: Int.leq (OfNat 0) a = False): Int.less a (OfNat 0) = True :=
  arithmetic [h]

--| Strictly below is at most.
theorem Float.Theory.intLeOfLess ∀ (a b: Int) (h: Int.less a b = True): Int.leq a b = True := arithmetic [h]

--| `a * m ≤ b * m + c` when `a` and `b` are within `c / m` of each other: the
--| one-sided half of an absolute-difference bound after scaling by `m`.
theorem Float.Theory.scaledAbsDiffLe ∀ (a b m c: Nat) (h: Nat.absDiff a b * m ≤ c): a * m ≤ b * m + c :=
  let d: Nat := Nat.absDiff a b
  let s: a * m ≤ (b + d) * m := Nat.leMulRight a (b + d) m (arithmetic)
  let e: (b + d) * m = b * m + d * m := algebra
  arithmetic [s, e, h]

--| The error model's bound with the common unit `p` cancelled, from above:
--| `|a p − c p| k ≤ c p + p h` gives `a k ≤ c k + c + h`.
theorem Float.Theory.relCancelUp ∀ (a c p k h: Nat)
    (pp: 0 < p)
    (err: Nat.absDiff (a * p) (c * p) * k ≤ c * p + p * h):
    a * k ≤ c * k + c + h :=
  let s: a * p * k ≤ c * p * k + (c * p + p * h) := Float.Theory.scaledAbsDiffLe (a * p) (c * p) k (c * p + p * h) err
  let e1: a * p * k = a * k * p := algebra
  let e2: c * p * k + (c * p + p * h) = (c * k + c + h) * p := algebra
  Float.Theory.cancelLe (a * k) (c * k + c + h) p pp (rewrite e1.flipped, e2.flipped then s)

--| The same bound from below: `c k ≤ a k + c + h`.
theorem Float.Theory.relCancelDown ∀ (a c p k h: Nat)
    (pp: 0 < p)
    (err: Nat.absDiff (a * p) (c * p) * k ≤ c * p + p * h):
    c * k ≤ a * k + c + h :=
  let s: c * p * k ≤ a * p * k + (c * p + p * h) :=
    Float.Theory.scaledAbsDiffLe (c * p) (a * p) k (c * p + p * h) (rewrite Nat.absDiffComm (c * p) (a * p) then err)
  let e1: c * p * k = c * k * p := algebra
  let e2: a * p * k + (c * p + p * h) = (a * k + c + h) * p := algebra
  Float.Theory.cancelLe (c * k) (a * k + c + h) p pp (rewrite e1.flipped, e2.flipped then s)

--| The error model's two-sided bound with the common unit `p` cancelled: for
--| `aa = a p`, `cc = c p` and `hh = p h`, `|aa − cc| k ≤ cc + hh` gives both
--| `a k ≤ c k + c + h` and `c k ≤ a k + c + h`. (The equations let a caller
--| state the bound on its own terms, such as `Float.addRelError`'s.)
theorem Float.Theory.relCancel ∀ (a c p k h aa cc hh: Nat)
    (pp: 0 < p)
    (ea: aa = a * p)
    (ec: cc = c * p)
    (eh: hh = p * h)
    (err: Nat.absDiff aa cc * k ≤ cc + hh):
    (a * k ≤ c * k + c + h) ∧ (c * k ≤ a * k + c + h) :=
  let e: Nat.absDiff (a * p) (c * p) * k ≤ c * p + p * h := rewrite ea.flipped, ec.flipped, eh.flipped then err
  Both (Float.Theory.relCancelUp a c p k h pp e) (Float.Theory.relCancelDown a c p k h pp e)

--| Regrouping for `relCancelScaled`: `r (v m) m = r (m m) v`.
theorem Float.Theory.scaleLeft ∀ (r v m: Nat): r * (v * m) * m = r * (m * m) * v := algebra

--| Regrouping for `relCancelScaled`.
theorem Float.Theory.scaleRight ∀ (wd v k m h: Nat):
    v * k * wd * m + (v * k * wd + v * m * h) = (wd * (k * m + k) + m * h) * v :=
  algebra

--| The error model's bound when both sides carry a scale `v` (and one a
--| further `m`): `|r v m − v k wd| m ≤ v k wd + v m h` gives
--| `r m m ≤ wd (k m + k) + m h`, with `v` cancelled.
theorem Float.Theory.relCancelScaled ∀ (r wd v k m h: Nat)
    (pv: 0 < v)
    (err: Nat.absDiff (r * (v * m)) (v * k * wd) * m ≤ v * k * wd + v * m * h):
    r * (m * m) ≤ wd * (k * m + k) + m * h :=
  let a: r * (v * m) * m ≤ v * k * wd * m + (v * k * wd + v * m * h) :=
    Float.Theory.scaledAbsDiffLe (r * (v * m)) (v * k * wd) m (v * k * wd + v * m * h) err
  let b: r * (m * m) * v ≤ (wd * (k * m + k) + m * h) * v :=
    rewrite (Float.Theory.scaleLeft r v m).flipped, (Float.Theory.scaleRight wd v k m h).flipped then a
  Float.Theory.cancelLe (r * (m * m)) (wd * (k * m + k) + m * h) v pv b

--| Multiplying a double known to lie between two finite ones by a
--| non-negative finite `c`, when the products with the bounds are finite,
--| keeps it finite and between the products.
theorem Float.mulBetween ∀ (lo x hi c: Float)
    (flo: Float.isFinite lo = True)
    (fhi: Float.isFinite hi = True)
    (fx: Float.isFinite x = True)
    (fc: Float.isFinite c = True)
    (hc: 0.0 <= c)
    (flc: Float.isFinite (lo * c) = True)
    (fhc: Float.isFinite (hi * c) = True)
    (a: lo <= x)
    (b: x <= hi):
    (Float.isFinite (x * c) = True) ∧ ((lo * c <= x * c) ∧ (x * c <= hi * c)) :=
  let l: lo * c <= x * c := Float.mulMonotoneLeft lo x c flo fx fc hc a
  let r: x * c <= hi * c := Float.mulMonotoneLeft x hi c fx fhi fc hc b
  Both (Float.finiteBetween (lo * c) (x * c) (hi * c) flc fhc l r) (Both l r)

--| `x % y` is exact for finite `x` and a finite non-zero `y`: its units are
--| `x`'s size less the largest whole number of `y`'s that fits (the quotient
--| `Nat.divFuel` finds), with `x`'s sign. `Float.remExact` bounds the result's
--| size; this gives its value.
theorem Float.Theory.remUnitsExact ∀ (x y: Float)
    (fx: Float.isFinite x = True)
    (fy: Float.isFinite y = True)
    (zy: Float.isZero y = False):
    Float.Theory.units (x % y)
      = Int.signed
        (Float.Model.signBit x.bits)
        (Int.natAbs (Float.Theory.units x)
          - Nat.divFuel
            (Int.natAbs (Float.Theory.units x))
            (Int.natAbs (Float.Theory.units x))
            (Int.natAbs (Float.Theory.units y))
            * Int.natAbs (Float.Theory.units y)) :=
  let a: Nat := x.bits
  let b: Nat := y.bits
  let fa: Float.Theory.FiniteBits a := Float.Theory.finiteBits x fx
  let fb: Float.Theory.FiniteBits b := Float.Theory.finiteBits y fy
  let zb: Float.Model.isZero b = False := Float.Theory.modelNotZero y zy
  let s: Bool := Float.Model.signBit a
  let m: Nat := Int.natAbs (Float.Model.units a)
  let d: Nat := Int.natAbs (Float.Model.units b)
  let q: Nat := Nat.divFuel m m d
  let r: Nat := m - q * d
  let mm: m = Float.Theory.magUnits (Float.Model.magnitude a) := Float.Theory.natAbsUnits a
  let dd: d = Float.Theory.magUnits (Float.Model.magnitude b) := Float.Theory.natAbsUnits b
  let magPos: 0 < Float.Model.magnitude b := arithmetic [zb]
  let dpos: 0 < d := J (y w => 0 < y) (Float.Theory.magUnitsLess 0 (Float.Model.magnitude b) magPos) dd.flipped
  let low: q * d ≤ m := Nat.divFuelLe m m d
  let high: m < Succ q * d := Nat.divFuelBound m m d (Nat.nonzeroOfPos d dpos) (Nat.leRefl m)
  let lt: r < d := arithmetic [low, high, Float.Theory.succMul q d]
  let qd: q * d = q * Float.Theory.magUnits (Float.Model.magnitude b) := Eq.cong (t => q * t) dd
  let ex: (Float.Theory.FiniteBits (Float.Model.roundRatio (Int.signed s r) 1 (-1074) s))
    ∧ (Float.Model.units (Float.Model.roundRatio (Int.signed s r) 1 (-1074) s) = Int.signed s r) :=
    Float.Theory.combinationExact
      (Float.Model.magnitude a)
      (Float.Model.magnitude b)
      r
      1
      q
      s
      s
      fa
      (arithmetic [low, mm, qd])
      (arithmetic [low, mm])
      (arithmetic [lt, dd])
  let rb: Float.Model.remBits a b = Float.Model.roundRatio (Int.signed s r) 1 (-1074) s :=
    Float.Theory.remFiniteBits a b fa fb zb
  calc Float.Theory.units (x % y)
    _ = Float.Model.units (Float.Model.remBits a b) := Eq.cong Float.Model.units (Float.Theory.remOfBits x y fx fy zy)
    _ = Float.Model.units (Float.Model.roundRatio (Int.signed s r) 1 (-1074) s) := Eq.cong Float.Model.units rb
    _ = Int.signed s r := ex.right

--| The sum of two finite doubles that are whole numbers, `f` and `k` whole
--| units of 2^-1074 each, is finite and exactly the sum, when that sum is at
--| most 2^53 in size (`Float.Theory.addWhole` with the sum's finiteness).
theorem Float.Theory.addWholeExact ∀ (y c: Float) (f k: Int)
    (fy: Float.isFinite y = True)
    (fc: Float.isFinite c = True)
    (uy: Float.Theory.units y = Int.mul f (OfNat (Float.Model.pow2 1074)))
    (uc: Float.Theory.units c = Int.mul k (OfNat (Float.Model.pow2 1074)))
    (h: Int.natAbs (Int.add f k) ≤ 9007199254740992):
    (Float.isFinite (y + c) = True)
      ∧ (Float.Theory.units (y + c) = Int.mul (Int.add f k) (OfNat (Float.Model.pow2 1074))) :=
  let z: Bool := Float.Model.signBit y.bits ∧ Float.Model.signBit c.bits
  let rb: (y + c).bits = Float.Model.roundScaled (Int.add f k) 0 z := calc (y + c).bits
    _ = Float.Model.roundRatio (Int.add (Float.Theory.units y) (Float.Theory.units c)) 1 (-1074) z :=
      Float.Theory.addBitsOf y c fy fc
    _ = Float.Model.roundRatio (Int.mul (Int.add f k) (OfNat (Float.Model.pow2 1074))) 1 (-1074) z :=
      Eq.cong
        (u => Float.Model.roundRatio u 1 (-1074) z)
        (Eq.trans (Eq.cong2 Int.add uy uc) (Float.Theory.addMulRight f k (Float.Model.pow2 1074)))
    _ = Float.Model.roundScaled (Int.add f k) 0 z := (Float.Theory.roundWhole (Int.add f k) z).flipped
  let rs := Float.Theory.roundScaledWhole (Int.add f k) z h
  Both
    (Float.Theory.isFiniteOf (y + c) (J (b w => Float.Theory.FiniteBits b) rs.left rb.flipped))
    (J (b w => Float.Model.units b = Int.mul (Int.add f k) (OfNat (Float.Model.pow2 1074))) rs.right rb.flipped)

--| The integers' side of `Float.Theory.sumNear`: `g` and `n` are at most `m`
--| in size, with `m ≤ 7e15 w` and `w ≥ 2`. A rounded sum `s` that meets
--| `Float.addRelError`'s bound (`2^53 ||s| − |g + n|| ≤ |g + n| + 2^52`) and
--| has the exact sum's sign is within `2 w` of it.
theorem Float.Theory.roundedSumNear ∀ (g n s: Int) (w m: Nat)
    (w2: 2 ≤ w)
    (mw: m ≤ w * 7000000000000000)
    (gLo: Int.leq (Int.neg (OfNat m)) g = True)
    (gHi: Int.leq g (OfNat m) = True)
    (nLo: Int.leq (Int.neg (OfNat m)) n = True)
    (nHi: Int.leq n (OfNat m) = True)
    (err: Nat.absDiff (Int.natAbs s * 1) (Int.natAbs (Int.add g n)) * 9007199254740992
      ≤ Int.natAbs (Int.add g n) + 1 * 4503599627370496)
    (sign: ((Int.leq (OfNat 0) (Int.add g n) = True) ∧ (Int.leq (OfNat 0) s = True))
      ∨ ((Int.less (Int.add g n) (OfNat 0) = True) ∧ (Int.leq s (OfNat 0) = True))):
    (Int.leq (Int.add g n) (Int.add s (OfNat (w * 2))) = True)
      ∧ (Int.leq s (Int.add (Int.add g n) (OfNat (w * 2))) = True) :=
  match sign with
    | Inl b | Inr b =>
      let b1 := b.left
      let b2 := b.right
      Both (arithmetic [w2, mw, gLo, gHi, nLo, nHi, err, b1, b2]) (arithmetic [w2, mw, gLo, gHi, nLo, nHi, err, b1, b2])

--| The sum of two units of size at most `m ≤ 7e15 w`, `w ≥ 1`, is below `t`
--| when `w · 10^18 ≤ t`.
theorem Float.Theory.sumSmallNear ∀ (g n: Int) (w m t: Nat)
    (w2: 2 ≤ w)
    (mw: m ≤ w * 7000000000000000)
    (gLo: Int.leq (Int.neg (OfNat m)) g = True)
    (gHi: Int.leq g (OfNat m) = True)
    (nLo: Int.leq (Int.neg (OfNat m)) n = True)
    (nHi: Int.leq n (OfNat m) = True)
    (top: w * 1000000000000000000 ≤ t):
    Int.natAbs (Int.add g n) < t :=
  arithmetic [w2, mw, gLo, gHi, nLo, nHi, top]

--| The sum of two doubles in `[lo, hi]` is finite and within `2 w` units
--| (2^-1074 each) of the exact sum, both ways: the standard model for `+`
--| (`Float.addRelError`) with the sign of the rounded sum following the exact
--| one's. The bounds are given as doubles and by their units: `m`, at most
--| `7e15 w`, bounds the units of `lo` and `hi` in size, and `w · 10^18` is
--| below 2^2097 (the size `addRelError` needs). With `w = 2^1030`,
--| `lo = -361.0` and `hi = 361.0` (units `2^1030 · 6350779162034176`), the
--| error is 2^-43 (`w · 2` units): the sum of two angles. The sums `lo + lo`
--| and `hi + hi` must be finite.
theorem Float.Theory.sumNear ∀ (g d lo hi: Float) (w m: Nat)
    (flo: Float.isFinite lo = True)
    (fhi: Float.isFinite hi = True)
    (fll: Float.isFinite (lo + lo) = True)
    (fhh: Float.isFinite (hi + hi) = True)
    (gLo: lo <= g)
    (gHi: g <= hi)
    (dLo: lo <= d)
    (dHi: d <= hi)
    (w2: 2 ≤ w)
    (mw: m ≤ w * 7000000000000000)
    (uLo: Int.leq (Int.neg (OfNat m)) (Float.Theory.units lo) = True)
    (uHi: Int.leq (Float.Theory.units hi) (OfNat m) = True)
    (top: w * 1000000000000000000 ≤ 1 * Nat.pow 2 2097):
    (Float.isFinite (g + d) = True)
      ∧ ((Int.leq
        (Int.add (Float.Theory.units g) (Float.Theory.units d))
        (Int.add (Float.Theory.units (g + d)) (OfNat (w * 2)))
        = True)
        ∧ (Int.leq
          (Float.Theory.units (g + d))
          (Int.add (Int.add (Float.Theory.units g) (Float.Theory.units d)) (OfNat (w * 2)))
          = True)) :=
  let fg: Float.isFinite g = True := Float.finiteBetween lo g hi flo fhi gLo gHi
  let fd: Float.isFinite d = True := Float.finiteBetween lo d hi flo fhi dLo dHi
  let fs: Float.isFinite (g + d) = True :=
    Float.finiteBetween
      (lo + lo)
      (g + d)
      (hi + hi)
      fll
      fhh
      (Float.Theory.leTrans
        (lo + lo)
        (lo + d)
        (g + d)
        (Float.addMonotone lo d lo flo fd flo dLo)
        (Float.addMonotoneLeft lo g d flo fg fd gLo))
      (Float.Theory.leTrans
        (g + d)
        (hi + d)
        (hi + hi)
        (Float.addMonotoneLeft g hi d fg fhi fd gHi)
        (Float.addMonotone d hi hi fd fhi fhi dHi))
  let gl := Float.Theory.leqTrans _ _ _ uLo (Float.Theory.unitsMonoKey lo.bits g.bits gLo)
  let gh := Float.Theory.leqTrans _ _ _ (Float.Theory.unitsMonoKey g.bits hi.bits gHi) uHi
  let dl := Float.Theory.leqTrans _ _ _ uLo (Float.Theory.unitsMonoKey lo.bits d.bits dLo)
  let dh := Float.Theory.leqTrans _ _ _ (Float.Theory.unitsMonoKey d.bits hi.bits dHi) uHi
  let sum: Int := Int.add (Float.Theory.units g) (Float.Theory.units d)
  let s: Int := Float.Theory.units (g + d)
  let err :=
    Float.addRelError g d fg fd fs
      (Float.Theory.sumSmallNear (Float.Theory.units g) (Float.Theory.units d) w m _ w2 mw gl gh dl dh top)
  let sign: ((Int.leq (OfNat 0) sum = True) ∧ (Int.leq (OfNat 0) s = True))
    ∨ ((Int.less sum (OfNat 0) = True) ∧ (Int.leq s (OfNat 0) = True)) :=
    Float.Theory.orCase
      [goal := ((Int.leq (OfNat 0) sum = True) ∧ (Int.leq (OfNat 0) s = True))
        ∨ ((Int.less sum (OfNat 0) = True) ∧ (Int.leq s (OfNat 0) = True))]
      (Float.Theory.boolCases (Int.leq (OfNat 0) sum))
      (nonneg =>
        let atLeast: -0.0 <= g + d :=
          Float.Theory.addAtLeast g d
            (-0.0)
            fg
            fd
            byComputing
            (J (y z => Int.leq y sum = True) nonneg (byComputing: Float.Theory.units (-0.0) = OfNat 0).flipped)
            (b => (Bool.trueNotFalse b).impossible)
        Inl
          (Both nonneg
            (J
              (y z => Int.leq y s = True)
              (Float.Theory.unitsMonoKey (-0.0).bits (g + d).bits atLeast)
              (byComputing: Float.Theory.units (-0.0) = OfNat 0))))
      (neg =>
        let below: Int.less sum (OfNat 0) = True := Float.Theory.intLessZeroOfNotNonneg sum neg
        let atMost: g + d <= 0.0 :=
          Float.Theory.addAtMost g d 0.0 fg fd byComputing
            (J
              (y z => Int.leq sum y = True)
              (Float.Theory.intLeOfLess sum (OfNat 0) below)
              (byComputing: Float.Theory.units 0.0 = OfNat 0).flipped)
            (b => byComputing)
        Inr
          (Both below
            (J
              (y z => Int.leq s y = True)
              (Float.Theory.unitsMonoKey (g + d).bits 0.0.bits atMost)
              (byComputing: Float.Theory.units 0.0 = OfNat 0))))
  Both fs (Float.Theory.roundedSumNear (Float.Theory.units g) (Float.Theory.units d) s w m w2 mw gl gh dl dh err sign)

-- Division by a larger divisor

--| A larger denominator rounds a positive ratio to a pattern no larger:
--| `n / d2` and `n / d1` over the common denominator `d1 · d2` are in order,
--| and rounding keeps their order (`roundsToMono`).
theorem Float.Theory.magnitudeAntiDen ∀ (n d1 d2: Nat) (s: Int)
    (pn: 0 < n)
    (p1: 0 < d1)
    (le: d1 ≤ d2):
    Float.Model.roundMagnitude False n d2 s ≤ Float.Model.roundMagnitude False n d1 s :=
  let u: Nat := Float.Model.scaleUp n s
  let p2: 0 < d2 := arithmetic [p1, le]
  let pa: 0 < Float.Model.scaleDown d1 s := Float.Theory.scaleDownPos d1 s p1
  let pb: 0 < Float.Model.scaleDown d2 s := Float.Theory.scaleDownPos d2 s p2
  let pab: 0 < Float.Model.scaleDown d2 s * Float.Model.scaleDown d1 s :=
    Float.Theory.mulPos (Float.Model.scaleDown d2 s) (Float.Model.scaleDown d1 s) pb pa
  let ab: Float.Model.scaleDown d1 s ≤ Float.Model.scaleDown d2 s :=
    rewrite Float.Theory.scaleDownPow d1 s, Float.Theory.scaleDownPow d2 s then
      Nat.leMulRight d1 d2 (Float.Theory.downPow s) le
  Float.Theory.roundsToMono
    (u * Float.Model.scaleDown d1 s)
    (u * Float.Model.scaleDown d2 s)
    (Float.Model.scaleDown d2 s * Float.Model.scaleDown d1 s)
    (Float.Model.roundMagnitude False n d2 s)
    (Float.Model.roundMagnitude False n d1 s)
    pab
    (Float.Theory.roundsToScale u
      (Float.Model.scaleDown d2 s)
      (u * Float.Model.scaleDown d1 s)
      (Float.Model.scaleDown d2 s * Float.Model.scaleDown d1 s)
      (Float.Model.roundMagnitude False n d2 s)
      pb
      pab
      (algebra: u * (Float.Model.scaleDown d2 s * Float.Model.scaleDown d1 s)
        = u * Float.Model.scaleDown d1 s * Float.Model.scaleDown d2 s)
      (Float.Theory.roundMagnitudeSpec n d2 s pn p2))
    (Float.Theory.roundsToScale u
      (Float.Model.scaleDown d1 s)
      (u * Float.Model.scaleDown d2 s)
      (Float.Model.scaleDown d2 s * Float.Model.scaleDown d1 s)
      (Float.Model.roundMagnitude False n d1 s)
      pa
      pab
      (algebra: u * (Float.Model.scaleDown d2 s * Float.Model.scaleDown d1 s)
        = u * Float.Model.scaleDown d2 s * Float.Model.scaleDown d1 s)
      (Float.Theory.roundMagnitudeSpec n d1 s pn p1))
    (Float.Theory.mulLeLeft (Float.Model.scaleDown d1 s) (Float.Model.scaleDown d2 s) u ab)

--| A nonnegative numerator over a larger denominator rounds no higher in
--| the total order, whatever the zero's sign.
theorem Float.Theory.roundKeyAntiDen ∀ (num: Int) (d1 d2: Nat) (scale: Int) (z: Bool)
    (p1: 0 < d1)
    (le: d1 ≤ d2)
    (nonneg: Int.leq (OfNat 0) num = True):
    Int.leq (Float.Theory.roundKey num d2 scale z) (Float.Theory.roundKey num d1 scale z) = True :=
  match num with
    | OfNat Zero =>
      match z with
        | True | False => byComputing
    | OfNat (Succ k) =>
      Float.Theory.leqVia
        (Float.Theory.roundKey (OfNat (Succ k)) d2 scale z)
        (Float.Theory.roundKey (OfNat (Succ k)) d1 scale z)
        (OfNat (Float.Model.roundMagnitude False (Succ k) d2 (Int.add scale (OfNat 1074))))
        (OfNat (Float.Model.roundMagnitude False (Succ k) d1 (Int.add scale (OfNat 1074))))
        (Float.Theory.roundKeyPos k d2 scale z (arithmetic [p1, le]))
        (Float.Theory.roundKeyPos k d1 scale z p1)
        (arithmetic [Float.Theory.magnitudeAntiDen (Succ k) d1 d2 (Int.add scale (OfNat 1074)) byComputing p1 le])

--| Division is antitone in a positive divisor: for `0 < d <= e`, both
--| finite, and a finite `x` with `0.0 <= x`, `x / e <= x / d`. The exact
--| quotients are in order, and rounding keeps it (`magnitudeAntiDen`).
--| `0.0 <= x` leaves out `-0.0`, whose quotients are `-0.0` either way, and
--| negative `x`, for which the order flips.
theorem Float.divAntitone ∀ (x d e: Float)
    (pos: 0.0 < d)
    (fd: Float.isFinite d = True)
    (fe: Float.isFinite e = True)
    (de: d <= e)
    (fx: Float.isFinite x = True)
    (nonneg: 0.0 <= x):
    x / e <= x / d :=
  let ud: Int := Float.Model.units d.bits
  let ue: Int := Float.Model.units e.bits
  let dpos: Int.less (OfNat 0) ud = True := Float.Theory.unitsPositive d pos
  let dle: Int.leq ud ue = True := Float.Theory.unitsMonoKey d.bits e.bits de
  let epos: 0.0 < e := Float.Theory.ltLeTrans (Float.orderKey 0.0) (Float.orderKey d) (Float.orderKey e) pos de
  let xnn: Int.leq (OfNat 0) (Float.Model.units x.bits) = True :=
    J
      (v w => Int.leq v (Float.Model.units x.bits) = True)
      (Float.Theory.unitsMonoKey 0.0.bits x.bits nonneg)
      (byComputing: Float.Theory.units 0.0 = OfNat 0)
  Float.Theory.leqVia
    (Float.orderKey (x / e))
    (Float.orderKey (x / d))
    (Float.Theory.roundKey (Float.Model.units x.bits) (Int.natAbs ue) (OfNat 0) (Float.Model.signBit x.bits))
    (Float.Theory.roundKey (Float.Model.units x.bits) (Int.natAbs ud) (OfNat 0) (Float.Model.signBit x.bits))
    (Float.Theory.quotientKeyFinite x e epos fe fx)
    (Float.Theory.quotientKeyFinite x d pos fd fx)
    (Float.Theory.roundKeyAntiDen
      (Float.Model.units x.bits)
      (Int.natAbs ud)
      (Int.natAbs ue)
      (OfNat 0)
      (Float.Model.signBit x.bits)
      (Float.Theory.natAbsPos ud dpos)
      (arithmetic [dpos, dle])
      xnn)

test "Float.divAntitone" :=
  1.0 / 3.0 <= 1.0 / 2.0 ∧ 0.0 / 5.0 <= 0.0 / 5e-324 ∧ 1e300 / 1e-10 <= 1e300 / 1e-20 ∧ 5e-324 / 3.0 <= 5e-324 / 2.0

--| A finite double over a positive finite one isn't the NaN: its key is
--| at most +infinity's (`roundKeyLeInf`), below the NaN's. It can overflow
--| to an infinity, as `1e300 / 1e-300` does.
theorem Float.divNotNaN ∀ (x d: Float)
    (pos: 0.0 < d)
    (fd: Float.isFinite d = True)
    (fx: Float.isFinite x = True):
    Float.isNaN (x / d) = False :=
  let pd: 0 < Int.natAbs (Float.Model.units d.bits) :=
    Float.Theory.natAbsPos (Float.Model.units d.bits) (Float.Theory.unitsPositive d pos)
  let low: Int.leq (Float.orderKey (x / d)) (OfNat 9218868437227405312) = True :=
    J
      (k w => Int.leq k (OfNat 9218868437227405312) = True)
      (Float.Theory.roundKeyLeInf
        (Int.natAbs (Float.Model.units d.bits))
        (OfNat 0)
        (Float.Model.signBit x.bits)
        pd
        (Float.Model.units x.bits))
      (Float.Theory.quotientKeyFinite x d pos fd fx).flipped
  match c: Float.isNaN (x / d) with
    | False => byComputing
    | True =>
      let b: (x / d).bits = 9221120237041090560 := Nat.equalSound (x / d).bits 9221120237041090560 c
      let k: Float.orderKey (x / d) = OfNat 9221120237041090560 := rewrite b
      Void.impossible (arithmetic [low, k])

test "Float.divNotNaN" := ¬Float.isNaN (1e300 / 1e-300) ∧ ¬Float.isNaN (0.0 / 5e-324) ∧ ¬Float.isNaN (-1.0 / 3.0)

-- Floor and ceiling within one

--| The floor of a double below 2^53 in size is finite: a whole number of
--| that size (`roundScaledWhole`).
theorem Float.floorIsFinite ∀ (x: Float)
    (small: Float.abs x < 9007199254740992.0):
    Float.isFinite (Float.floor x) = True :=
  let a: Nat := x.bits
  let s: Bool := Float.Model.signBit a
  let p: Nat := Float.Model.pow2 1074
  let n: Nat := Int.natAbs (Float.Model.units a)
  let f: Int := Float.Model.floorDiv s n p
  let fin: Float.Theory.FiniteBits a ∧ (n < p * 9007199254740992) := Float.Theory.absBelowUnits x small
  let fl: (Float.floor x).bits = Float.Model.roundScaled f 0 s :=
    Eq.trans (Float.Theory.floorOfBits x) (Float.Theory.floorFinite a (Float.Theory.notSpecialOf a fin.left))
  Float.Theory.isFiniteOf
    (Float.floor x)
    (J
      (r w => Float.Theory.FiniteBits r)
      (Float.Theory.roundScaledWhole f s (Float.Theory.floorDivBelow s n p 9007199254740992 byComputing fin.right)).left
      fl.flipped)

--| The ceiling of a double below 2^53 in size is finite, as `Float.floorIsFinite`.
theorem Float.ceilIsFinite ∀ (x: Float)
    (small: Float.abs x < 9007199254740992.0):
    Float.isFinite (Float.ceil x) = True :=
  let a: Nat := x.bits
  let s: Bool := Float.Model.signBit a
  let p: Nat := Float.Model.pow2 1074
  let n: Nat := Int.natAbs (Float.Model.units a)
  let g: Int := Float.Model.floorDiv (¬s) n p
  let fin: Float.Theory.FiniteBits a ∧ (n < p * 9007199254740992) := Float.Theory.absBelowUnits x small
  let cl: (Float.ceil x).bits = Float.Model.roundScaled (Int.neg g) 0 s :=
    Eq.trans (Float.Theory.ceilOfBits x) (Float.Theory.ceilFinite a (Float.Theory.notSpecialOf a fin.left))
  Float.Theory.isFiniteOf
    (Float.ceil x)
    (J
      (r w => Float.Theory.FiniteBits r)
      (Float.Theory.roundScaledWhole
        (Int.neg g)
        s
        (Float.Theory.natAbsNegLe g (Float.Theory.floorDivBelow (¬s) n p 9007199254740992 byComputing fin.right))).left
      cl.flipped)

test "Float.floorIsFinite" :=
  Float.isFinite (Float.floor -2.5)
    ∧ Float.isFinite (Float.ceil 9007199254740991.0)
    ∧ Float.isFinite (Float.floor 5e-324)

theorem Float.Theory.belowNextWhole ∀ (u v f: Int) (p: Nat)
    (h: Int.less u (Int.mul (Int.add f (OfNat 1)) (OfNat p)) = True)
    (ev: v = Int.mul f (OfNat p)):
    Int.less u (Int.add v (OfNat p)) = True :=
  let d: Int.mul (Int.add f (OfNat 1)) (OfNat p) = Int.add (Int.mul f (OfNat p)) (OfNat p) := algebra
  arithmetic [h, ev, d]

theorem Float.Theory.aboveNextWhole ∀ (u w v g: Int) (p: Nat)
    (h: Int.less w (Int.mul (Int.add g (OfNat 1)) (OfNat p)) = True)
    (eu: u = Int.neg w)
    (ev: v = Int.mul (Int.neg g) (OfNat p)):
    Int.less v (Int.add u (OfNat p)) = True :=
  let d: Int.mul (Int.add g (OfNat 1)) (OfNat p) = Int.add (Int.mul g (OfNat p)) (OfNat p) := algebra
  let n: Int.mul (Int.neg g) (OfNat p) = Int.neg (Int.mul g (OfNat p)) := algebra
  arithmetic [h, eu, ev, d, n]

--| A double below 2^53 in size is less than one above its floor, exactly:
--| in units of 2^-1074, `x < floor x + 1`, with no rounding in the sum
--| (`Float.ltFloorAddOne` says it of the double sum).
theorem Float.Theory.floorUnitsAbove ∀ (x: Float)
    (small: Float.abs x < 9007199254740992.0):
    Int.less (Float.Theory.units x) (Int.add (Float.Theory.units (Float.floor x)) (OfNat (Float.Model.pow2 1074)))
      = True :=
  let a: Nat := x.bits
  let s: Bool := Float.Model.signBit a
  let p: Nat := Float.Model.pow2 1074
  let n: Nat := Int.natAbs (Float.Model.units a)
  let f: Int := Float.Model.floorDiv s n p
  let fin: Float.Theory.FiniteBits a ∧ (n < p * 9007199254740992) := Float.Theory.absBelowUnits x small
  let range: ((Int.natAbs f ≤ 9007199254740992) ∧ (Int.natAbs (Int.add f (OfNat 1)) ≤ 9007199254740992))
    ∧ (Int.less (Int.signed s n) (Int.mul (Int.add f (OfNat 1)) (OfNat p)) = True) :=
    Float.Theory.floorDivRange s n p byComputing fin.right
  let fl: (Float.floor x).bits = Float.Model.roundScaled f 0 s :=
    Eq.trans (Float.Theory.floorOfBits x) (Float.Theory.floorFinite a (Float.Theory.notSpecialOf a fin.left))
  let uf: Float.Model.units (Float.floor x).bits = Int.mul f (OfNat p) :=
    J
      (r w => Float.Model.units r = Int.mul f (OfNat p))
      (Float.Theory.roundScaledWhole f s range.left.left).right
      fl.flipped
  J
    (y w => Int.less y (Int.add (Float.Theory.units (Float.floor x)) (OfNat p)) = True)
    (Float.Theory.belowNextWhole (Int.signed s n) (Float.Theory.units (Float.floor x)) f p range.right uf)
    (Float.Theory.unitsSigned a)

--| A double below 2^53 in size is more than one below its ceiling, exactly:
--| in units of 2^-1074, `ceil x < x + 1` (as doubles, `x + 1.0` can round
--| down to the ceiling; `Float.ceilSubOneLt`).
theorem Float.Theory.ceilUnitsBelow ∀ (x: Float)
    (small: Float.abs x < 9007199254740992.0):
    Int.less (Float.Theory.units (Float.ceil x)) (Int.add (Float.Theory.units x) (OfNat (Float.Model.pow2 1074)))
      = True :=
  let a: Nat := x.bits
  let s: Bool := Float.Model.signBit a
  let p: Nat := Float.Model.pow2 1074
  let n: Nat := Int.natAbs (Float.Model.units a)
  let g: Int := Float.Model.floorDiv (¬s) n p
  let fin: Float.Theory.FiniteBits a ∧ (n < p * 9007199254740992) := Float.Theory.absBelowUnits x small
  let range: ((Int.natAbs g ≤ 9007199254740992) ∧ (Int.natAbs (Int.add g (OfNat 1)) ≤ 9007199254740992))
    ∧ (Int.less (Int.signed (¬s) n) (Int.mul (Int.add g (OfNat 1)) (OfNat p)) = True) :=
    Float.Theory.floorDivRange (¬s) n p byComputing fin.right
  let cl: (Float.ceil x).bits = Float.Model.roundScaled (Int.neg g) 0 s :=
    Eq.trans (Float.Theory.ceilOfBits x) (Float.Theory.ceilFinite a (Float.Theory.notSpecialOf a fin.left))
  let uc: Float.Model.units (Float.ceil x).bits = Int.mul (Int.neg g) (OfNat p) :=
    J
      (r w => Float.Model.units r = Int.mul (Int.neg g) (OfNat p))
      (Float.Theory.roundScaledWhole (Int.neg g) s (Float.Theory.natAbsNegLe g range.left.left)).right
      cl.flipped
  Float.Theory.aboveNextWhole
    (Float.Theory.units x)
    (Int.signed (¬s) n)
    (Float.Theory.units (Float.ceil x))
    g
    p
    range.right
    (Eq.trans (Float.Theory.unitsSigned a).flipped (Float.Theory.signedFlip s n))
    uc

-- From units back to the order

--| Units in order give the total order when the larger is positive:
--| `units x ≤ units y` and `0 < units y` give `x <= y`. A negative or zero
--| `x` is below every positive double (`-0.0` and `0.0` included), and on
--| positive patterns the units are monotone both ways
--| (`magUnitsLeReflect`). Units alone can't order `-0.0` and `0.0`, hence
--| the condition; `Float.Theory.leOfUnitsNeg` is the other side.
theorem Float.Theory.leOfUnitsPos ∀ (x y: Float)
    (pos: Int.less (OfNat 0) (Float.Theory.units y) = True)
    (h: Int.leq (Float.Theory.units x) (Float.Theory.units y) = True):
    x <= y :=
  let uy := Float.Theory.unitsMag y.bits
  match sy: Nat.leq 9223372036854775808 y.bits with
    | True => Void.impossible (arithmetic [pos, uy])
    | False =>
      match sx: Nat.leq 9223372036854775808 x.bits with
        | True => byComputing
        | False =>
          let le: Float.Theory.magUnits x.bits ≤ Float.Theory.magUnits y.bits := arithmetic [h]
          arithmetic [Float.Theory.magUnitsLeReflect x.bits y.bits le]

--| Units in order give the total order when the smaller is negative:
--| `units x ≤ units y` and `units x < 0` give `x <= y`, as
--| `Float.Theory.leOfUnitsPos`.
theorem Float.Theory.leOfUnitsNeg ∀ (x y: Float)
    (neg: Int.less (Float.Theory.units x) (OfNat 0) = True)
    (h: Int.leq (Float.Theory.units x) (Float.Theory.units y) = True):
    x <= y :=
  let ux := Float.Theory.unitsMag x.bits
  match sx: Nat.leq 9223372036854775808 x.bits with
    | True =>
      match sy: Nat.leq 9223372036854775808 y.bits with
        | False => byComputing
        | True =>
          let le: Float.Theory.magUnits (y.bits - 9223372036854775808)
            ≤ Float.Theory.magUnits (x.bits - 9223372036854775808) :=
            arithmetic [h]
          arithmetic [Float.Theory.magUnitsLeReflect (y.bits - 9223372036854775808) (x.bits - 9223372036854775808) le]

test "Float.Theory.leOfUnitsPos" := -0.0 <= 5e-324 ∧ 0.0 <= 5e-324 ∧ -1.0 <= -0.0 ∧ -1.0 <= 0.0

-- The ceiling past a half

--| The product of two naturals as integers.
theorem Float.Theory.intMulOfNat ∀ (a b: Nat): Int.mul (OfNat a) (OfNat b) = OfNat (a * b) := algebra

--| A negative integer times a natural.
theorem Float.Theory.intMulNegSucc ∀ (j m: Nat): Int.mul (NegSucc j) (OfNat m) = Int.neg (OfNat ((j + 1) * m)) :=
  algebra

theorem Float.Theory.doubleMul ∀ (j h: Nat): j * (h * 2) = (2 * j) * h := algebra

--| A whole number `c` of units `h * 2` at least `(k + 1/2)` of them is at least `k + 1`.
theorem Float.Theory.halfStep ∀ (c u: Int) (h k p: Nat)
    (hp: 0 < h)
    (ep: p = h * 2)
    (hu: Int.leq (OfNat ((2 * k + 1) * h)) u = True)
    (hc: Int.leq u (Int.mul c (OfNat p)) = True):
    Int.leq (OfNat (k + 1)) c = True :=
  let hc2: Int.leq u (Int.mul c (OfNat (h * 2))) = True := J (q z => Int.leq u (Int.mul c (OfNat q)) = True) hc ep
  match c with
    | OfNat j =>
      let e: Int.mul (OfNat j) (OfNat (h * 2)) = OfNat (j * (h * 2)) := Float.Theory.intMulOfNat j (h * 2)
      let a: (2 * k + 1) * h ≤ (2 * j) * h := arithmetic [hu, hc2, e, Float.Theory.doubleMul j h]
      arithmetic [Float.Theory.cancelLe (2 * k + 1) (2 * j) h hp a]
    | NegSucc j =>
      let big: 1 * (h * 2) ≤ (j + 1) * (h * 2) := Nat.leMulRight 1 (j + 1) (h * 2) (arithmetic)
      Void.impossible (arithmetic [hu, hc2, Float.Theory.intMulNegSucc j (h * 2), hp, big])

--| `k ≤ c` scaled by `p`, for a natural `k`.
theorem Float.Theory.mulLeOf ∀ (c: Int) (k p: Nat)
    (h: Int.leq (OfNat k) c = True):
    Int.leq (OfNat (k * p)) (Int.mul c (OfNat p)) = True :=
  match c with | OfNat j => arithmetic [Nat.leMulRight k j p (arithmetic [h]), Float.Theory.intMulOfNat j p]

--| The ceiling of a double `y` below 2^53 in size that is at least
--| `k + 1/2` is at least `k + 1`, in units of 2^-1074: `ceil` gives a
--| whole number of units of 2^1074 at least `y`'s (`ceilDivGe`), and the
--| next whole number above `k` is `k + 1`. Stated with the half so that a
--| bound on `y` from the standard model, which is never exact, still
--| decides the ceiling.
theorem Float.Theory.ceilAtLeast ∀ (y: Float) (k: Nat)
    (small: Float.abs y < 9007199254740992.0)
    (hu: Int.leq (OfNat ((2 * k + 1) * Float.Model.pow2 1073)) (Float.Theory.units y) = True):
    Int.leq (OfNat ((k + 1) * Float.Model.pow2 1074)) (Float.Theory.units (Float.ceil y)) = True :=
  let a: Nat := y.bits
  let s: Bool := Float.Model.signBit a
  let p: Nat := Float.Model.pow2 1074
  let n: Nat := Int.natAbs (Float.Model.units a)
  let fin: Float.Theory.FiniteBits a ∧ (n < p * 9007199254740992) := Float.Theory.absBelowUnits y small
  let g: Int := Float.Model.floorDiv (¬s) n p
  let gb: Int.natAbs g ≤ 9007199254740992 := Float.Theory.floorDivBelow (¬s) n p 9007199254740992 byComputing fin.right
  let c: Int := Int.neg g
  let cl: (Float.ceil y).bits = Float.Model.roundScaled c 0 s :=
    Eq.trans (Float.Theory.ceilOfBits y) (Float.Theory.ceilFinite a (Float.Theory.notSpecialOf a fin.left))
  let uc: Float.Model.units (Float.ceil y).bits = Int.mul c (OfNat p) :=
    J
      (r w => Float.Model.units r = Int.mul c (OfNat p))
      (Float.Theory.roundScaledWhole c s (Float.Theory.natAbsNegLe g gb)).right
      cl.flipped
  let ge: Int.leq (Float.Theory.units y) (Int.mul c (OfNat p)) = True :=
    J
      (v z => Int.leq v (Int.mul c (OfNat p)) = True)
      (Float.Theory.ceilDivGe s n p byComputing)
      (Float.Theory.unitsSigned a)
  let ck := Float.Theory.halfStep c (Float.Theory.units y) (Float.Model.pow2 1073) k p byComputing byComputing hu ge
  J (v z => Int.leq (OfNat ((k + 1) * p)) v = True) (Float.Theory.mulLeOf c (k + 1) p ck) uc.flipped

-- The remainder as whole steps

--| A signed product, the sign moved out.
theorem Float.Theory.signedScaled ∀ (s: Bool) (r p: Nat): Int.signed s (r * p) = Int.mul (Int.signed s r) (OfNat p) :=
  match s with | False | True => algebra

theorem Float.Theory.remStepArith ∀ (s: Bool) (m q d r: Nat) (ux ur qd: Int)
    (eu: ux = Int.signed s m)
    (er: ur = Int.signed s r)
    (eq: qd = Int.mul (Int.signed s q) (OfNat d))
    (eqd: Int.mul (Int.signed s q) (OfNat d) = Int.signed s (q * d))
    (low: q * d ≤ m)
    (rr: r = m - q * d)
    (high: m < Succ q * d):
    (Int.add ur qd = ux) ∧ ((Int.natAbs ur < d) ∧ (Int.leq (OfNat 0) ux = True → Int.leq (OfNat 0) ur = True)) :=
  let lt: m < q * d + d := arithmetic [high, Float.Theory.succMul q d]
  match s with
    | False => Both (arithmetic [eu, er, eq, eqd, low, rr]) (Both (arithmetic [er, rr, lt, low]) (n => arithmetic [er]))
    | True =>
      Both
        (arithmetic [eu, er, eq, eqd, low, rr])
        (Both (arithmetic [er, rr, lt, low]) (n => arithmetic [n, eu, er, rr, low]))

--| `x % y`, for finite `x` and a positive finite `y`, is `x` less a whole
--| number `t` of `y`s, exactly, smaller than `y` in size, and not negative
--| when `x` isn't: `remUnitsExact` with truncated division's quotient. The
--| facts are handed to `k` with `t`, since `t` has no closed form worth
--| stating.
theorem Float.Theory.remStep ∀ (x y: Float)
    (fx: Float.isFinite x = True)
    (fy: Float.isFinite y = True)
    (pos: 0.0 < y)
    [goal: Prop]
    (k: ∀ (t: Int) => Int.add (Float.Theory.units (x % y)) (Int.mul t (Float.Theory.units y)) = Float.Theory.units x
      → Int.natAbs (Float.Theory.units (x % y)) < Int.natAbs (Float.Theory.units y)
      → (Int.leq (OfNat 0) (Float.Theory.units x) = True → Int.leq (OfNat 0) (Float.Theory.units (x % y)) = True)
      → goal):
    goal :=
  let s: Bool := Float.Model.signBit x.bits
  let m: Nat := Int.natAbs (Float.Theory.units x)
  let d: Nat := Int.natAbs (Float.Theory.units y)
  let q: Nat := Nat.divFuel m m d
  let up: Int.less (OfNat 0) (Float.Theory.units y) = True := Float.Theory.unitsPositive y pos
  let dpos: 0 < d := Float.Theory.natAbsPos (Float.Theory.units y) up
  let low: q * d ≤ m := Nat.divFuelLe m m d
  let high: m < Succ q * d := Nat.divFuelBound m m d (Nat.nonzeroOfPos d dpos) (Nat.leRefl m)
  let du: Float.Theory.units y = OfNat d := arithmetic [up]
  let sb: Nat.leq 9223372036854775808 y.bits = False := Float.Theory.positiveSignClear y pos
  let mz: Float.Model.isZero y.bits = False := Float.Theory.positiveNotZero y pos
  let mb: Float.Model.magnitude y.bits = y.bits := rewrite sb
  let zy: Float.isZero y = False := Both (arithmetic [mz, mb]) (arithmetic [sb])
  let sa :=
    Float.Theory.remStepArith s m q d
      (m - q * d)
      (Float.Theory.units x)
      (Float.Theory.units (x % y))
      (Int.mul (Int.signed s q) (Float.Theory.units y))
      (Float.Theory.unitsSigned x.bits).flipped
      (Float.Theory.remUnitsExact x y fx fy zy)
      (Eq.cong (u => Int.mul (Int.signed s q) u) du)
      (Float.Theory.signedScaled s q d).flipped
      low
      byComputing
      high
  k
    (Int.signed s q)
    sa.left
    (J (v z => Int.natAbs (Float.Theory.units (x % y)) < v) sa.right.left (Eq.cong Int.natAbs du).flipped)
    sa.right.right
