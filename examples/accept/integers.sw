-- Integers are `Int.OfNat n` (n) and `Int.NegSucc n` (-(n+1)). This file spells
-- values with constructors; literals are shown in int-literals.sw.
-- Everything here holds by computation.

-- The dial example: -18 % 100 is 82, not -18.
theorem dial: Int.mod (Int.NegSucc 17) (Int.OfNat 100) = Int.OfNat 82 := rfl

theorem dialNat: Int.modNat (Int.NegSucc 17) 100 = 82 := rfl

-- Leijen's table, one row per (a, d). T truncates (`Int.tdiv`, `Int.tmod`),
-- F floors (`Int.fdiv`, `Int.fmod`), E is Euclidean (`Int.div`, `Int.mod`).

-- 8, 3
theorem t83q: Int.tdiv (Int.OfNat 8) (Int.OfNat 3) = Int.OfNat 2 := rfl

theorem t83r: Int.tmod (Int.OfNat 8) (Int.OfNat 3) = Int.OfNat 2 := rfl

theorem f83q: Int.fdiv (Int.OfNat 8) (Int.OfNat 3) = Int.OfNat 2 := rfl

theorem f83r: Int.fmod (Int.OfNat 8) (Int.OfNat 3) = Int.OfNat 2 := rfl

theorem e83q: Int.div (Int.OfNat 8) (Int.OfNat 3) = Int.OfNat 2 := rfl

theorem e83r: Int.mod (Int.OfNat 8) (Int.OfNat 3) = Int.OfNat 2 := rfl

-- 8, -3
theorem t8n3q: Int.tdiv (Int.OfNat 8) (Int.NegSucc 2) = Int.NegSucc 1 := rfl

theorem t8n3r: Int.tmod (Int.OfNat 8) (Int.NegSucc 2) = Int.OfNat 2 := rfl

theorem f8n3q: Int.fdiv (Int.OfNat 8) (Int.NegSucc 2) = Int.NegSucc 2 := rfl

theorem f8n3r: Int.fmod (Int.OfNat 8) (Int.NegSucc 2) = Int.NegSucc 0 := rfl

theorem e8n3q: Int.div (Int.OfNat 8) (Int.NegSucc 2) = Int.NegSucc 1 := rfl

theorem e8n3r: Int.mod (Int.OfNat 8) (Int.NegSucc 2) = Int.OfNat 2 := rfl

-- -8, 3
theorem tn83q: Int.tdiv (Int.NegSucc 7) (Int.OfNat 3) = Int.NegSucc 1 := rfl

theorem tn83r: Int.tmod (Int.NegSucc 7) (Int.OfNat 3) = Int.NegSucc 1 := rfl

theorem fn83q: Int.fdiv (Int.NegSucc 7) (Int.OfNat 3) = Int.NegSucc 2 := rfl

theorem fn83r: Int.fmod (Int.NegSucc 7) (Int.OfNat 3) = Int.OfNat 1 := rfl

theorem en83q: Int.div (Int.NegSucc 7) (Int.OfNat 3) = Int.NegSucc 2 := rfl

theorem en83r: Int.mod (Int.NegSucc 7) (Int.OfNat 3) = Int.OfNat 1 := rfl

-- -8, -3
theorem tn8n3q: Int.tdiv (Int.NegSucc 7) (Int.NegSucc 2) = Int.OfNat 2 := rfl

theorem tn8n3r: Int.tmod (Int.NegSucc 7) (Int.NegSucc 2) = Int.NegSucc 1 := rfl

theorem fn8n3q: Int.fdiv (Int.NegSucc 7) (Int.NegSucc 2) = Int.OfNat 2 := rfl

theorem fn8n3r: Int.fmod (Int.NegSucc 7) (Int.NegSucc 2) = Int.NegSucc 1 := rfl

theorem en8n3q: Int.div (Int.NegSucc 7) (Int.NegSucc 2) = Int.OfNat 3 := rfl

theorem en8n3r: Int.mod (Int.NegSucc 7) (Int.NegSucc 2) = Int.OfNat 1 := rfl

-- -1, 2
theorem tn12q: Int.tdiv (Int.NegSucc 0) (Int.OfNat 2) = Int.OfNat 0 := rfl

theorem tn12r: Int.tmod (Int.NegSucc 0) (Int.OfNat 2) = Int.NegSucc 0 := rfl

theorem fn12q: Int.fdiv (Int.NegSucc 0) (Int.OfNat 2) = Int.NegSucc 0 := rfl

theorem fn12r: Int.fmod (Int.NegSucc 0) (Int.OfNat 2) = Int.OfNat 1 := rfl

theorem en12q: Int.div (Int.NegSucc 0) (Int.OfNat 2) = Int.NegSucc 0 := rfl

theorem en12r: Int.mod (Int.NegSucc 0) (Int.OfNat 2) = Int.OfNat 1 := rfl

-- Division needs a proof that the divisor isn't zero; with a local one,
-- the zero case is handled.
def safeDiv (a: Int) (d: Int): Int := if h: d != Int.OfNat 0 then Int.div a d else Int.OfNat 0

theorem safeDivZero: safeDiv (Int.OfNat 7) (Int.OfNat 0) = Int.OfNat 0 := rfl

theorem safeDivNeg: safeDiv (Int.NegSucc 6) (Int.OfNat 2) = Int.NegSucc 3 := rfl

-- Text.
theorem showNeg: Int.toText (Int.NegSucc 41) = "-42" := rfl

theorem showZero: Int.toText (Int.OfNat 0) = "0" := rfl

theorem readLeadingZeros: "-007".toInt = Just (Int.NegSucc 6) := rfl

theorem readMinusZero: "-0".toInt = Just (Int.OfNat 0) := rfl

theorem readPlain: "42".toInt = Just (Int.OfNat 42) := rfl

theorem readLoneMinus: "-".toInt = Nothing := rfl

theorem readEmpty: "".toInt = Nothing := rfl

theorem readPlus: "+5".toInt = Nothing := rfl

theorem readTwoMinuses: "--5".toInt = Nothing := rfl

theorem readLeadingSpace: " 5".toInt = Nothing := rfl

theorem readTrailingSpace: "5 ".toInt = Nothing := rfl

theorem readHex: "0x10".toInt = Nothing := rfl

theorem readDecimalPoint: "5.0".toInt = Nothing := rfl

theorem readFullwidth: "５".toInt = Nothing := rfl

-- Sign, absolute value, conversions.
theorem signNeg: Int.sign (Int.NegSucc 9) = Int.NegSucc 0 := rfl

theorem signZero: Int.sign (Int.OfNat 0) = Int.OfNat 0 := rfl

theorem signPos: Int.sign (Int.OfNat 9) = Int.OfNat 1 := rfl

theorem absNeg: Int.abs (Int.NegSucc 4) = Int.OfNat 5 := rfl

theorem checkedNeg: Int.toNatChecked (Int.NegSucc 4) = Nothing := rfl

theorem checkedPos: Int.toNatChecked (Int.OfNat 4) = Just 4 := rfl

-- Order: every negative is below every non-negative; `-5 < -2`.
theorem lessNegZero: Int.LessThan (Int.NegSucc 0) (Int.OfNat 0) := rfl

theorem lessNegNeg: Int.LessThan (Int.NegSucc 4) (Int.NegSucc 1) := rfl

theorem leqSame: Int.LessEq (Int.NegSucc 4) (Int.NegSucc 4) := rfl

theorem leqPosNeg: Int.leq (Int.OfNat 0) (Int.NegSucc 0) = False := rfl

theorem lessSame: Int.less (Int.OfNat 3) (Int.OfNat 3) = False := rfl

theorem compareMixed: Int.compare (Int.NegSucc 4) (Int.OfNat 0) = Less := rfl

theorem compareNegs: Int.compare (Int.NegSucc 4) (Int.NegSucc 1) = Less := rfl

theorem compareEqual: Int.compare (Int.NegSucc 4) (Int.NegSucc 4) = Equal := rfl

-- `==` is decided by `Int.decEq`.
theorem eqSame: (Int.NegSucc 3 == Int.NegSucc 3) = True := rfl

theorem eqDifferent: (Int.NegSucc 3 == Int.OfNat 3) = False := rfl
