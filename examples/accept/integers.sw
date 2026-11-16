-- Integers are `Int.OfNat n` (n) and `Int.NegSucc n` (-(n+1)). This file spells
-- values with constructors; literals are shown in int-literals.sw.
-- Everything here holds by computation.

import Std (Int)

-- The dial example: -18 % 100 is 82, not -18.
theorem dial: Int.mod (Int.NegSucc 17) (Int.OfNat 100) = Int.OfNat 82 := byComputing

theorem dialNat: Int.modNat (Int.NegSucc 17) 100 = 82 := byComputing

-- Leijen's table, one row per (a, d). T truncates (`Int.tdiv`, `Int.tmod`),
-- F floors (`Int.fdiv`, `Int.fmod`), E is Euclidean (`Int.div`, `Int.mod`).

-- 8, 3
theorem t83q: Int.tdiv (Int.OfNat 8) (Int.OfNat 3) = Int.OfNat 2 := byComputing

theorem t83r: Int.tmod (Int.OfNat 8) (Int.OfNat 3) = Int.OfNat 2 := byComputing

theorem f83q: Int.fdiv (Int.OfNat 8) (Int.OfNat 3) = Int.OfNat 2 := byComputing

theorem f83r: Int.fmod (Int.OfNat 8) (Int.OfNat 3) = Int.OfNat 2 := byComputing

theorem e83q: Int.div (Int.OfNat 8) (Int.OfNat 3) = Int.OfNat 2 := byComputing

theorem e83r: Int.mod (Int.OfNat 8) (Int.OfNat 3) = Int.OfNat 2 := byComputing

-- 8, -3
theorem t8n3q: Int.tdiv (Int.OfNat 8) (Int.NegSucc 2) = Int.NegSucc 1 := byComputing

theorem t8n3r: Int.tmod (Int.OfNat 8) (Int.NegSucc 2) = Int.OfNat 2 := byComputing

theorem f8n3q: Int.fdiv (Int.OfNat 8) (Int.NegSucc 2) = Int.NegSucc 2 := byComputing

theorem f8n3r: Int.fmod (Int.OfNat 8) (Int.NegSucc 2) = Int.NegSucc 0 := byComputing

theorem e8n3q: Int.div (Int.OfNat 8) (Int.NegSucc 2) = Int.NegSucc 1 := byComputing

theorem e8n3r: Int.mod (Int.OfNat 8) (Int.NegSucc 2) = Int.OfNat 2 := byComputing

-- -8, 3
theorem tn83q: Int.tdiv (Int.NegSucc 7) (Int.OfNat 3) = Int.NegSucc 1 := byComputing

theorem tn83r: Int.tmod (Int.NegSucc 7) (Int.OfNat 3) = Int.NegSucc 1 := byComputing

theorem fn83q: Int.fdiv (Int.NegSucc 7) (Int.OfNat 3) = Int.NegSucc 2 := byComputing

theorem fn83r: Int.fmod (Int.NegSucc 7) (Int.OfNat 3) = Int.OfNat 1 := byComputing

theorem en83q: Int.div (Int.NegSucc 7) (Int.OfNat 3) = Int.NegSucc 2 := byComputing

theorem en83r: Int.mod (Int.NegSucc 7) (Int.OfNat 3) = Int.OfNat 1 := byComputing

-- -8, -3
theorem tn8n3q: Int.tdiv (Int.NegSucc 7) (Int.NegSucc 2) = Int.OfNat 2 := byComputing

theorem tn8n3r: Int.tmod (Int.NegSucc 7) (Int.NegSucc 2) = Int.NegSucc 1 := byComputing

theorem fn8n3q: Int.fdiv (Int.NegSucc 7) (Int.NegSucc 2) = Int.OfNat 2 := byComputing

theorem fn8n3r: Int.fmod (Int.NegSucc 7) (Int.NegSucc 2) = Int.NegSucc 1 := byComputing

theorem en8n3q: Int.div (Int.NegSucc 7) (Int.NegSucc 2) = Int.OfNat 3 := byComputing

theorem en8n3r: Int.mod (Int.NegSucc 7) (Int.NegSucc 2) = Int.OfNat 1 := byComputing

-- -1, 2
theorem tn12q: Int.tdiv (Int.NegSucc 0) (Int.OfNat 2) = Int.OfNat 0 := byComputing

theorem tn12r: Int.tmod (Int.NegSucc 0) (Int.OfNat 2) = Int.NegSucc 0 := byComputing

theorem fn12q: Int.fdiv (Int.NegSucc 0) (Int.OfNat 2) = Int.NegSucc 0 := byComputing

theorem fn12r: Int.fmod (Int.NegSucc 0) (Int.OfNat 2) = Int.OfNat 1 := byComputing

theorem en12q: Int.div (Int.NegSucc 0) (Int.OfNat 2) = Int.NegSucc 0 := byComputing

theorem en12r: Int.mod (Int.NegSucc 0) (Int.OfNat 2) = Int.OfNat 1 := byComputing

-- Division needs a proof that the divisor isn't zero; with a local one,
-- the zero case is handled.
def safeDiv (a d: Int): Int := if h: d ≠ Int.OfNat 0 then Int.div a d else Int.OfNat 0

theorem safeDivZero: safeDiv (Int.OfNat 7) (Int.OfNat 0) = Int.OfNat 0 := byComputing

theorem safeDivNeg: safeDiv (Int.NegSucc 6) (Int.OfNat 2) = Int.NegSucc 3 := byComputing

-- Text.
theorem showNeg: Int.toText (Int.NegSucc 41) = "-42" := byComputing

theorem showZero: Int.toText (Int.OfNat 0) = "0" := byComputing

theorem readLeadingZeros: "-007".toInt = Some (Int.NegSucc 6) := byComputing

theorem readMinusZero: "-0".toInt = Some (Int.OfNat 0) := byComputing

theorem readPlain: "42".toInt = Some (Int.OfNat 42) := byComputing

theorem readLoneMinus: "-".toInt = None := byComputing

theorem readEmpty: "".toInt = None := byComputing

theorem readPlus: "+5".toInt = None := byComputing

theorem readTwoMinuses: "--5".toInt = None := byComputing

theorem readLeadingSpace: " 5".toInt = None := byComputing

theorem readTrailingSpace: "5 ".toInt = None := byComputing

theorem readHex: "0x10".toInt = None := byComputing

theorem readDecimalPoint: "5.0".toInt = None := byComputing

theorem readFullwidth: "５".toInt = None := byComputing

-- Sign, absolute value, conversions.
theorem signNeg: Int.sign (Int.NegSucc 9) = Int.NegSucc 0 := byComputing

theorem signZero: Int.sign (Int.OfNat 0) = Int.OfNat 0 := byComputing

theorem signPos: Int.sign (Int.OfNat 9) = Int.OfNat 1 := byComputing

theorem absNeg: Int.abs (Int.NegSucc 4) = Int.OfNat 5 := byComputing

theorem checkedNeg: Int.toNatChecked (Int.NegSucc 4) = None := byComputing

theorem checkedPos: Int.toNatChecked (Int.OfNat 4) = Some 4 := byComputing

-- Order: every negative is below every non-negative; `-5 < -2`.
theorem lessNegZero: Int.LessThan (Int.NegSucc 0) (Int.OfNat 0) := byComputing

theorem lessNegNeg: Int.LessThan (Int.NegSucc 4) (Int.NegSucc 1) := byComputing

theorem leqSame: Int.LessEq (Int.NegSucc 4) (Int.NegSucc 4) := byComputing

theorem leqPosNeg: Int.leq (Int.OfNat 0) (Int.NegSucc 0) = False := byComputing

theorem lessSame: Int.less (Int.OfNat 3) (Int.OfNat 3) = False := byComputing

theorem compareMixed: Int.compare (Int.NegSucc 4) (Int.OfNat 0) = Less := byComputing

theorem compareNegs: Int.compare (Int.NegSucc 4) (Int.NegSucc 1) = Less := byComputing

theorem compareEqual: Int.compare (Int.NegSucc 4) (Int.NegSucc 4) = Equal := byComputing

-- `==` is decided by `Int.decEq`.
theorem eqSame: (Int.NegSucc 3 == Int.NegSucc 3) = True := byComputing

theorem eqDifferent: (Int.NegSucc 3 == Int.OfNat 3) = False := byComputing
