-- Integers are `Int.OfNat n` (n) and `Int.NegSucc n` (-(n+1)); there is no
-- literal syntax yet. Everything here holds by computation.

-- The dial example: -18 % 100 is 82, not -18.
theorem dial : Int.mod (Int.NegSucc 17) (Int.OfNat 100) = Int.OfNat 82
dial = rfl

theorem dialNat : Int.modNat (Int.NegSucc 17) 100 = 82
dialNat = rfl

-- Leijen's table, one row per (a, d). T truncates (`Int.tdiv`, `Int.tmod`),
-- F floors (`Int.fdiv`, `Int.fmod`), E is Euclidean (`Int.div`, `Int.mod`).

-- 8, 3
theorem t83q : Int.tdiv (Int.OfNat 8) (Int.OfNat 3) = Int.OfNat 2
t83q = rfl

theorem t83r : Int.tmod (Int.OfNat 8) (Int.OfNat 3) = Int.OfNat 2
t83r = rfl

theorem f83q : Int.fdiv (Int.OfNat 8) (Int.OfNat 3) = Int.OfNat 2
f83q = rfl

theorem f83r : Int.fmod (Int.OfNat 8) (Int.OfNat 3) = Int.OfNat 2
f83r = rfl

theorem e83q : Int.div (Int.OfNat 8) (Int.OfNat 3) = Int.OfNat 2
e83q = rfl

theorem e83r : Int.mod (Int.OfNat 8) (Int.OfNat 3) = Int.OfNat 2
e83r = rfl

-- 8, -3
theorem t8n3q : Int.tdiv (Int.OfNat 8) (Int.NegSucc 2) = Int.NegSucc 1
t8n3q = rfl

theorem t8n3r : Int.tmod (Int.OfNat 8) (Int.NegSucc 2) = Int.OfNat 2
t8n3r = rfl

theorem f8n3q : Int.fdiv (Int.OfNat 8) (Int.NegSucc 2) = Int.NegSucc 2
f8n3q = rfl

theorem f8n3r : Int.fmod (Int.OfNat 8) (Int.NegSucc 2) = Int.NegSucc 0
f8n3r = rfl

theorem e8n3q : Int.div (Int.OfNat 8) (Int.NegSucc 2) = Int.NegSucc 1
e8n3q = rfl

theorem e8n3r : Int.mod (Int.OfNat 8) (Int.NegSucc 2) = Int.OfNat 2
e8n3r = rfl

-- -8, 3
theorem tn83q : Int.tdiv (Int.NegSucc 7) (Int.OfNat 3) = Int.NegSucc 1
tn83q = rfl

theorem tn83r : Int.tmod (Int.NegSucc 7) (Int.OfNat 3) = Int.NegSucc 1
tn83r = rfl

theorem fn83q : Int.fdiv (Int.NegSucc 7) (Int.OfNat 3) = Int.NegSucc 2
fn83q = rfl

theorem fn83r : Int.fmod (Int.NegSucc 7) (Int.OfNat 3) = Int.OfNat 1
fn83r = rfl

theorem en83q : Int.div (Int.NegSucc 7) (Int.OfNat 3) = Int.NegSucc 2
en83q = rfl

theorem en83r : Int.mod (Int.NegSucc 7) (Int.OfNat 3) = Int.OfNat 1
en83r = rfl

-- -8, -3
theorem tn8n3q : Int.tdiv (Int.NegSucc 7) (Int.NegSucc 2) = Int.OfNat 2
tn8n3q = rfl

theorem tn8n3r : Int.tmod (Int.NegSucc 7) (Int.NegSucc 2) = Int.NegSucc 1
tn8n3r = rfl

theorem fn8n3q : Int.fdiv (Int.NegSucc 7) (Int.NegSucc 2) = Int.OfNat 2
fn8n3q = rfl

theorem fn8n3r : Int.fmod (Int.NegSucc 7) (Int.NegSucc 2) = Int.NegSucc 1
fn8n3r = rfl

theorem en8n3q : Int.div (Int.NegSucc 7) (Int.NegSucc 2) = Int.OfNat 3
en8n3q = rfl

theorem en8n3r : Int.mod (Int.NegSucc 7) (Int.NegSucc 2) = Int.OfNat 1
en8n3r = rfl

-- -1, 2
theorem tn12q : Int.tdiv (Int.NegSucc 0) (Int.OfNat 2) = Int.OfNat 0
tn12q = rfl

theorem tn12r : Int.tmod (Int.NegSucc 0) (Int.OfNat 2) = Int.NegSucc 0
tn12r = rfl

theorem fn12q : Int.fdiv (Int.NegSucc 0) (Int.OfNat 2) = Int.NegSucc 0
fn12q = rfl

theorem fn12r : Int.fmod (Int.NegSucc 0) (Int.OfNat 2) = Int.OfNat 1
fn12r = rfl

theorem en12q : Int.div (Int.NegSucc 0) (Int.OfNat 2) = Int.NegSucc 0
en12q = rfl

theorem en12r : Int.mod (Int.NegSucc 0) (Int.OfNat 2) = Int.OfNat 1
en12r = rfl

-- Division needs a proof that the divisor isn't zero; with a local one,
-- the zero case is handled.
safeDiv : Int -> Int -> Int
safeDiv a d = if h : d != Int.OfNat 0 then Int.div a d else Int.OfNat 0

theorem safeDivZero : safeDiv (Int.OfNat 7) (Int.OfNat 0) = Int.OfNat 0
safeDivZero = rfl

theorem safeDivNeg : safeDiv (Int.NegSucc 6) (Int.OfNat 2) = Int.NegSucc 3
safeDivNeg = rfl

-- Text.
theorem showNeg : Int.toText (Int.NegSucc 41) = "-42"
showNeg = rfl

theorem showZero : Int.toText (Int.OfNat 0) = "0"
showZero = rfl

theorem readLeadingZeros : Text.toInt "-007" = Just (Int.NegSucc 6)
readLeadingZeros = rfl

theorem readMinusZero : Text.toInt "-0" = Just (Int.OfNat 0)
readMinusZero = rfl

theorem readPlain : Text.toInt "42" = Just (Int.OfNat 42)
readPlain = rfl

theorem readLoneMinus : Text.toInt "-" = Nothing
readLoneMinus = rfl

theorem readEmpty : Text.toInt "" = Nothing
readEmpty = rfl

theorem readPlus : Text.toInt "+5" = Nothing
readPlus = rfl

theorem readTwoMinuses : Text.toInt "--5" = Nothing
readTwoMinuses = rfl

theorem readLeadingSpace : Text.toInt " 5" = Nothing
readLeadingSpace = rfl

theorem readTrailingSpace : Text.toInt "5 " = Nothing
readTrailingSpace = rfl

theorem readHex : Text.toInt "0x10" = Nothing
readHex = rfl

theorem readDecimalPoint : Text.toInt "5.0" = Nothing
readDecimalPoint = rfl

theorem readFullwidth : Text.toInt "５" = Nothing
readFullwidth = rfl

-- Sign, absolute value, conversions.
theorem signNeg : Int.sign (Int.NegSucc 9) = Int.NegSucc 0
signNeg = rfl

theorem signZero : Int.sign (Int.OfNat 0) = Int.OfNat 0
signZero = rfl

theorem signPos : Int.sign (Int.OfNat 9) = Int.OfNat 1
signPos = rfl

theorem absNeg : Int.abs (Int.NegSucc 4) = Int.OfNat 5
absNeg = rfl

theorem checkedNeg : Int.toNatChecked (Int.NegSucc 4) = Nothing
checkedNeg = rfl

theorem checkedPos : Int.toNatChecked (Int.OfNat 4) = Just 4
checkedPos = rfl

-- Order: every negative is below every non-negative; `-5 < -2`.
theorem lessNegZero : Int.LessThan (Int.NegSucc 0) (Int.OfNat 0)
lessNegZero = rfl

theorem lessNegNeg : Int.LessThan (Int.NegSucc 4) (Int.NegSucc 1)
lessNegNeg = rfl

theorem leqSame : Int.LessEq (Int.NegSucc 4) (Int.NegSucc 4)
leqSame = rfl

theorem leqPosNeg : Int.leq (Int.OfNat 0) (Int.NegSucc 0) = False
leqPosNeg = rfl

theorem lessSame : Int.less (Int.OfNat 3) (Int.OfNat 3) = False
lessSame = rfl

theorem compareMixed : Int.compare (Int.NegSucc 4) (Int.OfNat 0) = Less
compareMixed = rfl

theorem compareNegs : Int.compare (Int.NegSucc 4) (Int.NegSucc 1) = Less
compareNegs = rfl

theorem compareEqual : Int.compare (Int.NegSucc 4) (Int.NegSucc 4) = Equal
compareEqual = rfl

-- `==` is decided by `Int.decEq`.
theorem eqSame : (Int.NegSucc 3 == Int.NegSucc 3) = True
eqSame = rfl

theorem eqDifferent : (Int.NegSucc 3 == Int.OfNat 3) = False
eqDifferent = rfl
