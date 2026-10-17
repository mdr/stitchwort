-- Number patterns on `Int` (docs/proposals/integers.md, "Number patterns on
-- `Int`"): a literal `k` is `OfNat k` and `-k` is `NegSucc (k - 1)` around a
-- number pattern on the `Nat` field, so a match on `Int` numbers is a `case`
-- on the sign with a number case in each branch.

describe : Int -> Text
describe 0    = "zero"
describe (-1) = "minus one"
describe 404  = "not found"
describe _    = "something else"

test "describe 0 == zero" = describe 0 == "zero"
test "describe (-1) == minus one" = describe (-1) == "minus one"
test "describe 404 == not found" = describe 404 == "not found"
test "describe (-404) == something else" = describe (-404) == "something else"
test "describe 1 == something else" = describe 1 == "something else"
test "describe (-2) == something else" = describe (-2) == "something else"

-- Row priority, and a variable is the integer, not the `Nat` field.
pick : Int -> Bool -> Int
pick (-1) True  = 7
pick z    False = z
pick _    _     = 9

theorem pick1 : pick (-1) False = -1
pick1 = rfl

theorem pick2 : pick (-2) False = -2
pick2 = rfl

theorem pick3 : pick 3 False = 3
pick3 = rfl

theorem pick4 : pick (-1) True = 7
pick4 = rfl

theorem pick5 : pick 3 True = 9
pick5 = rfl

-- The sign split is real evidence: a whole branch with no numbers in it is
-- the catch-all, even for an unknown magnitude.
zeroOrOther : Int -> Bool
zeroOrOther 0 = True
zeroOrOther _ = False

theorem negativeIsOther : (k : Nat) -> zeroOrOther (NegSucc k) = False
negativeIsOther k = rfl

-- `0` and `-0` are one key; the first row with it wins.
zeros : Int -> Nat
zeros 0    = 1
zeros (-0) = 2
zeros _    = 3

theorem zerosZero : zeros 0 = 1
zerosZero = rfl

theorem zerosOne : zeros 1 = 3
zerosOne = rfl

-- Repeated literals in different rows, with another column deciding.
twice : Int -> Bool -> Nat
twice (-3) True = 1
twice 5    True = 2
twice (-3) _    = 3
twice _    _    = 4

theorem twice1 : twice (-3) True = 1
twice1 = rfl

theorem twice2 : twice (-3) False = 3
twice2 = rfl

theorem twice3 : twice 5 False = 4
twice3 = rfl

theorem twice4 : twice 5 True = 2
twice4 = rfl

-- Very large keys, either side of zero.
big : Int -> Nat
big (-1000000000000000000000000000000) = 1
big 1000000000000000000000000000000    = 2
big _                                  = 3

theorem bigNeg : big (-1000000000000000000000000000000) = 1
bigNeg = rfl

theorem bigPos : big 1000000000000000000000000000000 = 2
bigPos = rfl

theorem bigNear : big (-999999999999999999999999999999) = 3
bigNear = rfl

-- A column mixing literals, an explicit constructor and `_`.
mixed : Int -> Nat
mixed 0         = 0
mixed (-1)      = 1
mixed (OfNat n) = n + 10
mixed _         = 99

theorem mixedZero : mixed 0 = 0
mixedZero = rfl

theorem mixedNegOne : mixed (-1) = 1
mixedNegOne = rfl

theorem mixedPos : mixed 4 = 14
mixedPos = rfl

theorem mixedNeg : mixed (-7) = 99
mixedNeg = rfl

-- A catch-all before a literal makes the literal's row unreachable.
shadowed : Int -> Nat
shadowed _ = 1
shadowed 5 = 2

theorem shadowedFive : shadowed 5 = 1
shadowedFive = rfl

-- Two `Int` columns.
quadrant : Int -> Int -> Text
quadrant 0 0       = "origin"
quadrant 0 _       = "y axis"
quadrant _ 0       = "x axis"
quadrant (-1) (-1) = "diagonal"
quadrant _ _       = "elsewhere"

test "quadrant 0 0 == origin" = quadrant 0 0 == "origin"
test "quadrant 0 (-3) == y axis" = quadrant 0 (-3) == "y axis"
test "quadrant (-3) 0 == x axis" = quadrant (-3) 0 == "x axis"
test "quadrant (-1) (-1) == diagonal" = quadrant (-1) (-1) == "diagonal"
test "quadrant (-1) 1 == elsewhere" = quadrant (-1) 1 == "elsewhere"
test "quadrant 2 2 == elsewhere" = quadrant 2 2 == "elsewhere"

-- Inside other patterns, where the field's type is known to be `Int`.
inJust : Maybe Int -> Nat
inJust (Just (-1)) = 1
inJust (Just 2)    = 2
inJust _           = 3

theorem inJust1 : inJust (Just (-1)) = 1
inJust1 = rfl

theorem inJust2 : inJust (Just 2) = 2
inJust2 = rfl

theorem inJust3 : inJust (Just (-2)) = 3
inJust3 = rfl

inPair : (Int, Nat) -> Nat
inPair (-2, 0) = 1
inPair (_, n)  = n

theorem inPair1 : inPair (-2, 0) = 1
inPair1 = rfl

theorem inPair2 : inPair (-2, 5) = 5
inPair2 = rfl

-- A definition that unfolds to `Int` is matched the same way.
Price : Type
Price = Int

priceLabel : Price -> Text
priceLabel 0    = "free"
priceLabel (-1) = "refund"
priceLabel _    = "paid"

test "priceLabel 0 == free" = priceLabel 0 == "free"
test "priceLabel (-1) == refund" = priceLabel (-1) == "refund"
test "priceLabel 3 == paid" = priceLabel 3 == "paid"

-- A literal, then constructors for the rest of each sign.
sign : Int -> Int
sign 0           = 0
sign (OfNat _)   = 1
sign (NegSucc _) = -1

test "sign 0 == 0" = sign 0 == 0
test "sign 12 == 1" = sign 12 == 1
test "sign (-12) == -1" = sign (-12) == -1
