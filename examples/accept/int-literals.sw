-- Numbers at `Int`: literals take their type from what's expected, and
-- arithmetic and comparisons are typed a group at a time
-- (docs/proposals/integers.md, "Literals" and "Numeric expressions").

-- Literals: `k` is `OfNat k`, `-k` is `NegSucc (k - 1)`, and `-0` is `OfNat 0`.
theorem lit : (5 : Int) = OfNat 5
lit = rfl

theorem negLit : (-5 : Int) = NegSucc 4
negLit = rfl

theorem negZero : (-0 : Int) = OfNat 0
negZero = rfl

-- Expected types reach literals inside constructors and lists.
theorem inJust : (Just 5 : Maybe Int) = Just (OfNat 5)
inJust = rfl

theorem inList : ([1, 2, -3] : List Int) = [OfNat 1, OfNat 2, NegSucc 2]
inList = rfl

theorem inPair : (MkPair 1 (-2) : Pair Nat Int) = MkPair 1 (NegSucc 1)
inPair = rfl

-- A definition that unfolds to `Int` takes literals too.
Price : Type
Price = Int

theorem price : (7 : Price) = OfNat 7
price = rfl

-- The minus sign makes a group `Int`, wherever it is.
theorem minusDecides : 3 - 5 = -2
minusDecides = rfl

theorem negGroup : -(3 - 5) = 2
negGroup = rfl

-- Prefix minus binds tighter than `%`: the dial.
theorem dial : -18 % 100 = 82
dial = rfl

theorem dialBracketed : -(18 % 100) = -18
dialBracketed = rfl

-- With nothing to say otherwise, a group is `Nat`, as before.
natDiff : Nat
natDiff = 3 - 5

theorem natDiffZero : natDiff = 0
natDiffZero = rfl

intDiff : Int
intDiff =
  let n : Int = 3 - 5
  n

theorem intDiffNeg : intDiff = -2
intDiffNeg = rfl

doubled : List Nat
doubled = List.map (\x -> x + 1) [1, 2]

-- A leaf without literals decides, wherever it is in the group.
addOne : Int -> Int
addOne x = x + 1

oneMinus : Int -> Int
oneMinus x = 1 - x

timesMinusTwo : Int -> Int
timesMinusTwo x = x * -2

isZero : Int -> Bool
isZero x = 0 == x

isZeroRight : Int -> Bool
isZeroRight x = x == 0

notZero : Int -> Prop
notZero x = 0 != x

zeroEq : Int -> Prop
zeroEq x = 0 = x

negative : Int -> Prop
negative x = x < 0

pick : Bool -> Int -> Int
pick c i = (if c then 1 else 2) + i

dialOf : Int -> Int
dialOf pos = pos % 100

justFive : Maybe Int -> Prop
justFive m = Just 5 = m

empty : List Int -> Prop
empty xs = xs = []

-- A `Nat` becomes an `Int` explicitly.
shifted : Nat -> Int -> Int
shifted n i = n.toInt + i

-- A generic function's literal argument defaults when it's checked, so
-- the `Int` has to come first or be written.
chooseFirst : [a : Type] -> a -> a -> a
chooseFirst x y = x

firstWritten : Int -> Int
firstWritten i = chooseFirst (5 : Int) i

firstAfter : Int -> Int
firstAfter i = chooseFirst i 5

-- Precedence.
absOfNeg : Int -> Int
absOfNeg x = (-x).abs

negOfAbs : Int -> Int
negOfAbs x = -x.abs

test "x + 1" = addOne (-1) == 0
test "1 - x" = oneMinus 3 == -2
test "x * -2" = timesMinusTwo 3 == -6
test "0 == x" = isZero 0
test "x == 0" = if isZeroRight 1 then False else True
test "if leaf" = pick True (-1) == 0
test "pos % 100" = dialOf (-18) == 82
test "n.toInt + i" = shifted 2 (-5) == -3
test "chooseFirst i 5" = firstAfter (-1) == -1
test "(-x).abs" = absOfNeg 3 == 3
test "-x.abs" = negOfAbs (-3) == -3
test "-f x" = -addOne 2 == -3
test "a - -b" = (5 : Int) - -2 == 7
test "-a * b" = -(2 : Int) * 3 == -6
test "Euclidean /" = (7 : Int) / -2 == -3
test "ordering" = if h : (-3 : Int) < 2 then True else False
test "Nat default" = 3 - 5 == 0
