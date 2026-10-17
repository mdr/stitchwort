-- Integers, extracted to JS (docs/proposals/integers.md): an `Int` is a
-- `bigint` of either sign at the boundary and inside generated code, and
-- each `/` and `%` is justified by a proof, checked at compile time or, for
-- an export's precondition, at runtime.
--
-- run: dial (-18)
-- run: divide (-7) 2
-- run: divide 7 (-2)
-- rejects: divide (OfNat 5) (OfNat 0)
-- run: describe (-1)
-- run: describe 0
-- run: describe 1000000000000000000000000000000
-- run: negatives [0, 4]

-- Where a dial at 0 ends up after `x` clicks, on a dial of 100.
export
dial : Int -> Int
dial x = x % 100

-- Each of the three conventions, and the precondition checked in JS.
export
divide : (a : Int) -> (d : Int) -> [auto ok : d != 0] -> List Int
divide a d = [a / d, a % d, Int.tdiv a d, Int.tmod a d, Int.fdiv a d, Int.fmod a d]

export
describe : Int -> Text
describe 0    = "zero"
describe (-1) = "minus one"
describe x    = if Int.less x 0 then "negative" else "positive"

export
negatives : List Nat -> List Int
negatives ns = List.map NegSucc ns

-- Every natively implemented operation, one export each.
export
neg : Int -> Int
neg x = -x

export
add : Int -> Int -> Int
add a b = a + b

export
sub : Int -> Int -> Int
sub a b = a - b

export
mul : Int -> Int -> Int
mul a b = a * b

export
eucDiv : (a : Int) -> (d : Int) -> [auto ok : d != 0] -> Int
eucDiv a d = a / d

export
eucMod : (a : Int) -> (d : Int) -> [auto ok : d != 0] -> Int
eucMod a d = a % d

export
tdiv : (a : Int) -> (d : Int) -> [auto ok : d != 0] -> Int
tdiv a d = Int.tdiv a d

export
tmod : (a : Int) -> (d : Int) -> [auto ok : d != 0] -> Int
tmod a d = Int.tmod a d

export
fdiv : (a : Int) -> (d : Int) -> [auto ok : d != 0] -> Int
fdiv a d = Int.fdiv a d

export
fmod : (a : Int) -> (d : Int) -> [auto ok : d != 0] -> Int
fmod a d = Int.fmod a d

export
modNat : Int -> (d : Nat) -> [auto ok : d != 0] -> Nat
modNat a d = Int.modNat a d

export
decEq : Int -> Int -> Bool
decEq a b = Decidable.toBool (Int.decEq a b)

export
leq : Int -> Int -> Bool
leq a b = Int.leq a b

export
less : Int -> Int -> Bool
less a b = Int.less a b

export
compare : Int -> Int -> Ordering
compare a b = Int.compare a b

export
natAbs : Int -> Nat
natAbs x = Int.natAbs x

export
abs : Int -> Int
abs x = Int.abs x

export
toNat : Int -> Nat
toNat x = Int.toNat x

export
toNatChecked : Int -> Maybe Nat
toNatChecked x = Int.toNatChecked x

export
sign : Int -> Int
sign x = Int.sign x

export
ofNat : Nat -> Int
ofNat n = Nat.toInt n

export
toText : Int -> Text
toText x = Int.toText x

export
parse : Text -> Maybe Int
parse t = Text.toInt t

-- run: neg 5
-- run: neg (-5)
-- run: add (-3) 10
-- run: sub 3 10
-- run: mul (-4) 5
-- run: eucDiv (-7) 2
-- run: eucMod (-7) (-2)
-- run: tdiv (-7) 2
-- run: tmod (-7) 2
-- run: fdiv 7 (-2)
-- run: fmod 7 (-2)
-- run: modNat (-7) 3
-- rejects: eucDiv (OfNat 5) (OfNat 0)
-- rejects: eucMod (NegSucc 4) (OfNat 0)
-- rejects: tdiv (OfNat 5) (OfNat 0)
-- rejects: tmod (OfNat 5) (OfNat 0)
-- rejects: fdiv (OfNat 5) (OfNat 0)
-- rejects: fmod (OfNat 5) (OfNat 0)
-- rejects: modNat (OfNat 5) 0
-- run: decEq 5 5
-- run: decEq 5 (-5)
-- run: leq (-5) (-5)
-- run: less (-5) (-5)
-- run: less (-6) (-5)
-- run: compare (-1) 0
-- run: compare 0 0
-- run: compare 1 0
-- run: natAbs (-5)
-- run: abs (-5)
-- run: toNat (-5)
-- run: toNat 5
-- run: toNatChecked (-5)
-- run: toNatChecked 5
-- run: sign (-5)
-- run: sign 0
-- run: sign 5
-- run: ofNat 5
-- run: toText (-5)
-- run: toText 1000000000000000000000000000000
-- run: parse "-12"
-- run: parse "007"
-- run: parse "+5"
-- run: parse ""
-- run: parse "-"

-- User code through the representation: constructors as values, patterns on
-- native results, and an `Int` pattern of each shape.
export
ofNats : List Nat -> List Int
ofNats ns = List.map OfNat ns

export
residue : (a : Int) -> (d : Int) -> [auto ok : d != 0] -> Text
residue a d = residueName (a % d)

residueName : Int -> Text
residueName 0    = "zero"
residueName 1    = "one"
residueName (-1) = "minus one"
residueName r    = if Int.less r 0 then "negative" else "other"

export
classify : Int -> Text
classify 0 = "zero"
classify 1 = "one"
classify (-1) = "minus one"
classify 1000000000000000000000000000000 = "10^30"
classify (-1000000000000000000000000000000) = "-10^30"
classify (OfNat 2) = "two"
classify (NegSucc 1) = "minus two"
classify (OfNat k) = "positive or zero, k = " ++ Nat.toText k
classify (NegSucc k) = "negative, k = " ++ Nat.toText k

-- Both constructor patterns, with the field used.
export
fields : Int -> Nat
fields (OfNat k) = k
fields (NegSucc k) = k + 100

export
maybeInt : Maybe Int -> Int
maybeInt Nothing = 0
maybeInt (Just x) = x * 2

export
negateAll : List (Maybe Int) -> List (Maybe Int)
negateAll xs = List.map (\m -> Maybe.map Int.neg m) xs

export
firstNeg : List Int -> Maybe Int
firstNeg Nil = Nothing
firstNeg (Cons x xs) = if Int.less x 0 then Just x else firstNeg xs

type Entry = { count : Nat, delta : Int }

export
apply : Entry -> Entry
apply e = { e | delta = e.delta + OfNat e.count }

export
entries : List Entry -> Int
entries Nil = 0
entries (Cons e es) = e.delta + entries es

-- run: ofNats [1, 2]
-- run: ofNats []
-- run: negatives [0, 4]
-- run: residue 7 2
-- run: residue (-7) 2
-- run: residue 6 2
-- run: residue (-6) 4
-- run: residue 5 (-2)
-- run: classify 0
-- run: classify 1
-- run: classify (-1)
-- run: classify 2
-- run: classify (-2)
-- run: classify 1000000000000000000000000000000
-- run: classify (-1000000000000000000000000000000)
-- run: classify 77
-- run: classify (-77)
-- run: fields 5
-- run: fields (-5)
-- run: maybeInt Nothing
-- run: maybeInt (Just (-4))
-- run: negateAll [Nothing, Just 3, Just (-3)]
-- run: firstNeg [3, -4, -5]
-- run: firstNeg [3]
-- run: apply { count = 3, delta = -10 }
-- run: entries [{ count = 1, delta = -5 }, { count = 2, delta = 7 }]
