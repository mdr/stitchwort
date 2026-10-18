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
export def dial (x : Int) : Int := x % 100

-- Each of the three conventions, and the precondition checked in JS.
export def divide (a : Int) (d : Int) : [auto ok : d != 0] -> List Int := [a / d, a % d, Int.tdiv a d, Int.tmod a d, Int.fdiv a d, Int.fmod a d]

export def describe : Int -> Text
  | 0    => "zero"
  | (-1) => "minus one"
  | x    => if Int.less x 0 then "negative" else "positive"

export def negatives (ns : List Nat) : List Int := List.map NegSucc ns

-- Every natively implemented operation, one export each.
export def neg (x : Int) : Int := -x

export def add (a : Int) (b : Int) : Int := a + b

export def sub (a : Int) (b : Int) : Int := a - b

export def mul (a : Int) (b : Int) : Int := a * b

export def eucDiv (a : Int) (d : Int) : [auto ok : d != 0] -> Int := a / d

export def eucMod (a : Int) (d : Int) : [auto ok : d != 0] -> Int := a % d

export def tdiv (a : Int) (d : Int) : [auto ok : d != 0] -> Int := Int.tdiv a d

export def tmod (a : Int) (d : Int) : [auto ok : d != 0] -> Int := Int.tmod a d

export def fdiv (a : Int) (d : Int) : [auto ok : d != 0] -> Int := Int.fdiv a d

export def fmod (a : Int) (d : Int) : [auto ok : d != 0] -> Int := Int.fmod a d

export def modNat (a : Int) (d : Nat) : [auto ok : d != 0] -> Nat := Int.modNat a d

export def decEq (a : Int) (b : Int) : Bool := Decidable.toBool (Int.decEq a b)

export def leq (a : Int) (b : Int) : Bool := Int.leq a b

export def less (a : Int) (b : Int) : Bool := Int.less a b

export def compare (a : Int) (b : Int) : Ordering := Int.compare a b

export def natAbs (x : Int) : Nat := Int.natAbs x

export def abs (x : Int) : Int := Int.abs x

export def toNat (x : Int) : Nat := Int.toNat x

export def toNatChecked (x : Int) : Maybe Nat := Int.toNatChecked x

export def sign (x : Int) : Int := Int.sign x

export def ofNat (n : Nat) : Int := Nat.toInt n

export def toText (x : Int) : Text := Int.toText x

export def parse (t : Text) : Maybe Int := Text.toInt t

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
export def ofNats (ns : List Nat) : List Int := List.map OfNat ns

export def residue (a : Int) (d : Int) : [auto ok : d != 0] -> Text := residueName (a % d)

def residueName : Int -> Text
  | 0    => "zero"
  | 1    => "one"
  | (-1) => "minus one"
  | r    => if Int.less r 0 then "negative" else "other"

export def classify : Int -> Text
  | 0 => "zero"
  | 1 => "one"
  | (-1) => "minus one"
  | 1000000000000000000000000000000 => "10^30"
  | (-1000000000000000000000000000000) => "-10^30"
  | OfNat 2 => "two"
  | NegSucc 1 => "minus two"
  | OfNat k => "positive or zero, k = " ++ Nat.toText k
  | NegSucc k => "negative, k = " ++ Nat.toText k

-- Both constructor patterns, with the field used.
export def fields : Int -> Nat
  | OfNat k => k
  | NegSucc k => k + 100

export def maybeInt : Maybe Int -> Int
  | Nothing => 0
  | Just x => x * 2

export def negateAll (xs : List (Maybe Int)) : List (Maybe Int) := List.map (\m => Maybe.map Int.neg m) xs

export def firstNeg : List Int -> Maybe Int
  | Nil => Nothing
  | Cons x xs => if Int.less x 0 then Just x else firstNeg xs

type Entry = { count : Nat, delta : Int }

export def apply (e : Entry) : Entry := { e | delta = e.delta + OfNat e.count }

export def entries : List Entry -> Int
  | Nil => 0
  | Cons e es => e.delta + entries es

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
