-- Constructor, number, negative number, list, tuple, record and absurd
-- patterns.

type Empty : Type

type Person = { name : Text, age : Nat }

ctor : List Nat -> Maybe Nat -> Nat
ctor Nil Nothing = 0
ctor (Cons x _) (Just y) = x + y
ctor _ _ = 1

num : Nat -> Text
num 0 = "zero"
num 7 = "seven"
num _ = "other"

neg : Int -> Text
neg 0 = "zero"
neg (-1) = "minus one"
neg _ = "other"

lst : List Nat -> Nat
lst [x, y] = x + y
lst _ = 0

tup : (Nat, Nat) -> Nat
tup (a, b) = a + b

rec : Person -> Text
rec { name, .. } = name

absurd : Empty -> Nat
absurd ()

nestedCtor : List (Maybe Nat) -> Nat
nestedCtor (Cons (Just x) _) = x
nestedCtor _ = 0
