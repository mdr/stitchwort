-- Constructor, number, negative number, list, tuple, record and absurd
-- patterns.

type Empty : Type

type Person = { name : Text, age : Nat }

def ctor : List Nat -> Maybe Nat -> Nat
  | Nil, Nothing => 0
  | Cons x _, Just y => x + y
  | _, _ => 1

def num : Nat -> Text
  | 0 => "zero"
  | 7 => "seven"
  | _ => "other"

def neg : Int -> Text
  | 0 => "zero"
  | (-1) => "minus one"
  | _ => "other"

def lst : List Nat -> Nat
  | [x, y] => x + y
  | _ => 0

def tup : (Nat, Nat) -> Nat
  | (a, b) => a + b

def rec : Person -> Text
  | { name, .. } => name

def absurd : Empty -> Nat
  | ()

def nestedCtor : List (Maybe Nat) -> Nat
  | Cons (Just x) _ => x
  | _ => 0
