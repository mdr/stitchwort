-- Qualified names, dot notation, imports.

import Text (split, join)
import Std.List (reverseOnto)

def sumAll (xs : List Nat) : Nat := List.sum xs

type Bag (a : Type) : Type =
  | Empty
  | Put (x : a) (rest : Bag a)

def Bag.length : Bag a -> Nat
  | Empty => 0
  | Put _ b => 1 + b.length

def Bag.double (b : Bag a) : Nat := b.length + b.length
