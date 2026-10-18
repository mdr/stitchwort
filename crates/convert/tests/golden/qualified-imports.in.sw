-- Qualified names, dot notation, imports.

import Text (split, join)
import Std.List (reverseOnto)

sumAll : List Nat -> Nat
sumAll xs = List.sum xs

type Bag (a : Type) : Type =
  | Empty
  | Put (x : a) (rest : Bag a)

Bag.length : Bag a -> Nat
Bag.length Empty = 0
Bag.length (Put _ b) = 1 + b.length

Bag.double : Bag a -> Nat
Bag.double b = b.length + b.length
