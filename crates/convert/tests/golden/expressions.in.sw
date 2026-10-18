-- Lambdas, match, let, records, named arguments and if.

lams : Nat -> Nat -> Nat -> Nat
lams a = \x y -> a + x + y

pairLam : Pair Nat Nat -> Nat
pairLam = \(MkPair a b) -> a + b

tupLam : (Nat, Nat) -> Nat
tupLam = \(a, b) -> a + b

nested : Nat -> Nat -> Nat -> Nat
nested a = \x -> \y -> a + x + y

m1 : List Nat -> Nat
m1 xs = match xs with
  | Nil -> 0
  | Cons x _ -> x

m2 : List Nat -> List Nat -> Nat
m2 xs ys = match xs, ys with
  | Nil, _ -> 0
  | Cons x _, Nil -> x
  | Cons x _, Cons y _ -> x + y

m3 : List Nat -> Maybe Nat -> Nat
m3 xs mb = match xs with
  | Nil ->
    match mb with
      | Nothing -> 0
      | Just v -> v
  | Cons x _ -> x

m4 : List Nat -> Nat
m4 xs = match h : List.length xs with
  | Zero -> 0
  | Succ n -> n

lets : Nat -> Nat
lets n =
  let x = n + 1
  let y : Nat = x + 1
  let (a, b) = (x, y)
  let MkPair c d = MkPair a b
  c + d

type Person = { name : Text, age : Nat }

alice : Person
alice = { name = "Alice", age = 30 }

older : Person -> Person
older p = { p | age = 31 }

named : Nat
named = List.length [a := Nat] [1, 2]

safeDiv : Nat -> Nat -> Nat
safeDiv n d =
  if h : d != 0 then n / d
  else 0
