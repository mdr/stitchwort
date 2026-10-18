-- Lambdas, match, let, records, named arguments and if.

def lams (a : Nat) : Nat -> Nat -> Nat := \x y => a + x + y

def pairLam : Pair Nat Nat -> Nat := \(MkPair a b) => a + b

def tupLam : (Nat, Nat) -> Nat := \(a, b) => a + b

def nested (a : Nat) : Nat -> Nat -> Nat := \x => \y => a + x + y

def m1 (xs : List Nat) : Nat := match xs with
  | Nil => 0
  | Cons x _ => x

def m2 (xs : List Nat) (ys : List Nat) : Nat := match xs, ys with
  | Nil, _ => 0
  | Cons x _, Nil => x
  | Cons x _, Cons y _ => x + y

def m3 (xs : List Nat) (mb : Maybe Nat) : Nat := match xs with
  | Nil =>
    match mb with
      | Nothing => 0
      | Just v => v
  | Cons x _ => x

def m4 (xs : List Nat) : Nat := match h : List.length xs with
  | Zero => 0
  | Succ n => n

def lets (n : Nat) : Nat :=
  let x := n + 1
  let y : Nat := x + 1
  let (a, b) := (x, y)
  let MkPair c d := MkPair a b
  c + d

type Person = { name : Text, age : Nat }

def alice : Person := { name = "Alice", age = 30 }

def older (p : Person) : Person := { p | age = 31 }

def named : Nat := List.length [a := Nat] [1, 2]

def safeDiv (n : Nat) (d : Nat) : Nat :=
  if h : d != 0 then n / d
  else 0
