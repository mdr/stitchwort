-- expect-error: E-DECREASING
-- `totalCong` exists, but takes its premise before the list, where a
-- congruence lemma for `total` takes `total`'s parameters first: the message
-- names the lemma and what's wrong with it.
import Std (List, Nat)

def total (f: Nat -> Nat): List Nat -> Nat
  | Nil       => 0
  | Cons x xs => f x + total f xs

theorem totalCong (f1: Nat -> Nat) (f2: Nat -> Nat) (ef: (x: Nat) -> f1 x = f2 x): (xs: List Nat) -> total f1 xs = total f2 xs
  | Nil       => rfl
  | Cons x xs => rewrite ef x, totalCong f1 f2 ef xs

def weight (n: Nat): Nat
  decreasing n
:=
  1 + total (d => if h: d < n then weight d else 0) (List.range n)
