-- expect-error: E-MUTUAL-SIGNATURE
-- A `decreasing` measure that names a theorem declared below, which is about
-- the definition itself: the measure is checked before the body, so it can't
-- use something that needs the definition finished first.
import Std (List, Nat)

def evens (n: Nat): List Nat
    decreasing evensNil
:=
  match n with
    | Zero => Nil
    | Succ Zero => Nil
    | Succ (Succ k) => Cons k (evens k [decreasing := Nat.leSucc k])

theorem evensNil (n: Nat): evens n = Nil := rfl
