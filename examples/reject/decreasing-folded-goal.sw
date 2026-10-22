-- expect-error: E-REFL
-- A definition with `decreasing` stays folded on an open argument: the goal
-- shows `evens n`, not the fuel it recurses on.
import Std (List, Nat)

def evens (n: Nat): List Nat
  decreasing n
:=
  match n with
    | Zero => Nil
    | Succ Zero => Nil
    | Succ (Succ k) => Cons k (evens k [decreasing := Nat.leSucc k])

theorem evensNil (n: Nat): evens n = Nil := rfl
