import Std (Nat)

def two (x: Nat): Nat
  decreasing x
:=
  match x with
    | Zero => 2
    | Succ m => two m [decreasing := omega]

theorem plainSum (x: Nat): x + 2 = Succ (Succ x) := rfl

theorem foldedSum (x: Nat): x + two 0 = Succ (Succ x) := rfl
