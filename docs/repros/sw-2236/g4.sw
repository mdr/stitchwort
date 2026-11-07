import Std (Nat, Float)

def two (x: Nat): Nat
  decreasing x
:=
  match x with
    | Zero => 2
    | Succ m => two m [decreasing := omega]

theorem plainFloat: Float.ofNat 2 = Float.ofNat (1 + 1) := rfl

theorem foldedFloat: Float.ofNat (two 0) = Float.ofNat 2 := rfl
