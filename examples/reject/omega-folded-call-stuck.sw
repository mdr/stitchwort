-- expect-error: E-OMEGA
-- A call stuck on a variable stays an atom as written: the message names
-- `drop k 1`, not the definition's internal form. False at `k = 1`.
import Std (Nat)

def drop (x: Nat) (y: Nat): Nat
    decreasing x
:=
  match x with
    | Zero => y
    | Succ m => drop m y [decreasing := omega]

theorem dropOne (k: Nat): drop k 1 = 0 := omega
