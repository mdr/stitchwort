-- `decreasing` under `Option.map` finds `Option.mapCong`, which keeps `Option.map`'s
-- parameters and binder kinds: the proof it builds applies them explicitly.
import Std (Nat, Option)

def down (n: Nat): Option Nat
    decreasing n
:= match n with
  | Zero => Some 0
  | Succ m => Option.map (Some m) (k => if h: k < n then (match down k with | Some v => v | None => 0) else 0)

theorem downStep (n: Nat): down n = down n := rfl
