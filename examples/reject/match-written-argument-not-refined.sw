-- expect-error: E-TYPE-MISMATCH
-- Inside a branch of `match e: flag c with`, `h` is refined, but an argument
-- written out (`reach flag (Succ k) c d`) is elaborated afresh and still has
-- the condition in it. `_` would be inferred from `h` instead (SW-194).

import Std (Bool)

def reach (flag: Nat -> Bool): Nat -> Nat -> Nat -> Bool
  | Zero,   c, d => c == d
  | Succ k, c, d =>
    if flag c then
      (match c with
         | Zero   => False
         | Succ b => reach flag k b d)
        || reach flag k (c + 1) d
    else reach flag k c d

theorem skip (flag: Nat -> Bool) (k: Nat) (c: Nat) (d: Nat) (b: Bool) (hc: (b && reach flag (Succ k) c d) = True):
    Bool.not (flag c) = True -> reach flag k c d = True :=
  match e: flag c with
    | True  => n => Void.exfalso (Bool.falseNotTrue n)
    | False => n => Bool.andRight b (reach flag (Succ k) c d) hc
