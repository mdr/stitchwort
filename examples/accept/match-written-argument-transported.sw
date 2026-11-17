-- Inside a branch of `match flag c with`, `hc` is refined, but an argument
-- written out (`reach flag (Succ k) c d`) is elaborated afresh and still has
-- the condition in it. `_` would be inferred from `hc` instead (SW-194); as
-- written, `hc` is rewritten along the `match`'s hidden equation (SW-1538,
-- match-refinement.md R2).
-- `andRight` takes its booleans explicitly, so the example can still write
-- one out: `Bool.andRight` has them implicit, with nothing to write.

import Std (Bool, Void)

def reach (flag: Nat → Bool): Nat → Nat → Nat → Bool
  | Zero, c, d => c == d
  | Succ k, c, d =>
    if flag c then
      (match c with
        | Zero => False
        | Succ b => reach flag k b d)
        ∨ reach flag k (c + 1) d
    else reach flag k c d

theorem andRight ∀ (a b: Bool) (h: (a ∧ b) = True): b = True := Bool.andRight h

theorem skip ∀ (flag: Nat → Bool) (k c d: Nat) (b: Bool)
    (hc: (b ∧ reach flag (Succ k) c d) = True):
    Bool.not (flag c) = True → reach flag k c d = True :=
  match flag c with
    | True => n => Void.impossible (Bool.falseNotTrue n)
    | False => n => andRight b (reach flag (Succ k) c d) hc
