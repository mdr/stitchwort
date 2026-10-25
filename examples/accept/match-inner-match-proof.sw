-- Proving things about a definition with a `match` inside an arm (SW-194).
-- `reach` has an inner `match` as an operand of `||`, so it is a generated
-- function that source can't name. Matching on the condition still refines
-- a hypothesis about `reach` (a parameter, a lambda's variable or a `let`),
-- and `_` for the operand that is the inner `match` lets unification fill it
-- in, so the proof never writes it.

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

theorem orCases (goal: Prop): (a: Bool) → (b: Bool) → (a ∨ b) = True → (a = True → goal) → (b = True → goal) → goal
  | True, b, h, f, g => f rfl
  | False, b, h, f, g => g h

-- Where the condition fails, `reach` skips the row.
theorem skip (flag: Nat → Bool) (k: Nat) (c: Nat) (d: Nat) (h: reach flag (Succ k) c d = True):
    ¬(flag c) = True → reach flag k c d = True :=
  match e: flag c with
    | True => n => Void.exfalso (Bool.falseNotTrue n)
    | False => n => h

-- The three ways a beam can have got to `d`. The left operand of `||` is the
-- inner `match`, written `_`; splitting `c` makes it compute.
theorem ways (flag: Nat → Bool) (k: Nat) (c: Nat) (d: Nat) (goal: Prop) (h: reach flag (Succ k) c d = True)
    (left: (b: Nat) → reach flag k b d = True → goal) (right: reach flag k (c + 1) d = True → goal)
    (straight: reach flag k c d = True → goal): goal :=
  let hr: reach flag (Succ k) c d = True := h
  match e: flag c with
    | True =>
      orCases goal _ (reach flag k (c + 1) d) hr
        (hl =>
          match c with
            | Zero => Void.exfalso (Bool.falseNotTrue hl)
            | Succ b => left b hl)
        right
    | False => straight hr
