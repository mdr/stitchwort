-- An `if` can be the right-hand side of `=` (or another comparison)
-- without brackets. It runs to the end of the expression, as an `if` does
-- anywhere else.

import Std (Bool, Eq, Nat)

def bonus (big: Bool) (n: Nat): Nat := if big then n + 10 else n

theorem bonusIf (big: Bool) (n: Nat): bonus big n = if big then n + 10 else n := rfl

theorem bonusAtLeast (big: Bool) (n: Nat): n ≤ if big then n + 10 else n :=
  match big with
    | True => omega
    | False => omega

def sameAsBonus (big: Bool) (n: Nat): Bool := bonus big n == if big then n + 10 else n

theorem sameAsBonusTrue: sameAsBonus True 1 = True := rfl

-- Brackets end it early.
theorem bracketed (n: Nat): (bonus False n = if False then 0 else n) = (n = n) := rfl
