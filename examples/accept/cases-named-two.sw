-- `cases x, y then t` splits `x`, then `y` in each of `x`'s cases, in the
-- order written, and closes each case with `t`.
import Std (Bool, Nat)

type Colour = | Red | Green | Blue

def warm: Colour → Bool
  | Red => True
  | _ => False

def score (c: Colour) (lit: Bool) (n: Nat): Nat := if warm c && lit then n + 2 else n + 1

theorem scoreGrows ∀ (c: Colour) (lit: Bool) (n: Nat): n < score c lit n := cases c, lit then arithmetic
