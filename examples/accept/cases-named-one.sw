-- `cases x then t` splits only `x`: here `cases` alone would split `warm c`'s
-- `c` and the comparison inside `score` too, while the proof needs only `c`.
import Std (Bool, Nat)

type Colour = | Red | Green | Blue

def warm: Colour → Bool
  | Red => True
  | _ => False

def bonus (c: Colour) (n: Nat): Nat := if warm c then n + 2 else n + 1

theorem bonusGrows ∀ (c: Colour) (n: Nat): n < bonus c n := cases c then arithmetic
