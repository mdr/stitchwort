-- What a number pattern is stuck on, `cases` splits by the pattern's
-- numbers and the rest, as a `match` on those numbers would (SW-3752). In
-- the rest's case the number is known to be none of them, so the
-- definition takes its last arm.
import Std (Nat)

def width: Nat → Nat
  | 0 => 1
  | 1 => 1
  | 10 => 2
  | n => n

theorem widthPast ∀ (n: Nat) (big: 10 < n): width n = n := cases

def isDigitCode (code: Nat): Bool := match code with
  | 32 => False
  | 45 => False
  | _ => 48 <= code && code <= 57

theorem digitCodeAtMost ∀ (code: Nat) (digit: isDigitCode code = True): code <= 57 := cases

-- A character pattern is a number pattern on the character's code: the
-- character is taken apart, then its code split.
def digitOrSpace (c: Char): Bool := match c with
  | ' ' => False
  | _ => 48 <= c.toNat && c.toNat <= 57

theorem atMostNine ∀ (c: Char) (h: digitOrSpace c = True): c.toNat <= 57 := cases
