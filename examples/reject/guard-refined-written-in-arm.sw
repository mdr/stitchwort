-- expect-error: E-TYPE-MISMATCH
-- A type written in a refined guard's arm still has the condition in it, so
-- `h3` doesn't have it replaced; the note says what the expected type
-- computes to, which `byComputing` proves.
import Std (Bool, Char, Nat)

def pick (b: Bool): Nat := if b then 1 else 0

theorem written ∀ (n: Nat) (c: Char) (h2: 0 < pick (c == 'a')): 0 < 1 := match n with
  | 0 if g: c == 'a' =>
    let h3: 0 < pick (c == 'a') := h2
    let k: 0 < 1 := h3
    k
  | _ => ?
