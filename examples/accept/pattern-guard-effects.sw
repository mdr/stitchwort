-- A guard that performs no operations works in a function that may perform
-- them, and may call functions whose abilities come from their callbacks.

import Std (Fail)

def positive (n: Nat): {Fail} Nat := match n with
  | k if k > 0 => k
  | _ => Fail.fail "zero"

def allBig (xs: List Nat): {Fail} Nat := match xs with
  | [x, ..rest] if xs.all (y => y > 2) => x
  | _ => Fail.fail "not all big"
