-- Facts about `Range.within`, taken apart, built and read through its
-- reading.
namespace Digits

import Range (within, Within)

def isDigitCode (n: Nat): Bool := within 48 n 57

theorem atMost (n: Nat) (h: isDigitCode n): n ≤ 57 :=
  match h with
    | { low, high } => high

theorem atLeast (n: Nat) (h: isDigitCode n): 48 ≤ n := h.read.low

theorem zero: isDigitCode 48 := { low = rfl, high = rfl }
