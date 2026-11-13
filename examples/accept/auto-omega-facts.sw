-- In a module that loads `omega`'s library (this one uses `omega`), `auto`
-- also proves what it can't decide by `omega` over the facts in scope.

import Std (Nat)

-- Division by 0 is defined (`n / 0 = 0`), so these ask for the proof
-- themselves.
def rem (n: Nat) (d: Nat) [auto ok: d ≠ 0]: Nat := n % d

def per (n: Nat) (d: Nat) [auto ok: d ≠ 0]: Nat := n / d

def remainderOfGap (n: Nat) (low: Nat) (high: Nat) (below: low < high): Nat := rem n (high - low)

def quotientPastTwice (n: Nat) (d: Nat) (big: 2 * d > 4): Nat := per n d

theorem gapPositive ∀ (low: Nat) (high: Nat) (below: low < high): 0 < high - low := omega

test "remainderOfGap" := remainderOfGap 17 2 7 rfl == 2
