-- In a module that loads `arithmetic`'s library (this one uses `arithmetic`), `auto`
-- also proves what it can't decide by `arithmetic` over the facts in scope.

import Std (Nat)

-- Division by 0 is defined (`n / 0 = 0`), so these ask for the proof
-- themselves.
def rem (n d: Nat) [auto ok: d ≠ 0]: Nat := n % d

def per (n d: Nat) [auto ok: d ≠ 0]: Nat := n / d

def remainderOfGap (n low high: Nat) (below: low < high): Nat := rem n (high - low)

def quotientPastTwice (n d: Nat) (big: 2 * d > 4): Nat := per n d

theorem gapPositive ∀ (low high: Nat) (below: low < high): 0 < high - low := arithmetic

test "remainderOfGap" := remainderOfGap 17 2 7 byComputing == 2
