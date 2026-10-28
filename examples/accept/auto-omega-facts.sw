-- In a module that loads `omega`'s library (this one uses `omega`), `auto`
-- also proves what it can't decide by `omega` over the facts in scope.

import Std (Nat)

def remainderOfGap (n: Nat) (low: Nat) (high: Nat) (below: low < high): Nat := n % (high - low)

def quotientPastTwice (n: Nat) (d: Nat) (big: 2 * d > 4): Nat := n / d

theorem gapPositive (low: Nat) (high: Nat) (below: low < high): 0 < high - low := omega

test "remainderOfGap" := remainderOfGap 17 2 7 rfl == 2
