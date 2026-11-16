-- expect-error: E-REWRITE-REPEATEDLY-BUDGET

import Std (Nat)

-- Each rule undoes the other: `a` becomes `b`, then `b` becomes `a`, and so
-- on. After 500 rewrites it stops, naming the cycle.
theorem bad ∀ (a b: Nat) (there: a = b) (back: b = a): a + 1 = b + 1 := rewrite repeatedly [there, back]
