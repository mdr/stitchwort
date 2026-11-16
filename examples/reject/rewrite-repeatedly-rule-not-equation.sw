-- expect-error: E-REWRITE-REPEATEDLY-RULE

import Std (Nat)

-- A rule is a proof of an equation; `both` proves a conjunction. (A test
-- such as `small: x < 3` is the equation `(x < 3) = True`, and is a rule.)
theorem bad ∀ (x: Nat) (both: x = 1 ∧ x = 1): x + 0 = 1 := rewrite repeatedly [both]
