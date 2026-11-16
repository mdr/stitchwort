-- expect-error: E-REWRITE-REPEATEDLY-RULE

import Std (Nat)

-- `Nat.addComm` turns `a + b` into `b + a`, which it fits again: a rule
-- whose right side holds an instance of its left is refused where it is
-- listed. Reordering a sum is `algebra`'s job.
theorem bad ∀ (x y: Nat): x + y = y + x := rewrite repeatedly [Nat.addComm]
